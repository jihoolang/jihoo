"""Parameterized and indexed data types and erased u64 indices, called by tests/core.py."""
import ctypes
import json
import os
import platform
import random
import re
import shlex
import struct

MAX = (1 << 64) - 1

# A true index: View(n) says whether n is 0 or k + 1. The motive of a case
# analysis depends on the index, which each case learns.
VIEW = """
(data View 1 0
  (Zero (View 0))
  (Succ (pi k U64 (View (uadd k 1)))))

(def below_succ
  (pi n U64 (pi v (View n) (Refine (lam j U64 (Lt j (uadd n 1))))))
  (lam n U64 (lam v (View n)
    (induct View (lam m U64 (lam t (View m) (Refine (lam j U64 (Lt j (uadd m 1))))))
      (pack (lam j U64 (Lt j 1)) 0 (decide-lt 0 1))
      (lam k U64 (pack (lam j U64 (Lt j (uadd k 2))) k (lt-add 0 2 k (decide-lt 0 2))))
      v))))
"""


def validate_indexed(compiler, root, temporary, environment, run, definitions, evaluate):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    example = root / "examples/core_indexed.jh"
    core_example = root / "examples/core_indexed.jhc"
    source_text = example.read_text()
    core_text = core_example.read_text()
    prefix = source_text.split("fn main()")[0]
    core_prefix = core_text.split("(export lookup")[0]
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable",
                   "JIHOO_LD": "/unavailable"}
    command("check", example, env=unavailable)
    command("check", core_example, source=False, env=unavailable)
    mir = command("emit-mir", example, "--lib").stdout
    assert mir == command("emit-mir", core_example, source=False).stdout
    # Each export takes only its runtime arguments: no erased length or
    # parameter, no tag or evidence, and no bounds assertion.
    assert mir.count("fn ") == 4 and mir.count("switch ") == 3, mir
    assert len(re.findall(r"= _\d+\[_\d+\]", mir)) == 4, mir
    for name in ("lookup", "spread", "first"):
        assert f"fn {name} [{name}] {{\n  let mut _0: i64\n  let mut _1: u64\n  let mut _2: " in mir, (name, mir)
    assert "fn front [front] {\n  let mut _0: i64\n  let mut _1: i64\n  let mut _2: [i64; 3]" in mir, mir
    for absent in ("assert", "call", "Lt", "Slot", "closure"):
        assert absent not in mir, (absent, mir)
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 33 and not result.stdout and not result.stderr

    # An erased argument is never evaluated, so it cannot trap.
    quiet = temporary / "indexed-quiet.jh"
    quiet.write_text(prefix + f"fn ignore(n: erased(u64)) -> i64 {{ 7 }}\nfn main() -> i64 {{ ignore({MAX} + 1) }}\n")
    for level in ("-O0", "-O2"):
        assert command("run", quiet, level, success=False).returncode == 7, level
    trap = temporary / "indexed-trap.jh"
    # A parameterized value is evaluated for its traps, even when unused.
    trap.write_text(prefix + f"fn ignore(s: Slot(4)) -> i64 {{ 7 }}\nfn main() -> i64 {{ ignore(slot(4, {MAX} + 1)) }}\n")
    for level in ("-O0", "-O2"):
        assert command("run", trap, level, success=False).returncode == 132, level

    valid = prefix + """
fn weaken(n: erased(u64), i: u64, p: erased(Lt(i, n))) -> Lt(i, n + 1) { lt_le(i, n, n + 1, p, lt_add(0, 2, n, decide_lt(0, 2))) }
fn same(n: erased(u64), s: Slot(n)) -> Slot(n) { s }
fn empty_position(n: erased(u64)) -> Eq(position(n, Slot.Empty), 0) { refl(0) }
fn full_position(i: u64, p: erased(Lt(i, 9))) -> Eq(position(9, Slot.Full(pack(i, p))), i) { refl(i) }
fn tail(n: erased(u64), xs: [i64; n + 2]) -> i64 { index(xs, 1, lt_add(0, n + 1, 1, zero_le(n))) }
export fn twice(i: u64) -> i64 { read(4, [1, 2, 3, 4], widen(4, 4, decide_lt(4, 5), widen(4, 4, decide_lt(4, 5), slot(4, i))), 0) }
"""
    valid_path = temporary / "indexed-valid.jh"
    valid_path.write_text(valid)
    command("check", valid_path, "--lib")
    view = temporary / "indexed-view.jhc"
    view.write_text(VIEW + "(export pred (pi n U64 U64) (lam n U64 (witness (app below_succ (uadd n 1) (Succ n)))))\n(export zero U64 (witness (app below_succ 0 Zero)))\n")
    command("check", view, source=False)
    view_mir = command("emit-mir", view, source=False).stdout
    assert "fn pred [pred]" in view_mir and "switch" not in view_mir and "call" not in view_mir, view_mir

    source_invalid = {
        "erased-runtime": "fn bad(n: erased(u64)) -> u64 { n }",
        "erased-argument": "fn id(x: u64) -> u64 { x }\nfn bad(n: erased(u64)) -> u64 { id(n) }",
        "erased-branch": "fn bad(n: erased(u64), i: u64) -> i64 { if_lt(i, n, fn(p) { 1 }, 0) }",
        "erased-fold": "fn bad(n: erased(u64)) -> i64 { fold(n, 0, fn(i, p, acc) { acc }) }",
        "erased-witness": "fn bad(n: erased(u64)) -> refine(fn(j) { Eq(j, n) }) { pack(n, refl(n)) }",
        "erased-field": "fn bad(n: erased(u64)) -> Slot(n + 1) { Slot.Full(pack(n, lt_add(0, 1, n, decide_lt(0, 1)))) }",
        "erased-i64": "fn bad(x: erased(i64)) -> i64 { 0 }",
        "erased-sum": "fn bad(n: erased(u64), i: u64) -> u64 { i + n }",
        "wrong-parameter": "fn bad(s: Slot(3)) -> Slot(4) { s }",
        "wrong-length": "fn bad(n: erased(u64), xs: [i64; n], s: Slot(n + 1)) -> i64 { read(n, xs, s, 0) }",
        "no-expected": "fn bad() -> u64 { witness(Slot.Empty) }",
        "other-expected": "enum Other(n: u64) {\n    None\n}\nfn bad() -> Other(3) { Slot.Empty }",
        "unparameterized": "fn bad(s: Slot) -> i64 { 0 }",
        "parameter-type": "enum Signed(x: i64) {\n    A\n}",
        "false-by-cases": "fn bad(n: u64, nz: erased(Lt(0, n)), s: Slot(n)) -> Lt(position(n, s), 1) { induct(fn(t) { Lt(position(n, t), 1) }, decide_lt(0, 1), fn(j) { proof(j) }, s) }",
        "unwidened": "fn bad(n: erased(u64), m: erased(u64), s: Slot(n)) -> Slot(m) { match s { Empty => Slot.Empty, Full(j) => Slot.Full(j) } }",
        "export-erased": "export fn bad(n: erased(u64)) -> i64 { 0 }",
        "short-array": "export fn bad() -> i64 { head(0, []) }",
        "parameter-binder": "fn bad(s: Slot(3)) -> i64 { match s { Empty => 0, Full(n, j) => 1 } }",
    }
    for name, body in source_invalid.items():
        path = temporary / f"indexed-{name}.jh"
        path.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert str(path) in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"indexed-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False)
        assert not obj.exists()

    core_invalid = {
        "parameter-later": "(data P 1 1 (C (pi x U64 (pi0 n U64 (P n)))))",
        "parameter-relevant": "(data P 1 1 (C (pi n U64 (P n))))",
        "parameter-changed": "(data P 1 1 (C (pi0 n U64 (P (uadd n 1)))))",
        "parameters-over-arity": "(data P 1 2 (C (pi0 n U64 (P n))))",
        "erased-i64": "(def bad (pi0 x I64 I64) (lam0 x I64 (int 0)))",
        "erased-runtime": "(def bad (pi0 n U64 U64) (lam0 n U64 n))",
        "index-motive": VIEW + "(def bad (pi n U64 (pi v (View n) U64)) (lam n U64 (lam v (View n) (induct View (lam t (View n) U64) 0 (lam k U64 k) v))))",
        "wrong-index-case": VIEW.replace("(pack (lam j U64 (Lt j 1)) 0 (decide-lt 0 1))", "(pack (lam j U64 (Lt j 0)) 0 (decide-lt 0 1))"),
        "index-confusion": VIEW.replace("(lt-add 0 2 k (decide-lt 0 2))", "(lt-add 0 1 k (decide-lt 0 1))"),
        "parameter-motive": "(def bad (pi s (Slot 3) I64) (lam s (Slot 3) (induct Slot (lam t (Slot 4) I64) (int 0) (lam j (Refine (lam j U64 (Lt j 4))) (int 1)) s)))",
        "missing-parameter": "(def bad (Slot 3) Empty)",
    }
    for name, body in core_invalid.items():
        path = temporary / f"indexed-{name}.jhc"
        path.write_text(core_prefix + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert "core:" in diagnostic.stderr, (name, diagnostic.stderr)

    reference = {}
    for _, name, _, body in definitions(core_text):
        reference[name] = evaluate(body, reference.copy())
    rng = random.Random(0x5E)
    indices = [0, 1, 2, 3, 4, 5, 1 << 63, MAX, *(rng.getrandbits(64) for _ in range(10))]
    xs = [0, 1, -1, 7, -(1 << 63), (1 << 63) - 1, *(rng.randrange(-(1 << 62), 1 << 62) for _ in range(6))]
    formatted = temporary / "indexed-formatted.jh"
    formatted.write_text(command("fmt", example).stdout)
    assert mir == command("emit-mir", formatted, "--lib").stdout
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            for is_source, suffix in ((True, "jh"), (False, "jhc")):
                obj = temporary / f"indexed-{target}{level}-{suffix}.o"
                options = ["--lib"] if is_source else []
                command("emit-obj", example if is_source else core_example, *options,
                        "--target", target, level, "-o", str(obj), source=is_source)
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                library = temporary / f"indexed{level}-{suffix}.so"
                cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
                run([*cc, "-shared", str(obj), "-o", str(library)])
                native = ctypes.CDLL(str(library))
                for name in ("lookup", "spread", "first"):
                    getattr(native, name).argtypes = [ctypes.c_uint64]
                    getattr(native, name).restype = ctypes.c_int64
                native.front.argtypes = [ctypes.c_int64]
                native.front.restype = ctypes.c_int64
                for i in indices:
                    assert native.lookup(i) == reference["lookup"](i) == ([10, 20, 30][i] if i < 3 else -1), i
                    assert native.spread(i) == reference["spread"](i) == ([1, 2, 3][i] if i < 3 else 0), i
                    assert native.first(i) == reference["first"](i) == [5, 6, 7, 8][i if i < 4 else 0], i
                for x in xs:
                    assert native.front(x) == reference["front"](x) == x, x
    print(f"dependent indexed data: paired source/core execution, erased indices, {len(source_invalid)} source and {len(core_invalid)} core rejections passed")
