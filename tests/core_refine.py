"""Refinements {x : U64 | P x}, called by tests/core.py."""
import ctypes
import json
import os
import platform
import random
import re
import shlex
import struct

MAX = (1 << 64) - 1


def validate_refine(compiler, root, temporary, environment, run, definitions, evaluate):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    example = root / "examples/core_refine.jh"
    core_example = root / "examples/core_refine.jhc"
    source_text = example.read_text()
    core_text = core_example.read_text()
    prefix = source_text.split("fn main()")[0]
    core_prefix = core_text.split("(export wrap")[0]
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable",
                   "JIHOO_LD": "/unavailable"}
    command("check", example, env=unavailable)
    command("check", core_example, source=False, env=unavailable)
    mir = command("emit-mir", example, "--lib").stdout
    assert mir == command("emit-mir", core_example, source=False).stdout
    # wrap: one comparison and one load; clamp: one comparison and no load;
    # last: two comparisons, k - 1 once and one load. A refinement is its
    # u64: no evidence, pairs or bounds assertions.
    assert mir.count("fn ") == 3 and mir.count("switch ") == 4, mir
    assert len(re.findall(r"= _\d+\[_\d+\]", mir)) == 2 and mir.count(" - ") == 1, mir
    assert "fn clamp [clamp] {\n  let mut _0: u64\n  let mut _1: u64\n" in mir, mir
    for absent in ("assert", "call", "Lt", "Eq", "pack", "closure", "(", "{ "):
        assert absent not in mir.replace("fn ", ""), (absent, mir)
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 53 and not result.stdout and not result.stderr

    # A refinement's witness is evaluated for its traps, even when unused.
    traps = {
        "witness": "fn main() -> i64 { at(3, [1, 2, 3], below(18446744073709551615 + 1, 3, decide_lt(0, 3))) }",
        "unused-branch": "fn ignore(s: refine(fn(j) { Lt(j, 3) })) -> i64 { 7 }\nfn main() -> i64 { ignore(below(18446744073709551615 + 1, 3, decide_lt(0, 3))) }",
        "unused-pack": "fn same(i: u64) -> refine(fn(j) { Eq(j, j) }) { pack(i, refl(i)) }\nfn ignore(s: refine(fn(j) { Eq(j, j) })) -> i64 { 7 }\nfn main() -> i64 { ignore(same(18446744073709551615 + 1)) }",
    }
    for name, body in traps.items():
        path = temporary / f"refine-trap-{name}.jh"
        path.write_text(prefix + body + "\n")
        for level in ("-O0", "-O2"):
            assert command("run", path, level, success=False).returncode == 132, (name, level)
    # Erased evidence alone is never evaluated.
    quiet = temporary / "refine-quiet.jh"
    quiet.write_text(prefix + "fn big(i: u64) -> refine(fn(j) { Eq(j + 18446744073709551615, j + 18446744073709551615) }) { pack(i, refl(i + 18446744073709551615)) }\nfn ignore(s: refine(fn(j) { Eq(j + 18446744073709551615, j + 18446744073709551615) })) -> i64 { 7 }\nfn main() -> i64 { ignore(big(1)) }\n")
    for level in ("-O0", "-O2"):
        assert command("run", quiet, level, success=False).returncode == 7, level

    valid = prefix + """
fn computed() -> Eq(witness(below(7, 3, decide_lt(0, 3))), 0) { refl(0) }
fn kept() -> Eq(witness(below(2, 3, decide_lt(0, 3))), 2) { refl(2) }
fn successor(k: u64, p: erased(Lt(0, k))) -> Eq(witness(pred(k, p)) + 1, k) { proof(pred(k, p)) }
fn irrelevant(k: u64, p: erased(Lt(0, k)), q: erased(Lt(0, k))) -> Eq(witness(pred(k, p)), witness(pred(k, q))) { refl(witness(pred(k, p))) }
fn same(n: u64, s: refine(fn(j) { Lt(j, n) })) -> refine(fn(j) { Lt(j, n) }) { s }
fn weaken(n: u64, s: refine(fn(j) { Lt(j, n) })) -> refine(fn(j) { Lt(j, n + 1) }) {
    pack(witness(s), lt_le(witness(s), n, n + 1, proof(s), lt_add(0, 2, n, decide_lt(0, 2))))
}
fn repacked(n: u64, xs: [i64; n + 1], s: refine(fn(j) { Lt(j, n) })) -> i64 { at(n + 1, xs, weaken(n, s)) }
fn both(i: u64) -> refine(fn(j) { Lt(j, 3) }) { if_lt(i, 2, fn(p) { pack(i + 1, lt_add(i, 2, 1, p)) }, pack(0, decide_lt(0, 3))) }
"""
    valid_path = temporary / "refine-valid.jh"
    valid_path.write_text(valid)
    command("check", valid_path, "--lib")

    source_invalid = {
        "false-pack": "fn bad(i: u64) -> refine(fn(j) { Lt(j, 3) }) { pack(i, decide_lt(0, 3)) }",
        "other-witness": "fn bad() -> refine(fn(j) { Lt(j, 3) }) { pack(5, decide_lt(0, 3)) }",
        "no-subtyping": "fn bad(n: u64, s: refine(fn(j) { Lt(j, n) })) -> refine(fn(j) { Lt(j, n + 1) }) { s }",
        "wrong-bound": "fn bad(n: u64, xs: [i64; n], s: refine(fn(j) { Lt(j, n + 1) })) -> i64 { index(xs, witness(s), proof(s)) }",
        "wrong-index": "fn bad(n: u64, xs: [i64; n], i: u64, s: refine(fn(j) { Lt(j, n) })) -> i64 { index(xs, i, proof(s)) }",
        "wrong-equation": "fn bad(k: u64, p: erased(Lt(0, k))) -> refine(fn(j) { Eq(j, k) }) { pack(sub(k, 1, lt_add(0, k, 1, p)), refl(k)) }",
        "runtime-proof": "fn id(x: u64) -> u64 { x }\nfn bad(s: refine(fn(j) { Lt(j, 3) })) -> u64 { id(proof(s)) }",
        "witness-of-u64": "fn bad(i: u64) -> u64 { witness(i) }",
        "proof-of-u64": "fn bad(i: u64) -> Lt(i, 3) { proof(i) }",
        "pack-untyped": "fn bad(i: u64) -> u64 { witness(pack(i, refl(i))) }",
        "pack-u64": "fn bad(i: u64) -> u64 { pack(i, refl(i)) }",
        "signed-witness": "fn bad(x: i64) -> refine(fn(j) { Eq(j, j) }) { pack(x, refl(0)) }",
        "data-predicate": "fn bad(s: refine(fn(j) { u64 })) -> i64 { 0 }",
        "family-arity": "fn bad(s: refine(fn(a, b) { Lt(a, b) })) -> i64 { 0 }",
        "erased-refinement": "fn bad(s: erased(refine(fn(j) { Lt(j, 3) }))) -> i64 { 0 }",
        "export-argument": "export fn bad(s: refine(fn(j) { Lt(j, 3) })) -> i64 { 0 }",
        "branch-escape": "fn bad(i: u64) -> i64 { at(3, [1, 2, 3], if_lt(i, 3, fn(p) { pack(i, p) }, pack(i, p))) }",
        "arity": "fn bad(s: refine(fn(j) { Lt(j, 3) })) -> u64 { witness(s, s) }",
    }
    for name, body in source_invalid.items():
        path = temporary / f"refine-{name}.jh"
        path.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert str(path) in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"refine-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False)
        assert not obj.exists()

    below3 = "(Refine (lam j U64 (Lt j 3)))"
    core_invalid = {
        "false-pack": "(def bad (Refine (lam j U64 (Lt j 3))) (pack (lam j U64 (Lt j 3)) 5 (decide-lt 0 3)))",
        "other-family": "(def bad (Refine (lam j U64 (Lt j 4))) (pack (lam j U64 (Lt j 3)) 0 (decide-lt 0 3)))",
        "data-predicate": "(def bad (pi s (Refine (lam j U64 U64)) I64) (lam s (Refine (lam j U64 U64)) (int 0)))",
        "erased-refinement": f"(def bad (pi0 s {below3} I64) (lam0 s {below3} (int 0)))",
        "runtime-proof": f"(def bad (pi s {below3} I64) (lam s {below3} (index (array (int 1) (int 2) (int 3)) (proof s) (proof s))))",
        "witness-of-u64": "(def bad U64 (witness 3))",
        "proof-binder": f"(def bad (pi s (Lt 0 1) I64) (lam s (Lt 0 1) (int 0)))",
    }
    for name, body in core_invalid.items():
        path = temporary / f"refine-{name}.jhc"
        path.write_text(core_prefix + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert "core:" in diagnostic.stderr, (name, diagnostic.stderr)
    # Code generation also refuses a refinement from a foreign caller.
    foreign = temporary / "refine-foreign.jhc"
    foreign.write_text(f"(export bad (pi s {below3} U64) (lam s {below3} (witness s)))\n")
    diagnostic = command("emit-mir", foreign, source=False, success=False)
    assert diagnostic.returncode == 1 and "scalar arguments" in diagnostic.stderr, diagnostic.stderr

    reference = {}
    for _, name, _, body in definitions(core_text):
        reference[name] = evaluate(body, reference.copy())
    rng = random.Random(0x5C)
    values = [0, 1, 2, 3, 4, 5, 6, 1 << 63, MAX, *(rng.getrandbits(64) for _ in range(12))]
    formatted = temporary / "refine-formatted.jh"
    formatted.write_text(command("fmt", example).stdout)
    assert mir == command("emit-mir", formatted, "--lib").stdout
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            for is_source, suffix in ((True, "jh"), (False, "jhc")):
                obj = temporary / f"refine-{target}{level}-{suffix}.o"
                options = ["--lib"] if is_source else []
                command("emit-obj", example if is_source else core_example, *options,
                        "--target", target, level, "-o", str(obj), source=is_source)
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                library = temporary / f"refine{level}-{suffix}.so"
                cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
                run([*cc, "-shared", str(obj), "-o", str(library)])
                native = ctypes.CDLL(str(library))
                for name, restype in (("wrap", ctypes.c_int64), ("clamp", ctypes.c_uint64),
                                      ("last", ctypes.c_int64)):
                    getattr(native, name).argtypes = [ctypes.c_uint64]
                    getattr(native, name).restype = restype
                for x in values:
                    assert native.wrap(x) == reference["wrap"](x) == [11, 22, 33][x if x < 3 else 0], x
                    assert native.clamp(x) == reference["clamp"](x)[1] == (x if x < 4 else 0), x
                    expected = [10, 20, 30, 40][x - 1] if 1 <= x <= 4 else -1
                    assert native.last(x) == reference["last"](x) == expected, x
    print(f"dependent refinements: paired source/core execution, projections, {len(source_invalid)} source and {len(core_invalid)} core rejections passed")
