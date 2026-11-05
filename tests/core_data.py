"""Non-recursive data types and case analysis, called by tests/core.py."""
import ctypes
import json
import os
import platform
import random
import re
import shlex
import struct

MAX = (1 << 64) - 1
IMAX = (1 << 63) - 1


def validate_data(compiler, root, temporary, environment, run, definitions, evaluate):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    example = root / "examples/core_data.jh"
    core_example = root / "examples/core_data.jhc"
    source_text = example.read_text()
    core_text = core_example.read_text()
    prefix = source_text.split("fn main()")[0]
    core_prefix = core_text.split("(data Reading")[0]
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable",
                   "JIHOO_LD": "/unavailable"}
    command("check", example, env=unavailable)
    command("check", core_example, source=False, env=unavailable)
    mir = command("emit-mir", example, "--lib").stdout
    assert mir == command("emit-mir", core_example, source=False).stdout
    # lookup and first: one comparison and one load each; measure: two
    # comparisons, one product, one sum and one load. No tags, data,
    # evidence or bounds assertions.
    assert mir.count("fn ") == 3 and mir.count("switch ") == 4, mir
    assert len(re.findall(r"= _\d+\[_\d+\]", mir)) == 3, mir
    assert mir.count(" * ") == 1 and mir.count(" + ") == 1, mir
    for absent in ("assert", "call", "Lt", "Slot", "Reading", "discriminant", "closure", "{ "):
        assert absent not in mir.replace("fn ", "", 3).split("\n", 1)[1], (absent, mir)
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 64 and not result.stdout and not result.stderr

    # Data values are evaluated field by field for their traps, even when
    # unused; erased fields are not evaluated.
    overflow = f"{IMAX} + 1"
    traps = {
        "unused-value": f"fn ignore(r: Reading) -> i64 {{ 7 }}\nfn main() -> i64 {{ ignore(Reading.Value({overflow})) }}",
        "unused-scrutinee": f"fn one(r: Reading) -> i64 {{ match r {{ Missing => 1, Value(x) => 1, Scaled(x, k) => 1 }} }}\nfn main() -> i64 {{ one(Reading.Value({overflow})) }}",
        "unused-branch": f"fn ignore(r: Reading) -> i64 {{ 7 }}\nfn main() -> i64 {{ fold(1, 0, fn(i, p, acc) {{ ignore(if_lt(i, 1, fn(q) {{ Reading.Value({overflow}) }}, Reading.Missing)) }}) }}",
        "nested": f"fn ignore(s: Sample) -> i64 {{ 7 }}\nfn main() -> i64 {{ ignore(Sample.Taken(Reading.Scaled(1, {overflow}), slot(0))) }}",
    }
    for name, body in traps.items():
        path = temporary / f"data-trap-{name}.jh"
        path.write_text(prefix + body + "\n")
        for level in ("-O0", "-O2"):
            assert command("run", path, level, success=False).returncode == 132, (name, level)
    quiet = temporary / "data-quiet.jh"
    quiet.write_text(prefix + f"enum Proven {{\n    Yes(erased(Eq({MAX} + 1, {MAX} + 1)))\n}}\nfn ignore(v: Proven) -> i64 {{ 7 }}\nfn main() -> i64 {{ ignore(Proven.Yes(refl({MAX} + 1))) }}\n")
    for level in ("-O0", "-O2"):
        assert command("run", quiet, level, success=False).returncode == 7, level

    valid = prefix + """
fn computed() -> Eq(position(Slot.Full(pack(2, decide_lt(2, 4)))), 2) { refl(2) }
fn empty() -> Eq(position(Slot.Empty), 0) { refl(0) }
fn safe(s: Slot) -> refine(fn(j) { Lt(j, 4) }) {
    match s {
        Full(j) => j
        Slot.Empty => pack(0, decide_lt(0, 4))
    }
}
fn ignored(r: Reading) -> i64 {
    match r {
        Missing => 0
        Value(_) => 1
        Reading.Scaled(_, k) => k
    }
}
fn nested(s: Sample) -> u64 {
    match s {
        Taken(r, at) => match at {
            Empty => 0
            Full(j) => witness(j) + 1
        }
    }
}
fn nested_bound(s: Sample) -> Lt(nested(s), 5) {
    induct(fn(t) { Lt(nested(t), 5) }, fn(r, at) { induct(fn(u) { Lt(nested(Sample.Taken(r, u)), 5) }, decide_lt(0, 5), fn(j) { lt_add(witness(j), 4, 1, proof(j)) }, at) }, s)
}
export fn via(i: u64) -> i64 { index([1, 2, 3, 4, 5], nested(Sample.Taken(Reading.Missing, slot(i))), nested_bound(Sample.Taken(Reading.Missing, slot(i)))) }
"""
    valid_path = temporary / "data-valid.jh"
    valid_path.write_text(valid)
    command("check", valid_path, "--lib")

    source_invalid = {
        "missing-arm": "fn bad(r: Reading) -> i64 { match r { Missing => 0, Value(x) => x } }",
        "duplicate-arm": "fn bad(s: Slot) -> i64 { match s { Empty => 0, Empty => 1 } }",
        "field-count": "fn bad(r: Reading) -> i64 { match r { Missing => 0, Value(x, y) => x, Scaled(x, k) => k } }",
        "too-few-fields": "fn bad(r: Reading) -> i64 { match r { Missing => 0, Value(x) => x, Scaled(x) => x } }",
        "guard": "fn bad(r: Reading) -> i64 { match r { Missing => 0, Value(x) if true => x, Scaled(x, k) => k } }",
        "no-expected": "fn bad(s: Slot) -> u64 { witness(match s { Empty => pack(0, decide_lt(0, 4)), Full(j) => j }) }",
        "match-u64": "fn bad(i: u64) -> i64 { match i { Empty => 0, Full(j) => 1 } }",
        "match-evidence": "fn bad(p: erased(Lt(0, 1))) -> i64 { match p { Empty => 0, Full(j) => 1 } }",
        "erased-recursive": "enum List {\n    Nil\n    Cons(i64, erased(List))\n}",
        "heap-holds-flat": "enum Flat {\n    A\n}\nenum Heap {\n    Nil\n    Cons(Flat, Heap)\n}",
        "array-field": "enum Holder {\n    Holds([i64; 3])\n}",
        "unqualified": "fn bad(i: u64, p: erased(Lt(i, 4))) -> Slot { Full(pack(i, p)) }",
        "unknown-variant": "fn bad() -> Slot { Slot.Nothing }",
        "field-type": "fn bad() -> Slot { Slot.Full(5) }",
        "missing-field": "fn bad() -> Reading { Reading.Scaled(5) }",
        "false-by-cases": "fn bad(s: Slot) -> Lt(position(s), 3) { induct(fn(t) { Lt(position(t), 3) }, decide_lt(0, 3), fn(j) { proof(j) }, s) }",
        "missing-case": "fn bad(s: Slot) -> Lt(position(s), 4) { induct(fn(t) { Lt(position(t), 4) }, decide_lt(0, 4), s) }",
        "export-argument": "export fn bad(s: Slot) -> i64 { 0 }",
        "export-result": "export fn bad(i: u64) -> Slot { slot(i) }",
        "erased-data-runtime": "fn bad(s: erased(Slot)) -> u64 { position(s) }",
        "arm-types": "fn bad(s: Slot) -> i64 { match s { Empty => 0, Full(j) => j } }",
        "parameters": "enum Box(T: type) {\n    B(u64)\n}",
        "duplicate-variant": "enum Twice {\n    A\n    A\n}",
        "arm-scope": "fn bad(r: Reading) -> i64 { match r { Missing => x, Value(x) => x, Scaled(x, k) => k } }",
        "runtime-proof-field": "enum Proven {\n    Yes(erased(Lt(0, 1)))\n}\nfn id(x: u64) -> u64 { x }\nfn bad(v: Proven) -> u64 { match v { Yes(e) => id(e) } }",
        "duplicate-type": "enum Slot {\n    Other\n}",
    }
    for name, body in source_invalid.items():
        path = temporary / f"data-{name}.jh"
        path.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert str(path) in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"data-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False)
        assert not obj.exists()

    refine4 = "(Refine (lam j U64 (Lt j 4)))"
    core_invalid = {
        "erased-recursive": "(data L (Nil L) (Cons (pi x I64 (pi0 t L L))))",
        "array-field": "(data B (Holds (pi a (Array 3) B)))",
        "relevant-proof": "(data B (W (pi p (Lt 0 1) B)))",
        "function-field": "(data B (F (pi f (pi x U64 U64) B)))",
        "foreign-result": "(data B (C (pi x U64 Slot)))",
        "large-motive": f"(def bad (pi s Slot (Type 0)) (lam s Slot (induct Slot (lam t Slot (Type 0)) U64 (lam j {refine4} I64) s)))",
        "motive-domain": f"(def bad (pi s Slot I64) (lam s Slot (induct Slot (lam t U64 I64) (int 0) (lam j {refine4} (int 1)) s)))",
        "case-type": f"(def bad (pi s Slot I64) (lam s Slot (induct Slot (lam t Slot I64) 0 (lam j {refine4} (int 1)) s)))",
        "false-dependent": f"(def bad (pi s Slot (Lt (app read (array (int 1) (int 2) (int 3) (int 4)) s (int 0)) 3)) (lam s Slot (induct Slot (lam t Slot (Lt 0 3)) (decide-lt 0 3) (lam j {refine4} (decide-lt 0 3)) s)))",
        "runtime-proof-field": "(data P (W (pi0 e (Lt 0 1) P)))\n(def bad (pi v P U64) (lam v P (induct P (lam t P U64) (lam0 e (Lt 0 1) e) v)))",
        "prop-into-data": "(inductive Ev 0 (ev Ev))\n(def bad (pi0 e Ev U64) (lam0 e Ev (induct Ev U64 0 e)))",
        "missing-field": "(def bad Slot (Full))",
    }
    for name, body in core_invalid.items():
        path = temporary / f"data-{name}.jhc"
        path.write_text(core_prefix + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert "core:" in diagnostic.stderr, (name, diagnostic.stderr)
    foreign = temporary / "data-foreign.jhc"
    foreign.write_text(core_prefix + "(export bad (pi s Slot I64) (lam s Slot (int 0)))\n")
    diagnostic = command("emit-mir", foreign, source=False, success=False)
    assert diagnostic.returncode == 1 and "scalar arguments" in diagnostic.stderr, diagnostic.stderr

    reference = {}
    for _, name, _, body in definitions(core_text):
        reference[name] = evaluate(body, reference.copy())
    rng = random.Random(0x5D)
    indices = [0, 1, 2, 3, 4, 5, 1 << 63, MAX, *(rng.getrandbits(64) for _ in range(10))]
    xs = [0, 1, -1, 7, -9, 1 << 40, -(1 << 40), *(rng.randrange(-(1 << 40), 1 << 40) for _ in range(6))]
    formatted = temporary / "data-formatted.jh"
    formatted.write_text(command("fmt", example).stdout)
    assert mir == command("emit-mir", formatted, "--lib").stdout
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            for is_source, suffix in ((True, "jh"), (False, "jhc")):
                obj = temporary / f"data-{target}{level}-{suffix}.o"
                options = ["--lib"] if is_source else []
                command("emit-obj", example if is_source else core_example, *options,
                        "--target", target, level, "-o", str(obj), source=is_source)
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                library = temporary / f"data{level}-{suffix}.so"
                cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
                run([*cc, "-shared", str(obj), "-o", str(library)])
                native = ctypes.CDLL(str(library))
                for name in ("lookup", "first"):
                    getattr(native, name).argtypes = [ctypes.c_uint64]
                    getattr(native, name).restype = ctypes.c_int64
                native.measure.argtypes = [ctypes.c_uint64, ctypes.c_int64]
                native.measure.restype = ctypes.c_int64
                for i in indices:
                    inside = i < 4
                    assert native.lookup(i) == reference["lookup"](i) == ([10, 20, 30, 40][i] if inside else -1), i
                    assert native.first(i) == reference["first"](i) == [5, 6, 7, 8][i if inside else 0], i
                    for x in xs:
                        expected = (x if i < 2 else 3 * x) + ([1, 2, 3, 4][i] if inside else 0)
                        assert native.measure(i, x) == reference["measure"](i)(x) == expected, (i, x)
    print(f"dependent data: paired source/core execution, case analysis, kept traps, {len(source_invalid)} source and {len(core_invalid)} core rejections passed")
