"""u64 subtraction with evidence, called by tests/core.py."""
import ctypes
import json
import os
import platform
import random
import re
import shlex
import struct

MAX = (1 << 64) - 1


def validate_sub(compiler, root, temporary, environment, run, definitions, evaluate):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    example = root / "examples/core_sub.jh"
    core_example = root / "examples/core_sub.jhc"
    source_text = example.read_text()
    core_text = core_example.read_text()
    prefix = source_text.split("fn main()")[0]
    core_prefix = core_text.split("(export convolve")[0]
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable",
                   "JIHOO_LD": "/unavailable"}
    command("check", example, env=unavailable)
    command("check", core_example, source=False, env=unavailable)
    mir = command("emit-mir", example, "--lib").stdout
    assert mir == command("emit-mir", core_example, source=False).stdout
    # convolve: one loop, two loads and n - (i + 1); last: two comparisons,
    # k - 1 and one load. No evidence or bounds assertions.
    assert mir.count("fn ") == 2 and mir.count("switch ") == 3, mir
    assert len(re.findall(r"= _\d+\[_\d+\]", mir)) == 3 and mir.count(" - ") == 2, mir
    for absent in ("assert", "call", "Lt", "sub", "closure"):
        assert absent not in mir, (absent, mir)
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 143 and not result.stdout and not result.stderr

    # Cancellation does not remove the evaluation of what it cancels.
    traps = {
        "cancelled-sum": "fn main() -> i64 { if_eq(sub(18446744073709551615 + 1, 1, lt_add(0, 18446744073709551615 + 1, 1, zero_le(18446744073709551615))), 18446744073709551615, fn(e) { 7 }, 9) }",
    }
    for name, body in traps.items():
        path = temporary / f"sub-trap-{name}.jh"
        path.write_text(prefix + body + "\n")
        for level in ("-O0", "-O2"):
            assert command("run", path, level, success=False).returncode == 132, (name, level)

    # Cancellation and computation in conversion.
    valid = prefix + """
fn back(k: u64, p: erased(Lt(0, k))) -> Eq(pred(k, p) + 1, k) { refl(k) }
fn forth(i: u64) -> Eq(sub(i + 1, 1, lt_add(0, i + 1, 1, zero_le(i))), i) { refl(i) }
fn closed() -> Eq(sub(5, 2, decide_lt(2, 6)), 3) { refl(3) }
fn same(k: u64, p: erased(Lt(0, k)), q: erased(Lt(0, k))) -> Eq(pred(k, p), pred(k, q)) { refl(pred(k, p)) }
"""
    valid_path = temporary / "sub-valid.jh"
    valid_path.write_text(valid)
    command("check", valid_path, "--lib")

    source_invalid = {
        "missing-evidence": "fn bad(k: u64) -> u64 { sub(k, 1) }",
        "operator": "fn bad(k: u64) -> u64 { k - 1 }",
        "strict-evidence": "fn bad(a: u64, b: u64, p: erased(Lt(b, a))) -> u64 { sub(a, b, p) }",
        "reversed-evidence": "fn bad(a: u64, b: u64, p: erased(Lt(a, b + 1))) -> u64 { sub(a, b, p) }",
        "underflow": "fn bad() -> u64 { sub(0, 1, decide_lt(0, 1)) }",
        "closed-wrong": "fn bad() -> Eq(sub(5, 2, decide_lt(2, 6)), 2) { refl(2) }",
        "no-cancel": "fn bad(k: u64, m: u64, p: erased(Lt(0, k))) -> Eq(pred(k, p) + m, k + m) { refl(k + m) }",
        "wrapped": "fn bad(k: u64, p: erased(Lt(0, k))) -> Eq(pred(k, p), k + 18446744073709551615) { refl(k + 18446744073709551615) }",
        "mirror-strict": "fn bad(i: u64, n: u64, p: erased(Lt(i, n + 1))) -> Lt(sub(n, i, p), n) { lt_add(0, i, sub(n, i, p), zero_le(i)) }",
        "last-unchecked": "export fn bad(k: u64) -> i64 { if_lt(0, k, fn(p) { index([10, 20, 30, 40], pred(k, p), pred_lt(k, p)) }, -1) }",
        "zero-strict": "fn bad(a: u64) -> Lt(0, a) { zero_le(a) }",
        "runtime-evidence": "fn bad(k: u64, p: erased(Lt(0, k))) -> u64 { sub(k, 1, p) + p }",
        "signed": "fn bad(x: i64, p: erased(Lt(0, 1))) -> u64 { sub(x, 0, p) }",
        "arity": "fn bad(k: u64) -> Lt(0, k + 1) { zero_le(k, k) }",
    }
    for name, body in source_invalid.items():
        path = temporary / f"sub-{name}.jh"
        path.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert str(path) in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"sub-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False)
        assert not obj.exists()

    core_invalid = {
        "underflow": "(def bad U64 (usub 0 1 (decide-lt 0 1)))",
        "strict-evidence": "(def bad (pi a U64 (pi b U64 (pi0 p (Lt b a) U64))) (lam a U64 (lam b U64 (lam0 p (Lt b a) (usub a b p)))))",
        "closed-wrong": "(def bad (Eq (usub 5 2 (decide-lt 2 6)) 2) (refl 2))",
        "zero-strict": "(def bad (pi a U64 (Lt 0 a)) (lam a U64 (zero-le a)))",
        "relevant-evidence": "(def bad (pi0 p (Lt 0 1) U64) (lam0 p (Lt 0 1) (uadd (usub 0 0 p) p)))",
    }
    for name, body in core_invalid.items():
        path = temporary / f"sub-{name}.jhc"
        path.write_text(core_prefix + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert "core:" in diagnostic.stderr, (name, diagnostic.stderr)

    reference = {}
    for _, name, _, body in definitions(core_text):
        reference[name] = evaluate(body, reference.copy())
    rng = random.Random(0x5B)
    xs = [0, 1, -1, 7, -9, 1 << 40, *(rng.randrange(-(1 << 40), 1 << 40) for _ in range(12))]
    ks = [0, 1, 2, 3, 4, 5, 6, 1 << 63, MAX, *(rng.getrandbits(64) for _ in range(8))]
    formatted = temporary / "sub-formatted.jh"
    formatted.write_text(command("fmt", example).stdout)
    assert mir == command("emit-mir", formatted, "--lib").stdout
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            for is_source, suffix in ((True, "jh"), (False, "jhc")):
                obj = temporary / f"sub-{target}{level}-{suffix}.o"
                options = ["--lib"] if is_source else []
                command("emit-obj", example if is_source else core_example, *options,
                        "--target", target, level, "-o", str(obj), source=is_source)
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                library = temporary / f"sub{level}-{suffix}.so"
                cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
                run([*cc, "-shared", str(obj), "-o", str(library)])
                native = ctypes.CDLL(str(library))
                native.convolve.argtypes = [ctypes.c_int64]
                native.convolve.restype = ctypes.c_int64
                native.last.argtypes = [ctypes.c_uint64]
                native.last.restype = ctypes.c_int64
                for x in xs:
                    assert native.convolve(x) == reference["convolve"](x) == 120 + 3 * x, x
                for k in ks:
                    expected = [10, 20, 30, 40][k - 1] if 1 <= k <= 4 else -1
                    assert native.last(k) == reference["last"](k) == expected, k
    print(f"dependent subtraction: paired source/core execution, cancellation, {len(source_invalid)} source and {len(core_invalid)} core rejections passed")
