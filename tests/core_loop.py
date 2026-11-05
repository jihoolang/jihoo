"""Bounded loops and i64 arithmetic in the dependent core, called by tests/core.py."""
import ctypes
import json
import os
import platform
import random
import re
import shlex
import struct


def validate_loop(compiler, root, temporary, environment, run, definitions, evaluate):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    example = root / "examples/core_loop.jh"
    core_example = root / "examples/core_loop.jhc"
    source_text = example.read_text()
    core_text = core_example.read_text()
    prefix = source_text.split("export fn weighted")[0]
    core_prefix = core_text.split("(export weighted")[0]
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable",
                   "JIHOO_LD": "/unavailable"}
    command("check", example, env=unavailable)
    command("check", core_example, source=False, env=unavailable)
    mir = command("emit-mir", example, "--lib").stdout
    assert mir == command("emit-mir", core_example, source=False).stdout
    # Two loops, each with one comparison; loads without bounds checks;
    # no evidence, calls or closures.
    assert mir.count("fn ") == 2 and mir.count("switch ") == 2 and len(re.findall(r"= _\d+\[_\d+\]", mir)) == 2, mir
    for absent in ("assert", "call", "Lt", "fold", "closure"):
        assert absent not in mir, (absent, mir)
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 97 and not result.stdout and not result.stderr

    # Overflow traps at runtime, whether or not its operands are constants;
    # the kernel never folds it into a wrapped value.
    traps = {
        "literal": "fn main() -> i64 { 9223372036854775807 + 1 }",
        "negative": "fn main() -> i64 { -9223372036854775808 - 1 }",
        "product": "fn main() -> i64 { 4611686018427387904 * 2 }",
        "loop": "fn main() -> i64 { repeat(2, 9223372036854775807) }",
        # Arguments are evaluated before the call, as in ordinary jihoo,
        # even when beta reduction substitutes them away.
        "unused-argument": "fn ignore(x: i64) -> i64 { 7 }\nfn main() -> i64 { ignore(9223372036854775807 + 1) }",
        "untaken-branch": "fn pick(i: u64, x: i64) -> i64 { if_lt(i, 1, fn(p) { x }, 0) }\nfn main() -> i64 { pick(5, 9223372036854775807 + 1) }",
        "unused-loop": "fn ignore(x: i64) -> i64 { 7 }\nfn main() -> i64 { ignore(repeat(2, 9223372036854775807)) }",
        "unused-array": "fn first(n: u64, xs: [i64; n]) -> i64 { 7 }\nfn main() -> i64 { first(2, [1, 9223372036854775807 * 2]) }",
    }
    loop = source_text[source_text.index("export fn repeat"):source_text.index("fn main()")]
    for name, body in traps.items():
        path = temporary / f"loop-trap-{name}.jh"
        path.write_text(prefix + loop + body + "\n")
        for level in ("-O0", "-O2"):
            assert command("run", path, level, success=False).returncode == 132, (name, level)
    folded = temporary / "loop-folded.jh"
    folded.write_text(prefix + "export fn k() -> i64 { 2 * 3 + 1 - fold(0, 5, fn(i, p, acc) { acc * 2 }) }\n")
    folded_mir = command("emit-mir", folded, "--lib").stdout
    assert "2_i64" in folded_mir and "*" not in folded_mir and "goto" not in folded_mir, folded_mir

    source_invalid = {
        "u64-subtraction": "fn bad(i: u64) -> u64 { i - 1 }",
        "u64-operands": "fn bad(i: u64) -> i64 { i + 1 }",
        "division": "fn bad(x: i64) -> i64 { x / 2 }",
        "comparison": "fn bad(x: i64) -> i64 { x < 2 }",
        "longer-loop": "fn bad() -> i64 { fold(3, 0, fn(i, p, acc) { index([1, 2], i, p) }) }",
        "wrong-index": "fn bad(n: u64, xs: [i64; n]) -> i64 { fold(n, 0, fn(i, p, acc) { index(xs, 0, p) }) }",
        "other-bound": "fn bad(n: u64, m: u64, xs: [i64; n]) -> i64 { fold(m, 0, fn(i, p, acc) { index(xs, i, p) }) }",
        "runtime-proof": "fn bad() -> i64 { fold(3, 0, fn(i, p, acc) { p }) }",
        "index-result": "fn bad() -> i64 { fold(3, 0, fn(i, p, acc) { i }) }",
        "arity": "fn bad() -> i64 { fold(3, 0, fn(i, acc) { acc }) }",
        "typed-binder": "fn bad() -> i64 { fold(3, 0, fn(i: u64, p, acc) { acc }) }",
        "u64-result": "fn bad(n: u64) -> u64 { fold(n, 0, fn(i, p, acc) { acc }) }",
        "signed-count": "fn bad(x: i64) -> i64 { fold(x, 0, fn(i, p, acc) { acc }) }",
        "proof-escape": "fn bad() -> i64 { fold(3, 0, fn(i, p, acc) { acc }) + index([1, 2, 3], 2, p) }",
        "proof-arithmetic": "fn bad(p: erased(Lt(0, 1))) -> i64 { p + 1 }",
        "missing-body": "fn bad() -> i64 { fold(3, 0) }",
        "named-body": "fn bad() -> i64 { fold(3, 0, get) }",
        "foreign-array": "export fn bad(xs: [i64; 3]) -> i64 { sum(3, xs) }",
    }
    for name, body in source_invalid.items():
        path = temporary / f"loop-{name}.jh"
        path.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert str(path) in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"loop-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False)
        assert not obj.exists()

    core_invalid = {
        "relevant-bound": "(def bad I64 (fold 3 (int 0) (lam i U64 (lam p (Lt i 3) (lam acc I64 acc)))))",
        "wrong-bound": "(def bad I64 (fold 3 (int 0) (lam i U64 (lam0 p (Lt i 4) (lam acc I64 (index (array (int 1) (int 2) (int 3) (int 4)) i p))))))",
        "u64-accumulator": "(def bad I64 (fold 3 (int 0) (lam i U64 (lam0 p (Lt i 3) (lam acc U64 (int 0))))))",
        "u64-arithmetic": "(def bad U64 (add 1 2))",
        "mixed-arithmetic": "(def bad I64 (add (int 1) 2))",
        "signed-count": "(def bad I64 (fold (int 3) (int 0) (lam i U64 (lam0 p (Lt i 3) (lam acc I64 acc)))))",
        "proof-arithmetic": "(def bad (pi0 p (Lt 0 1) I64) (lam0 p (Lt 0 1) (add p (int 1))))",
        "not-a-function": "(def bad I64 (fold 3 (int 0) (int 1)))",
    }
    for name, body in core_invalid.items():
        path = temporary / f"loop-{name}.jhc"
        path.write_text(core_prefix + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert "core:" in diagnostic.stderr, (name, diagnostic.stderr)

    # A loop body that is a function after normalization, not a lambda:
    # lowering sees it eta-expanded, with the branch inside the loop.
    conditional_text = core_text + """
(export conditional
  (pi n U64 I64)
  (lam n U64
    (fold n (int 0)
      (if-eq n 0 e
        (lam i U64 (lam0 p (Lt i n) (lam acc I64 (add acc (int 1)))))
        (lam i U64 (lam0 p (Lt i n) (lam acc I64 (add acc (int 2)))))))))
"""
    conditional = temporary / "loop-conditional.jhc"
    conditional.write_text(conditional_text)
    conditional_mir = command("emit-mir", conditional, source=False).stdout
    assert "call" not in conditional_mir and "assert" not in conditional_mir
    reference = {}
    for _, name, _, body in definitions(conditional_text):
        reference[name] = evaluate(body, reference.copy())
    rng = random.Random(0x100F)
    small = [0, 1, -1, 2, -2, 7, -7, 1 << 40, -(1 << 40),
             *(rng.randrange(-(1 << 58), 1 << 58) for _ in range(16))]
    formatted = temporary / "loop-formatted.jh"
    formatted.write_text(command("fmt", example).stdout)
    assert mir == command("emit-mir", formatted, "--lib").stdout
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            for is_source, suffix in ((True, "jh"), (False, "jhc")):
                obj = temporary / f"loop-{target}{level}-{suffix}.o"
                options = ["--lib"] if is_source else []
                command("emit-obj", example if is_source else conditional, *options,
                        "--target", target, level, "-o", str(obj), source=is_source)
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                library = temporary / f"loop{level}-{suffix}.so"
                cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
                run([*cc, "-shared", str(obj), "-o", str(library)])
                native = ctypes.CDLL(str(library))
                native.weighted.argtypes = [ctypes.c_int64]
                native.weighted.restype = ctypes.c_int64
                native.repeat.argtypes = [ctypes.c_uint64, ctypes.c_int64]
                native.repeat.restype = ctypes.c_int64
                for x in small:
                    expected = reference["weighted"](x)
                    assert expected == x + 2 * (x - 1) + 3 * (2 * x) - 4 * x
                    assert native.weighted(x) == expected, x
                if not is_source:
                    native.conditional.argtypes = [ctypes.c_uint64]
                    native.conditional.restype = ctypes.c_int64
                    for n in (0, 1, 2, 5, 1000):
                        assert native.conditional(n) == reference["conditional"](n) == 2 * n
                for n in (0, 1, 2, 3, 17, 1000):
                    for x in small[:9]:
                        expected = reference["repeat"](n)(x)
                        assert expected == n * x and native.repeat(n, x) == expected, (n, x)
    print(f"dependent loops: paired source/core execution, overflow traps, {len(source_invalid)} source and {len(core_invalid)} core rejections passed")
