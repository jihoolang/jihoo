"""u64 addition and the order of the naturals, called by tests/core.py."""
import ctypes
import json
import os
import platform
import random
import re
import shlex
import struct

MAX = (1 << 64) - 1


def validate_order(compiler, root, temporary, environment, run, definitions, evaluate):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    example = root / "examples/core_order.jh"
    core_example = root / "examples/core_order.jhc"
    source_text = example.read_text()
    core_text = core_example.read_text()
    prefix = source_text.split("export fn pairs")[0]
    core_prefix = core_text.split("(export pairs")[0]
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable",
                   "JIHOO_LD": "/unavailable"}
    command("check", example, env=unavailable)
    command("check", core_example, source=False, env=unavailable)
    mir = command("emit-mir", example, "--lib").stdout
    assert mir == command("emit-mir", core_example, source=False).stdout
    # pairs: one loop and two loads; prefix: a comparison of k, then a loop
    # with one load; next: a checked i + 1, a comparison and one load.
    assert mir.count("fn ") == 3 and mir.count("switch ") == 4, mir
    assert len(re.findall(r"= _\d+\[_\d+\]", mir)) == 4, mir
    for absent in ("assert", "call", "Lt", "lt_", "closure"):
        assert absent not in mir, (absent, mir)
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 58 and not result.stdout and not result.stderr

    # u64 sums trap rather than wrap, from runtime values and literals.
    rest = source_text[source_text.index("export fn pairs"):source_text.index("fn main()")]
    traps = {
        "next": f"fn main() -> i64 {{ next({MAX}) }}",
        "literal": f"fn main() -> i64 {{ if_lt({MAX} + 1, 3, fn(p) {{ 1 }}, 2) }}",
        "unused": f"fn ignore(i: u64) -> i64 {{ 7 }}\nfn main() -> i64 {{ ignore({MAX} + 1) }}",
    }
    for name, body in traps.items():
        path = temporary / f"order-trap-{name}.jh"
        path.write_text(prefix + rest + body + "\n")
        for level in ("-O0", "-O2"):
            assert command("run", path, level, success=False).returncode == 132, (name, level)

    source_invalid = {
        "wrapped-literal": f"fn bad() -> Eq({MAX} + 1, 0) {{ refl(0) }}",
        "decide-beyond-u64": f"fn bad() -> Lt(0, {MAX} + 1) {{ decide_lt(0, {MAX} + 1) }}",
        "wrong-shift": "fn bad(i: u64, n: u64, p: erased(Lt(i, n))) -> Lt(i + 1, n) { lt_add(i, n, 1, p) }",
        "strict-le": "fn bad(x: u64, y: u64, z: u64, p: erased(Lt(x, y)), q: erased(Lt(y, z + 2))) -> Lt(x, z) { lt_le(x, y, z, p, q) }",
        "le-le": "fn bad(x: u64, y: u64, z: u64, p: erased(Lt(x, y + 1)), q: erased(Lt(y, z + 1))) -> Lt(x, z) { lt_le(x, y, z, p, q) }",
        "wrong-cancel": "fn bad(a: u64, b: u64, p: erased(Lt(a + 1, b + 2))) -> Lt(a, b) { lt_cancel(a, b, 1, p) }",
        "reverse": "fn bad(a: u64, b: u64, p: erased(Lt(a, b))) -> Lt(b, a) { lt_cancel(b, a, 0, p) }",
        "irreflexive": "fn bad(a: u64) -> Lt(a, a) { lt_le(a, a, a, weaken(a, a, lt_add(0, 0, a, decide_lt(0, 0))), lt_add(0, 1, a, decide_lt(0, 1))) }",
        "u64-subtraction": "fn bad(i: u64) -> u64 { i - 1 }",
        "u64-product": "fn bad(i: u64) -> u64 { i * 2 }",
        "mixed-sum": "fn bad(i: u64, x: i64) -> u64 { i + x }",
        "prefix-too-long": "export fn bad(k: u64) -> i64 { if_lt(k, 6, fn(q) { fold(k, 0, fn(i, p, acc) { acc + index([10, 20, 30, 40], i, lt_le(i, k, 4, p, q)) }) }, -1) }",
        "next-unchecked": "export fn bad(i: u64) -> i64 { if_lt(i, 4, fn(p) { index([10, 20, 30, 40], i + 1, p) }, -1) }",
        "short-array": "fn bad(n: u64, xs: [i64; n]) -> i64 { fold(n, 0, fn(i, p, acc) { index(xs, i + 1, lt_add(i, n, 1, p)) }) }",
        "relevant-rule": "export fn bad() -> i64 { lt_add(0, 1, 0, decide_lt(0, 1)) }",
        "runtime-evidence": "fn bad(p: erased(Lt(0, 1))) -> u64 { p + 1 }",
        "signed-rule-index": "fn bad(x: i64, p: erased(Lt(0, 1))) -> Lt(0, 1) { lt_add(0, 1, x, p) }",
        "rule-arity": "fn bad(p: erased(Lt(0, 1))) -> Lt(0, 1) { lt_add(0, 1, p) }",
    }
    for name, body in source_invalid.items():
        path = temporary / f"order-{name}.jh"
        path.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert str(path) in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"order-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False)
        assert not obj.exists()

    core_invalid = {
        "false-le": "(def bad (Lt 1 0) (lt-le 0 1 0 (decide-lt 0 1) (decide-lt 1 1)))",
        "false-add": "(def bad (Lt 1 1) (lt-add 1 0 1 (decide-lt 0 1)))",
        "false-cancel": "(def bad (Lt 1 0) (lt-cancel 1 0 1 (decide-lt 0 1)))",
        "wrapped": f"(def bad (Eq (uadd {MAX} 1) 0) (refl 0))",
        "decided-sum": "(def bad (Lt (uadd 1 1) 2) (decide-lt (uadd 1 1) 2))",
        "signed-sum": "(def bad U64 (uadd (int 1) 1))",
        "relevant-sum": "(def bad (pi0 p (Lt 0 1) U64) (lam0 p (Lt 0 1) (uadd p 1)))",
    }
    for name, body in core_invalid.items():
        path = temporary / f"order-{name}.jhc"
        path.write_text(core_prefix + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert "core:" in diagnostic.stderr, (name, diagnostic.stderr)

    reference = {}
    for _, name, _, body in definitions(core_text):
        reference[name] = evaluate(body, reference.copy())
    rng = random.Random(0x0D3E)
    xs = [0, 1, -1, 3, -5, 1 << 40, *(rng.randrange(-(1 << 29), 1 << 29) for _ in range(12))]
    ks = [0, 1, 2, 3, 4, 5, 6, 1 << 63, MAX, *(rng.getrandbits(64) for _ in range(8))]
    # next(MAX) traps, as tested above; every other index is compared.
    indices = [k for k in ks if k != MAX] + [MAX - 1]
    formatted = temporary / "order-formatted.jh"
    formatted.write_text(command("fmt", example).stdout)
    assert mir == command("emit-mir", formatted, "--lib").stdout
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            for is_source, suffix in ((True, "jh"), (False, "jhc")):
                obj = temporary / f"order-{target}{level}-{suffix}.o"
                options = ["--lib"] if is_source else []
                command("emit-obj", example if is_source else core_example, *options,
                        "--target", target, level, "-o", str(obj), source=is_source)
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                library = temporary / f"order{level}-{suffix}.so"
                cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
                run([*cc, "-shared", str(obj), "-o", str(library)])
                native = ctypes.CDLL(str(library))
                native.pairs.argtypes = [ctypes.c_int64]
                native.pairs.restype = ctypes.c_int64
                native.prefix.argtypes = [ctypes.c_uint64]
                native.prefix.restype = ctypes.c_int64
                native.next.argtypes = [ctypes.c_uint64]
                native.next.restype = ctypes.c_int64
                for x in xs:
                    assert native.pairs(x) == reference["pairs"](x) == 8 * x, x
                for k in ks:
                    expected = sum([10, 20, 30, 40][:k]) if k <= 4 else -1
                    assert native.prefix(k) == reference["prefix"](k) == expected, k
                for i in indices:
                    expected = [10, 20, 30, 40][i + 1] if i + 1 < 4 else -1
                    assert native.next(i) == reference["next"](i) == expected, i
    print(f"dependent order: paired source/core execution, u64 traps, {len(source_invalid)} source and {len(core_invalid)} core rejections passed")
