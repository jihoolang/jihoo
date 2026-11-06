"""Owned heap buffers and the kernel's linearity check, called by tests/core.py."""
import ctypes
import json
import os
import platform
import random
import re
import shlex
import struct

MAX = (1 << 64) - 1

# Counts the allocations and frees of the linked object, so that a native
# call can be checked to free exactly what it allocates.
COUNTER = r"""
#include <stddef.h>
void *__real_malloc(size_t);
void __real_free(void *);
long allocations, frees;
void *__wrap_malloc(size_t n) { allocations++; return __real_malloc(n); }
void __wrap_free(void *p) { frees++; __real_free(p); }
"""


def validate_buffer(compiler, root, temporary, environment, run, definitions, evaluate, buffers):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    example = root / "examples/core_buffer.jh"
    core_example = root / "examples/core_buffer.jhc"
    source_text = example.read_text()
    core_text = core_example.read_text()
    prefix = source_text.split("fn main()")[0]
    core_prefix = core_text.split("(export total")[0]
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable",
                   "JIHOO_LD": "/unavailable"}
    command("check", example, env=unavailable)
    command("check", core_example, source=False, env=unavailable)
    mir = command("emit-mir", example, "--lib").stdout
    assert mir == command("emit-mir", core_example, source=False).stdout
    # Two exports, then malloc and free. Each export allocates once and frees
    # once; the only assertions are the allocations' null checks, and loads
    # and stores have no bounds checks.
    assert mir.count("fn ") == 4 and "fn malloc [malloc] (extern)" in mir, mir
    assert "fn free [free] (extern)" in mir, mir
    assert mir.count("call malloc(") == 2 and mir.count("call free(") == 2, mir
    assert mir.count("assert ") == 2 and mir.count('"allocation failed"') == 2, mir
    for absent in ("Lt", "closure", "Buffer"):
        assert absent not in mir, (absent, mir)
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 30 and not result.stdout and not result.stderr

    # Allocation sizes are checked, and a failed allocation stops the program.
    traps = {
        "size-overflow": "fn main() -> i64 { total(2305843009213693951, 1) }",
        "length-overflow": f"fn main() -> i64 {{ total({MAX}, 1) }}",
    }
    for name, body in traps.items():
        path = temporary / f"buffer-trap-{name}.jh"
        path.write_text(prefix + body + "\n")
        for level in ("-O0", "-O2"):
            assert command("run", path, level, success=False).returncode == 132, (name, level)
    huge = temporary / "buffer-huge.jh"
    huge.write_text(prefix + "fn main() -> i64 { total(576460752303423487, 1) }\n")
    for level in ("-O0", "-O2"):
        result = command("run", huge, level, success=False)
        assert result.returncode != 0 and "allocation failed" in result.stderr, (level, result.stderr)

    valid = prefix + """
fn give(b: buffer(3), x: i64) -> i64 { free(b, x) }
fn first_argument(b: buffer(3)) -> i64 { give(b, 1) }
fn both(b: buffer(3), c: buffer(2), x: i64) -> i64 { free(b, free(c, x)) }
fn back(b: buffer(3)) -> buffer(3) { load(b, 0, decide_lt(0, 3), fn(x, c) { store(c, 1, x, decide_lt(1, 3)) }) }
fn branches(i: u64, b: buffer(3)) -> i64 { if_lt(i, 3, fn(p) { load(b, i, p, fn(x, c) { free(c, x) }) }, free(b, 0)) }
fn chosen(i: u64) -> buffer(2) { if_lt(i, 2, fn(p) { alloc(2, 1) }, alloc(2, 2)) }
fn empty_loop(b: buffer(3)) -> buffer(3) { fold(0, b, fn(i, p, acc) { acc }) }
fn nonempty(n: u64, b: buffer(n + 1)) -> Lt(0, n + 1) { zero_le(n) }
fn head(n: u64, b: buffer(n + 1)) -> i64 { load(b, 0, nonempty(n, b), fn(x, c) { free(c, x) }) }
fn empty() -> i64 { free(alloc(0, 7), 1) }
enum Choice {
    Keep
    Drop(i64)
}
fn decide(c: Choice, b: buffer(1)) -> i64 {
    match c {
        Keep => load(b, 0, decide_lt(0, 1), fn(x, d) { free(d, x) })
        Drop(y) => free(b, y)
    }
}
// A u64 that touches memory is evaluated once, never cancelled.
fn once(b: buffer(1)) -> u64 {
    sub(load(b, 0, decide_lt(0, 1), fn(x, c) { free(c, 5) }) + 1, 1,
        lt_add(0, load(b, 0, decide_lt(0, 1), fn(x, c) { free(c, 5) }) + 1, 1,
            zero_le(load(b, 0, decide_lt(0, 1), fn(x, c) { free(c, 5) }))))
}
export fn cancelled() -> i64 { if_lt(once(alloc(1, 0)), 9, fn(p) { 1 }, 2) }
export fn calls(x: i64, i: u64) -> i64 {
    give(alloc(3, x), 1) + both(alloc(3, 0), alloc(2, 0), 2) + give(back(alloc(3, x)), 3) +
        branches(i, alloc(3, x)) + free(chosen(i), 4) + give(empty_loop(alloc(3, x)), 5) +
        head(2, alloc(3, x)) + empty() + decide(Choice.Drop(x), alloc(1, x)) + decide(Choice.Keep, alloc(1, x))
}
"""
    valid_path = temporary / "buffer-valid.jh"
    valid_path.write_text(valid)
    command("check", valid_path, "--lib")

    source_invalid = {
        "double-free": "fn bad(b: buffer(3)) -> i64 { free(b, free(b, 0)) }",
        "use-after-free": "fn bad(b: buffer(3)) -> i64 { free(b, load(b, 0, decide_lt(0, 3), fn(x, c) { free(c, x) })) }",
        "two-calls": "fn give(b: buffer(3)) -> i64 { free(b, 0) }\nfn bad(b: buffer(3)) -> i64 { give(b) + give(b) }",
        "loop-capture": "fn bad(b: buffer(3)) -> i64 { fold(3, 0, fn(i, p, acc) { load(b, i, p, fn(x, c) { free(c, x) }) }) }",
        "out-of-bounds": "fn bad(b: buffer(3)) -> i64 { load(b, 3, decide_lt(3, 4), fn(x, c) { free(c, x) }) }",
        "unchecked-store": "fn bad(b: buffer(3), i: u64) -> buffer(3) { store(b, i, 0, decide_lt(0, 3)) }",
        "wrong-length": "fn bad(b: buffer(3)) -> buffer(4) { b }",
        "lost-store": "fn bad(b: buffer(3)) -> i64 { free(b, 0) + free(store(b, 0, 1, decide_lt(0, 3)), 0) }",
        "continuation-other": "fn bad(b: buffer(3), c: buffer(3)) -> i64 { load(b, 0, decide_lt(0, 3), fn(x, d) { free(c, free(d, x)) }) + free(c, 0) }",
        "erased-buffer": "fn bad(b: erased(buffer(3))) -> i64 { 0 }",
        "export-argument": "export fn bad(b: buffer(3)) -> i64 { free(b, 0) }",
        "export-result": "export fn bad() -> buffer(3) { alloc(3, 0) }",
        "array-element": "fn bad() -> i64 { index([alloc(1, 0)], 0, decide_lt(0, 1)) }",
        "u64-accumulator": "fn bad() -> u64 { fold(3, 0, fn(i, p, acc) { acc }) }",
        "signed-length": "fn bad(x: i64) -> i64 { free(alloc(x, 0), 0) }",
        "load-no-expected": "fn bad(b: buffer(1)) -> u64 { witness(load(b, 0, decide_lt(0, 1), fn(x, c) { free(c, x) })) }",
    }
    for name, body in source_invalid.items():
        path = temporary / f"buffer-{name}.jh"
        path.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert str(path) in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"buffer-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False)
        assert not obj.exists()

    consume = "(def consume (pi b (Buffer 1) (pi x I64 I64)) (lam b (Buffer 1) (lam x I64 (free b x))))\n"
    twice = "(def twice (pi f (pi x I64 I64) I64) (lam f (pi x I64 I64) (add (app f (int 1)) (app f (int 2)))))\n"
    core_invalid = {
        "partial-application": consume + twice + "(def bad (pi b (Buffer 1) I64) (lam b (Buffer 1) (app twice (app consume b))))",
        "captured": twice + "(def bad (pi b (Buffer 1) I64) (lam b (Buffer 1) (app twice (lam x I64 (free b x)))))",
        "leak": "(def bad (pi b (Buffer 1) I64) (lam b (Buffer 1) (int 0)))",
        "double": "(def bad (pi b (Buffer 1) I64) (lam b (Buffer 1) (free b (free b (int 0)))))",
        "erased": "(def bad (pi0 b (Buffer 1) I64) (lam0 b (Buffer 1) (int 0)))",
        "continuation-shape": "(def bad (pi b (Buffer 1) I64) (lam b (Buffer 1) (load b 0 (decide-lt 0 1) (lam x U64 (lam c (Buffer 1) (free c (int 0)))))))",
        "continuation-length": "(def bad (pi b (Buffer 1) I64) (lam b (Buffer 1) (load b 0 (decide-lt 0 1) (lam x I64 (lam c (Buffer 2) (free c x))))))",
        "result-escape": "(def bad (pi b (Buffer 1) I64) (lam b (Buffer 1) (load b 0 (decide-lt 0 1) (lam x I64 (lam c (Buffer 1) c)))))",
        "loop-closure": "(def bad I64 (fold 3 (int 0) (app (lam b (Buffer 1) (lam i U64 (lam0 p (Lt i 3) (lam acc I64 (free b acc))))) (alloc 1 (int 0)))))",
        "loop-expression": "(def bad I64 (fold 3 (int 0) (free (alloc 1 (int 0)) (lam i U64 (lam0 p (Lt i 3) (lam acc I64 acc))))))",
        "returned-closure": twice + "(def bad (pi b (Buffer 1) (pi x I64 I64)) (lam b (Buffer 1) (lam x I64 (free b x))))\n(def worse I64 (app twice (app bad (alloc 1 (int 0)))))",
        "unsaturated-branch": twice + consume + "(def bad (pi b (Buffer 1) I64) (lam b (Buffer 1) (app twice (if-lt 0 1 p (app consume b) (app consume b)))))",
    }
    for name, body in core_invalid.items():
        path = temporary / f"buffer-{name}.jhc"
        path.write_text(core_prefix + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert "core:" in diagnostic.stderr, (name, diagnostic.stderr)

    reference = {}
    for _, name, _, body in definitions(core_text):
        reference[name] = evaluate(body, reference.copy())

    def checked(name, *args):
        """Evaluate an export independently; every buffer it made is freed once."""
        start = len(buffers)
        value = reference[name]
        for a in args:
            value = value(a)
        assert all(not b.alive for b in buffers[start:]), (name, args, "leak")
        return value

    rng = random.Random(0x5F)
    ns = [0, 1, 2, 3, 7, 100, *(rng.randrange(0, 2000) for _ in range(6))]
    xs = [0, 1, -1, 7, -9, 1 << 40, *(rng.randrange(-(1 << 40), 1 << 40) for _ in range(6))]
    indices = [0, 1, 2, 3, 4, 1 << 63, MAX, *(rng.getrandbits(64) for _ in range(6))]
    formatted = temporary / "buffer-formatted.jh"
    formatted.write_text(command("fmt", example).stdout)
    assert mir == command("emit-mir", formatted, "--lib").stdout
    counter = temporary / "buffer-counter.c"
    counter.write_text(COUNTER)
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            for is_source, suffix in ((True, "jh"), (False, "jhc")):
                obj = temporary / f"buffer-{target}{level}-{suffix}.o"
                options = ["--lib"] if is_source else []
                command("emit-obj", example if is_source else core_example, *options,
                        "--target", target, level, "-o", str(obj), source=is_source)
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                library = temporary / f"buffer{level}-{suffix}.so"
                cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
                run([*cc, "-shared", "-fPIC", str(obj), str(counter), "-o", str(library),
                     "-Wl,--wrap=malloc", "-Wl,--wrap=free"])
                native = ctypes.CDLL(str(library))
                allocations = ctypes.c_long.in_dll(native, "allocations")
                frees = ctypes.c_long.in_dll(native, "frees")
                native.total.argtypes = [ctypes.c_uint64, ctypes.c_int64]
                native.total.restype = ctypes.c_int64
                native.pick.argtypes = [ctypes.c_uint64, ctypes.c_int64]
                native.pick.restype = ctypes.c_int64
                for n in ns:
                    for x in xs[:4]:
                        before = (allocations.value, frees.value)
                        assert native.total(n, x) == checked("total", n, x) == (n + 1) * x, (n, x)
                        assert (allocations.value - before[0], frees.value - before[1]) == (1, 1), n
                for i in indices:
                    for x in xs:
                        before = (allocations.value, frees.value)
                        expected = x + i if i < 3 else -1
                        assert native.pick(i, x) == checked("pick", i, x) == expected, (i, x)
                        made = 1 if i < 3 else 0
                        assert (allocations.value - before[0], frees.value - before[1]) == (made, made), i
    # The valid program's mixed calls also free what they allocate.
    valid_obj = temporary / "buffer-valid.o"
    command("emit-obj", valid_path, "--lib", "-O0", "-o", str(valid_obj))
    library = temporary / "buffer-valid.so"
    cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
    run([*cc, "-shared", "-fPIC", str(valid_obj), str(counter), "-o", str(library),
         "-Wl,--wrap=malloc", "-Wl,--wrap=free"])
    native = ctypes.CDLL(str(library))
    native.calls.argtypes = [ctypes.c_int64, ctypes.c_uint64]
    native.calls.restype = ctypes.c_int64
    allocations = ctypes.c_long.in_dll(native, "allocations")
    frees = ctypes.c_long.in_dll(native, "frees")
    for i in (0, 1, 2, 3, 9):
        native.calls(5, i)
        assert allocations.value == frees.value and allocations.value > 0, i
    native.cancelled.restype = ctypes.c_int64
    before = allocations.value
    assert native.cancelled() == 1
    assert allocations.value == frees.value == before + 1
    print(f"dependent buffers: paired source/core execution, counted allocations, {len(source_invalid)} source and {len(core_invalid)} core rejections passed")
