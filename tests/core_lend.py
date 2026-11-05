"""Dependent lends, called by tests/core.py.

When a lend lends a variable, the kernel checks its reader with the
borrow equal to Borrow(owner) and its continuation with the owner given
back equal to the owner itself. So evidence about an owner holds of its
borrow and after the lend, and a borrowing call's result type may
mention the owner. The owner is then used exactly once, after its lend.
"""
import ctypes
import json
import os
import platform
import random
import shlex
import struct

from core_buffer import COUNTER

SOURCE_INVALID = {
    "other-owner": "fn bad(xs: List, ys: List, b: buffer(4), p: erased(Lt(length(ys), 4))) -> i64 { slot(xs, b, p) }",
    "unchecked": "fn bad(xs: List, b: buffer(4)) -> i64 { slot(xs, b, decide_lt(0, 4)) }",
    "other-size": "fn bad(xs: List, b: buffer(4)) -> i64 {\n    let ys = repeat(1, 0)\n    let k = size(ys)\n    if_lt(witness(k), 4, fn(q) { slot(xs, b, transport(fn(m) { Lt(m, 4) }, proof(k), q)) }, -1)\n}",
    "false-size": "fn bad(xs: ref List) -> refine(fn(k) { Eq(k, length(xs)) }) { pack(0, refl(0)) }",
    "after-move": "fn bad(xs: List, b: buffer(4), p: erased(Lt(length(xs), 4))) -> u64 {\n    let v = slot_owned(xs, b, p)\n    witness(size(xs))\n}",
    "stale-bound": "fn bad(n: u64, b: buffer(4)) -> i64 {\n    let xs = repeat(n, 1)\n    let k = size(xs)\n    let ys = repeat(n + 1, 1)\n    if_lt(witness(k), 4, fn(q) { slot(ys, b, transport(fn(m) { Lt(m, 4) }, proof(k), q)) }, -1)\n}",
}

CORE_INVALID = {
    "use-in-reader": "(def bad (pi xs List I64) (lam xs List (lend xs (lam r (Ref List) (drop List xs (int 0))) (lam a I64 (lam y List (drop List y a))))))",
    "unused-after": "(def bad (pi xs List I64) (lam xs List (lend xs (lam r (Ref List) (int 0)) (lam a I64 (lam y List a)))))",
    "both-names": "(def bad (pi xs List I64) (lam xs List (lend xs (lam r (Ref List) (int 0)) (lam a I64 (lam y List (drop List y (drop List xs a)))))))",
    "borrow-after": "(def bad (pi xs List U64) (lam xs List (lend xs (lam r (Ref List) 0) (lam a U64 (lam y List (drop List y (app length (borrow xs))))))))",
    "borrow-other": "(def bad (pi xs List (pi ys List U64)) (lam xs List (lam ys List (lend xs (lam r (Ref List) (app length (borrow ys))) (lam a U64 (lam y List (drop List y (drop List ys a))))))))",
    "borrow-escape": "(def bad (pi xs List U64) (lam xs List (lend xs (lam r (Ref List) (borrow xs)) (lam a (Ref List) (lam y List (drop List y 0))))))",
    "consume-before": "(def bad (pi xs List U64) (lam xs List (drop List xs (lend xs (lam r (Ref List) (app length r)) (lam a U64 (lam y List (drop List y a)))))))",
    "nested-free": "(def bad (pi xs List U64) (lam xs List (lend xs (lam r (Ref List) (lend xs (lam s (Ref List) (app length s)) (lam a U64 (lam z List (drop List z a))))) (lam a U64 (lam y List (drop List y a))))))",
    "false-reader": "(def bad (pi xs List (pi ys List (pi b (Buffer 4) (pi0 p (Lt (app length (borrow ys)) 4) I64)))) (lam xs List (lam ys List (lam b (Buffer 4) (lam0 p (Lt (app length (borrow ys)) 4) (lend xs (lam r (Ref List) (app slot r b p)) (lam a I64 (lam y List (drop List y (drop List ys a))))))))))",
    "closure": "(def twice (pi h (pi z U64 U64) U64) (lam h (pi z U64 U64) (uadd (app h 0) (app h 0))))\n(def bad (pi xs List U64) (lam xs List (app twice (lend xs (lam r (Ref List) 0) (lam a U64 (lam y List (lam z U64 (drop List xs 0))))))))",
}


def validate_lend(compiler, root, temporary, environment, run, definitions, evaluate, buffers,
                  nodes):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    def counted(obj, name):
        """A shared library of obj whose malloc and free are counted."""
        counter = temporary / "lend-counter.c"
        counter.write_text(COUNTER)
        library = temporary / f"{name}.so"
        cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
        run([*cc, "-shared", "-fPIC", str(obj), str(counter), "-o", str(library),
             "-Wl,--wrap=malloc", "-Wl,--wrap=free"])
        native = ctypes.CDLL(str(library))
        return native, ctypes.c_long.in_dll(native, "allocations"), ctypes.c_long.in_dll(native, "frees")

    example = root / "examples/core_lend.jh"
    core_example = root / "examples/core_lend.jhc"
    source_text = example.read_text()
    core_text = core_example.read_text()
    prefix = source_text.split("export fn demo")[0]
    core_prefix = core_text.split("(export demo")[0]
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable",
                   "JIHOO_LD": "/unavailable"}
    command("check", example, env=unavailable)
    command("check", core_example, source=False, env=unavailable)
    mir = command("emit-mir", example, "--lib").stdout
    assert mir == command("emit-mir", core_example, source=False).stdout
    # The load at the list's length has no bounds check: the evidence is
    # erased, and only the allocation checks remain.
    checks = [line for line in mir.splitlines() if "assert" in line or "panic" in line]
    assert checks and all('"allocation failed"' in line for line in checks), mir
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 10 and not result.stdout and not result.stderr

    for name, body in SOURCE_INVALID.items():
        path = temporary / f"lend-{name}.jh"
        path.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert str(path) in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"lend-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False)
        assert not obj.exists()

    for name, body in CORE_INVALID.items():
        path = temporary / f"lend-{name}.jhc"
        path.write_text(core_prefix + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert "core:" in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"lend-{name}.o"
        command("emit-obj", path, "-o", str(obj), source=False, success=False)
        assert not obj.exists(), name

    # More valid programs: a fact about an owner kept across several lets
    # that lend it, and in .jhc, the owner borrowed by name in the reader.
    valid = prefix + """
fn total(xs: ref List) -> i64 { induct(fn(t) { i64 }, 0, fn(x, rest, ih) { x + ih }, xs) }
fn twice(n: u64, x: i64) -> i64 {
    let xs = repeat(n, x)
    let k = size(xs)
    let s = total(xs)
    let again = size(xs)
    if_lt(witness(k), 4, fn(q) {
        let v = slot(xs, alloc(4, s), transport(fn(m) { Lt(m, 4) }, proof(k), q))
        v + total(xs)
    }, -1)
}
export fn more(n: u64, x: i64) -> i64 { twice(n, x) }
"""
    valid_path = temporary / "lend-valid.jh"
    valid_path.write_text(valid)
    command("check", valid_path, "--lib")
    obj = temporary / "lend-valid.o"
    command("emit-obj", valid_path, "--lib", "-O0", "-o", str(obj))
    native, allocations, frees = counted(obj, "lend-valid")
    native.more.argtypes = [ctypes.c_uint64, ctypes.c_int64]
    native.more.restype = ctypes.c_int64
    for n in (0, 1, 3, 4, 7):
        for x in (0, 5, -3):
            expected = (n * x + n * x) if n < 4 else -1
            assert native.more(n, x) == expected, (n, x)
            assert allocations.value == frees.value, (n, x)

    # A reader that borrows its owner by name, inlined where the owner is
    # a temporary: lowering keeps the owner bound once.
    written = core_prefix + """
(def reader (pi xs List U64) (lam xs List
  (lend xs (lam r (Ref List) (uadd (app length r) (app length (borrow xs))))
    (lam a U64 (lam y List (drop List y a))))))
(export read (pi n U64 U64) (lam n U64 (app reader (app repeat n (int 1)))))
(export more (pi n U64 U64) (lam n U64 (app reader (Cons (int 1) (app repeat n (int 1))))))
"""
    written_path = temporary / "lend-written.jhc"
    written_path.write_text(written)
    for level in ("-O0", "-O2"):
        obj = temporary / f"lend-written{level}.o"
        command("emit-obj", written_path, level, "-o", str(obj), source=False)
        native, allocations, frees = counted(obj, f"lend-written{level}")
        for name, extra in (("read", 0), ("more", 1)):
            function = getattr(native, name)
            function.argtypes = [ctypes.c_uint64]
            function.restype = ctypes.c_uint64
            for n in (0, 1, 5):
                assert function(n) == 2 * (n + extra), (name, n)
                assert allocations.value == frees.value

    reference = {}
    for _, name, _, body in definitions(core_text):
        reference[name] = evaluate(body, reference.copy())

    def checked(name, *args):
        """Evaluate an export independently; every buffer and node is freed once."""
        start_buffers, start_nodes = len(buffers), len(nodes)
        value = reference[name]
        for a in args:
            value = value(a)
        assert all(not b.alive for b in buffers[start_buffers:]), (name, args, "buffer leak")
        assert all(not n.alive for n in nodes[start_nodes:]), (name, args, "node leak")
        return value

    rng = random.Random(0x67)
    ns = [0, 1, 2, 3, 4, 9, *(rng.randrange(0, 200) for _ in range(2))]
    xs = [0, 1, -1, 5, *(rng.randrange(-(1 << 40), 1 << 40) for _ in range(2))]
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            for is_source, suffix in ((True, "jh"), (False, "jhc")):
                obj = temporary / f"lend-{target}{level}-{suffix}.o"
                options = ["--lib"] if is_source else []
                command("emit-obj", example if is_source else core_example, *options,
                        "--target", target, level, "-o", str(obj), source=is_source)
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                native, allocations, frees = counted(obj, f"lend{level}-{suffix}")
                native.demo.argtypes = [ctypes.c_uint64, ctypes.c_int64]
                native.demo.restype = ctypes.c_int64
                native.first.argtypes = [ctypes.c_int64]
                native.first.restype = ctypes.c_int64
                for n in ns:
                    for x in xs:
                        before = allocations.value
                        expected = -1 if n >= 4 else x if n == 2 else 0
                        assert native.demo(n, x) == checked("demo", n, x) == expected, (n, x)
                        # n + 1 nodes, and the buffer when the length fits.
                        made = allocations.value - before
                        assert made == n + 1 + (n < 4) or level == "-O2", (n, x, made)
                        assert allocations.value == frees.value
                for x in xs:
                    assert native.first(x) == checked("first", x) == x
                    assert allocations.value == frees.value
    print(f"dependent lends: paired source/core execution, counted frees, {len(SOURCE_INVALID)} source and {len(CORE_INVALID)} core rejections passed")
