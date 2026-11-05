"""Proofs by induction over a borrow, called by tests/core.py.

induct into a proposition on a borrow is a proof by induction over the
value the borrow reads, Deref(r), which only types and evidence may
contain; Deref(Borrow(x)) is x and Borrow(Deref(r)) is r.
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
    "false-step": "fn bad(xs: ref List) -> Eq(twice(xs), length(xs)) { induct(fn(t) { Eq(twice(t), length(t)) }, refl(0), fn(x, rest, ih) { transport(fn(k) { Eq(twice(rest) + 2, k + 1) }, ih, refl(twice(rest) + 2)) }, xs) }",
    "no-induction": "fn bad(xs: ref List) -> Eq(twice(xs), length(xs) + length(xs)) { refl(twice(xs)) }",
    "false-base": "fn bad(xs: ref List) -> Eq(twice(xs) + 1, length(xs) + length(xs)) { induct(fn(t) { Eq(twice(t) + 1, length(t) + length(t)) }, refl(0), fn(x, rest, ih) { transport(fn(k) { Eq(twice(rest) + 3, k + 2) }, ih, refl(twice(rest) + 3)) }, xs) }",
    "other-borrow": "fn bad(xs: ref List, ys: ref List) -> Eq(twice(xs), length(ys) + length(ys)) { twice_length(xs) }",
    "unchecked": "fn bad(xs: ref List, b: buffer(9)) -> i64 { at_twice(xs, b, decide_lt(0, 9)) }",
    "hypothesis-as-step": "fn bad(xs: ref List) -> Eq(twice(xs), length(xs) + length(xs)) { induct(fn(t) { Eq(twice(t), length(t) + length(t)) }, refl(0), fn(x, rest, ih) { ih }, xs) }",
}

CORE_INVALID = {
    "runtime-deref": "(def bad (pi xs (Ref List) I64) (lam xs (Ref List) (case List (lam t List I64) (int 0) (lam x I64 (lam rest List (drop List rest x))) (deref xs))))",
    "lend-deref": "(def bad (pi xs List I64) (lam xs List (lend xs (lam r (Ref List) (deref r)) (lam a List (lam y List (drop List y (drop List a (int 0))))))))",
    "deref-owned": "(def bad (pi xs List (pi0 p (Eq (app length (borrow (deref xs))) 0) I64)) (lam xs List (lam0 p (Eq (app length (borrow (deref xs))) 0) (drop List xs (int 0)))))",
    "false-induction": "(def bad (pi xs (Ref List) (Eq (app twice xs) (app length xs))) (lam xs (Ref List) (induct List (lam t List (Eq (app twice (borrow t)) (app length (borrow t)))) (refl 0) (lam x I64 (lam0 rest List (lam0 ih (Eq (app twice (borrow rest)) (app length (borrow rest))) (transport (lam k U64 (Eq (uadd (app twice (borrow rest)) 2) (uadd k 1))) ih (refl (uadd (app twice (borrow rest)) 2)))))) (deref xs))))",
    "wrong-borrow": "(def bad (pi xs (Ref List) (pi ys (Ref List) (Eq (app twice xs) (uadd (app length ys) (app length ys))))) (lam xs (Ref List) (lam ys (Ref List) (app twice_length xs))))",
}


def validate_borrow_induct(compiler, root, temporary, environment, run, definitions, evaluate,
                           buffers, nodes):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    def counted(obj, name):
        """A shared library of obj whose malloc and free are counted."""
        counter = temporary / "borrow-induct-counter.c"
        counter.write_text(COUNTER)
        library = temporary / f"{name}.so"
        cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
        run([*cc, "-shared", "-fPIC", str(obj), str(counter), "-o", str(library),
             "-Wl,--wrap=malloc", "-Wl,--wrap=free"])
        native = ctypes.CDLL(str(library))
        return native, ctypes.c_long.in_dll(native, "allocations"), ctypes.c_long.in_dll(native, "frees")

    example = root / "examples/core_borrow_induct.jh"
    core_example = root / "examples/core_borrow_induct.jhc"
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
    # The induction is erased: the only recursions left are size's length
    # and at_twice's twice, and the load at twice(xs) has no bounds check.
    assert mir.count("fn recursion.") == 2, mir
    checks = [line for line in mir.splitlines() if "assert" in line or "panic" in line]
    assert checks and all('"allocation failed"' in line for line in checks), mir
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 9 and not result.stdout and not result.stderr

    for name, body in SOURCE_INVALID.items():
        path = temporary / f"borrow-induct-{name}.jh"
        path.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert str(path) in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"borrow-induct-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False)
        assert not obj.exists()

    for name, body in CORE_INVALID.items():
        path = temporary / f"borrow-induct-{name}.jhc"
        path.write_text(core_prefix + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert "core:" in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"borrow-induct-{name}.o"
        command("emit-obj", path, "-o", str(obj), source=False, success=False)
        assert not obj.exists(), name

    # More valid programs: induction over a borrowed tree's fields, a
    # lemma used on an owned list through a borrow in its type, and one
    # used on the borrow a lend makes.
    valid = prefix + """
enum Tree {
    Leaf(i64)
    Node(Tree, Tree)
}
fn leaves(t: ref Tree) -> u64 { induct(fn(u) { u64 }, fn(x) { 1 }, fn(l, r, a, b) { a + b }, t) }
fn nodes(t: ref Tree) -> u64 { induct(fn(u) { u64 }, fn(x) { 0 }, fn(l, r, a, b) { a + b + 1 }, t) }
fn more_leaves(t: ref Tree) -> Eq(leaves(t), nodes(t) + 1) {
    induct(fn(u) { Eq(leaves(u), nodes(u) + 1) }, fn(x) { refl(1) }, fn(l, r, a, b) {
        transport(fn(k) { Eq(leaves(l) + leaves(r), nodes(l) + 1 + k) }, b,
            transport(fn(k) { Eq(leaves(l) + leaves(r), k + leaves(r)) }, a,
                refl(leaves(l) + leaves(r))))
    }, t)
}
fn owned(xs: List) -> Eq(twice(xs), length(xs) + length(xs)) { twice_length(xs) }
fn read(t: ref Tree, b: buffer(9), p: erased(Lt(nodes(t) + 1, 9))) -> i64 {
    load(b, leaves(t), transport(fn(k) { Lt(k, 9) },
        transport(fn(k) { Eq(k, leaves(t)) }, more_leaves(t), refl(leaves(t))), p), fn(v, b) { v })
}
fn grow(x: i64) -> Tree { Tree.Node(Tree.Leaf(x), Tree.Node(Tree.Leaf(x), Tree.Leaf(x))) }
fn shape(t: ref Tree) -> refine(fn(k) { Eq(k, nodes(t)) }) { pack(nodes(t), refl(nodes(t))) }
export fn more(x: i64) -> i64 {
    let t = grow(x)
    let k = shape(t)
    if_lt(witness(k) + 1, 9, fn(q) {
        read(t, store(alloc(9, 0), 3, x, decide_lt(3, 9)), transport(fn(m) { Lt(m + 1, 9) }, proof(k), q))
    }, -1)
}
"""
    valid_path = temporary / "borrow-induct-valid.jh"
    valid_path.write_text(valid)
    command("check", valid_path, "--lib")
    obj = temporary / "borrow-induct-valid.o"
    command("emit-obj", valid_path, "--lib", "-O0", "-o", str(obj))
    native, allocations, frees = counted(obj, "borrow-induct-valid")
    native.more.argtypes = [ctypes.c_int64]
    native.more.restype = ctypes.c_int64
    for x in (0, 5, -3, 1 << 40):
        # Three leaves: the buffer is read at 3.
        assert native.more(x) == x, x
        assert allocations.value == frees.value, x

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

    rng = random.Random(0x68)
    ns = [0, 1, 2, 3, 4, 5, 9, *(rng.randrange(0, 200) for _ in range(2))]
    xs = [0, 1, -1, 5, *(rng.randrange(-(1 << 40), 1 << 40) for _ in range(2))]
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            for is_source, suffix in ((True, "jh"), (False, "jhc")):
                obj = temporary / f"borrow-induct-{target}{level}-{suffix}.o"
                options = ["--lib"] if is_source else []
                command("emit-obj", example if is_source else core_example, *options,
                        "--target", target, level, "-o", str(obj), source=is_source)
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                native, allocations, frees = counted(obj, f"borrow-induct{level}-{suffix}")
                native.demo.argtypes = [ctypes.c_uint64, ctypes.c_int64]
                native.demo.restype = ctypes.c_int64
                for n in ns:
                    for x in xs:
                        before = allocations.value
                        expected = -1 if 2 * n >= 9 else x if n == 2 else 0
                        assert native.demo(n, x) == checked("demo", n, x) == expected, (n, x)
                        # n + 1 nodes, and the buffer when the lengths fit.
                        made = allocations.value - before
                        assert made == n + 1 + (2 * n < 9) or level == "-O2", (n, x, made)
                        assert allocations.value == frees.value
    print(f"dependent induction over borrows: paired source/core execution, counted frees, {len(SOURCE_INVALID)} source and {len(CORE_INVALID)} core rejections passed")
