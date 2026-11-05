"""Borrows of owned values, called by tests/core.py.

A `ref T` parameter reads a buffer or heap data without consuming it. The
source elaborator lends an owned local where a borrow is expected, for the
expression or `let` value that borrows it; the kernel checks that no
borrow outlives its lend and that the owner is not consumed meanwhile.
"""
import ctypes
import json
import os
import platform
import random
import re
import shlex
import struct

from core_buffer import COUNTER

SOURCE_INVALID = {
    "borrow-and-consume": "fn bad(xs: List) -> i64 { total(xs) + sum(xs) }",
    "consume-and-borrow": "fn bad(xs: List) -> i64 { sum(xs) + total(xs) }",
    "after-move": "fn bad(xs: List) -> i64 {\n    let s = sum(xs)\n    total(xs) + s\n}",
    "escape": "fn bad(xs: List) -> i64 {\n    let r: ref List = xs\n    0\n}",
    "borrowed-result": "fn keep(xs: ref List) -> ref List { xs }",
    "consume-borrow": "fn bad(xs: ref List) -> i64 { sum(xs) }",
    "free-borrow": "fn bad(xs: ref List) -> i64 { free(xs, 0) }",
    "consume-field": "fn bad(xs: ref List) -> i64 { match xs { Nil => 0, Cons(x, rest) => sum(rest) } }",
    "store-borrow": "fn bad(b: ref buffer(3)) -> buffer(3) { store(b, 0, 1, decide_lt(0, 3)) }",
    "load-borrow": "fn bad(b: ref buffer(3)) -> i64 { load(b, 0, decide_lt(0, 3), fn(x, c) { x }) }",
    "unchecked-index": "fn bad(b: ref buffer(3), i: u64) -> i64 { index(b, i, decide_lt(0, 3)) }",
    "two-owners": "fn both(a: ref List, b: ref List) -> i64 { 0 }\nfn bad(xs: List, ys: List) -> i64 { both(xs, ys) }",
    "temporary": "fn bad() -> u64 { length(repeat(2, 1)) }",
    "export-borrow": "export fn bad(xs: ref List) -> i64 { 0 }",
    "scalar-borrow": "fn bad(x: ref u64) -> u64 { 0 }",
    "flat-borrow": "enum Two {\n    A\n}\nfn bad(t: ref Two) -> i64 { 0 }",
    "data-field": "enum Holder {\n    Has(ref List)\n}",
    "inout": "fn bad(xs: inout List) -> i64 { 0 }",
    "recursion-capture": "fn bad(xs: ref List, ys: List) -> i64 { induct(fn(t) { i64 }, sum(ys), fn(x, rest, ih) { ih + sum(ys) }, xs) }",
    "dependent-result": "fn bad(xs: ref List) -> i64 { induct(fn(t) { Eq(0, 0) }, refl(0), fn(x, rest, ih) { ih }, xs) }",
    "let-pattern": "fn bad(xs: List) -> i64 {\n    var s = total(xs)\n    s + sum(xs)\n}",
}

CORE_INVALID = {
    "lend-escape": "(def bad (pi xs List I64) (lam xs List (lend xs (lam r (Ref List) r) (lam a (Ref List) (lam xs List (drop List xs (int 0)))))))",
    "lend-function": "(def bad (pi xs List I64) (lam xs List (lend xs (lam r (Ref List) (lam y I64 y)) (lam a (pi y I64 I64) (lam xs List (drop List xs (app a (int 0))))))))",
    "lend-scalar": "(def bad (pi x I64 I64) (lam x I64 (lend x (lam r (Ref List) (int 0)) (lam a I64 (lam y I64 a)))))",
    "lend-other": "(def bad (pi xs List I64) (lam xs List (lend xs (lam r (Ref (Buffer 1)) (int 0)) (lam a I64 (lam xs List (drop List xs a))))))",
    "lend-and-use": "(def bad (pi xs List I64) (lam xs List (lend xs (lam r (Ref List) (app sum xs)) (lam a I64 (lam ys List (drop List ys a))))))",
    "lend-leak": "(def bad (pi xs List I64) (lam xs List (lend xs (lam r (Ref List) (int 0)) (lam a I64 (lam xs List a)))))",
    "lend-result-type": "(def bad (pi xs List I64) (lam xs List (lend xs (lam r (Ref List) (int 0)) (lam a U64 (lam xs List (drop List xs (int 0)))))))",
    "lend-proof": "(def bad (pi xs List I64) (lam xs List (lend xs (lam r (Ref List) (refl 0)) (lam a (Eq 0 0) (lam xs List (drop List xs (int 0)))))))",
    "view-owned": "(def bad (pi xs List I64) (lam xs List (view List I64 (int 0) (lam x I64 (lam rest (Ref List) x)) xs)))",
    "view-free-field": "(def bad (pi xs (Ref List) I64) (lam xs (Ref List) (view List I64 (int 0) (lam x I64 (lam rest (Ref List) (drop List rest x))) xs)))",
    "view-owned-field": "(def bad (pi xs (Ref List) I64) (lam xs (Ref List) (view List I64 (int 0) (lam x I64 (lam rest List (drop List rest x))) xs)))",
    "view-missing-result": "(def bad (pi xs (Ref List) I64) (lam xs (Ref List) (view-rec List I64 (int 0) (lam x I64 (lam rest (Ref List) x)) xs)))",
    "view-flat": "(data Two (A Two) (B Two))\n(def bad (pi t (Ref Two) I64) (lam t (Ref Two) (int 0)))",
    "ref-scalar": "(def bad (pi x (Ref U64) I64) (lam x (Ref U64) (int 0)))",
    "view-type": "(def bad (pi xs (Ref List) I64) (lam xs (Ref List) (view List (Type 0) I64 (lam x I64 (lam rest (Ref List) I64)) xs)))",
}


# Whole programs the kernel must reject: a type variable standing for a
# borrow or an owned type, and continuations returning closures that hold
# the owned values they were given (found by an independent review).
UNSOUND = {
    "escape": '(def escape\n  (pi A (Type 0) (pi x (Buffer 1) (pi f (pi r (Ref (Buffer 1)) A) A)))\n  (lam A (Type 0) (lam x (Buffer 1) (lam f (pi r (Ref (Buffer 1)) A)\n    (lend x f (lam a A (lam y (Buffer 1) (free y a))))))))\n(def dangling (Ref (Buffer 1))\n  (app escape (Ref (Buffer 1)) (alloc 1 (int 7)) (lam r (Ref (Buffer 1)) r)))\n(export bad I64 (index dangling 0 (decide-lt 0 1)))\n',
    "closure": '(def twice (pi h (pi z U64 U64) U64) (lam h (pi z U64 U64) (uadd (app h 0) (app h 0))))\n(export bad U64\n  (app twice (lend (alloc 1 (int 7)) (lam r (Ref (Buffer 1)) 0)\n    (lam a U64 (lam y (Buffer 1) (lam z U64 (free y 0)))))))\n',
    "load": '(def twice (pi h (pi z U64 U64) U64) (lam h (pi z U64 U64) (uadd (app h 0) (app h 0))))\n(export bad U64\n  (app twice (load (alloc 1 (int 7)) 0 (decide-lt 0 1) (lam x I64 (lam b (Buffer 1) (lam z U64 (free b 0)))))))\n',
    "case": '(data List (Nil List) (Cons (pi x I64 (pi xs List List))))\n(def twice (pi h (pi z U64 U64) U64) (lam h (pi z U64 U64) (uadd (app h 0) (app h 0))))\n(def drop (pi xs List U64) (lam xs List (induct List (lam t List U64) 0 (lam x I64 (lam0 rest List (lam ih U64 ih))) xs)))\n(export bad U64\n  (app twice (case List (lam t List (pi z U64 U64)) (lam z U64 z)\n    (lam x I64 (lam rest List (lam z U64 (app drop rest)))) (Cons (int 1) Nil))))\n',
    "dup": '(def dup (pi A (Type 0) (pi x A (pi f (pi a A (pi b A I64)) I64)))\n  (lam A (Type 0) (lam x A (lam f (pi a A (pi b A I64)) (app f x x)))))\n(export bad I64 (app dup (Buffer 1) (alloc 1 (int 0)) (lam a (Buffer 1) (lam b (Buffer 1) (free a (free b (int 0)))))))\n',
}

POLYMORPHIC = "(def id (pi A (Type 0) (pi x A A)) (lam A (Type 0) (lam x A x)))\n(export good I64 (app id I64 (int 3)))\n"


def validate_borrow(compiler, root, temporary, environment, run, definitions, evaluate, buffers, nodes):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    def counted(obj, name):
        """A shared library of obj whose malloc and free are counted."""
        counter = temporary / "borrow-counter.c"
        counter.write_text(COUNTER)
        library = temporary / f"{name}.so"
        cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
        run([*cc, "-shared", "-fPIC", str(obj), str(counter), "-o", str(library),
             "-Wl,--wrap=malloc", "-Wl,--wrap=free"])
        native = ctypes.CDLL(str(library))
        return native, ctypes.c_long.in_dll(native, "allocations"), ctypes.c_long.in_dll(native, "frees")

    example = root / "examples/core_borrow.jh"
    core_example = root / "examples/core_borrow.jhc"
    source_text = example.read_text()
    core_text = core_example.read_text()
    prefix = source_text.split("export fn stats")[0]
    core_prefix = core_text.split("(export stats")[0]
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable",
                   "JIHOO_LD": "/unavailable"}
    command("check", example, env=unavailable)
    command("check", core_example, source=False, env=unavailable)
    mir = command("emit-mir", example, "--lib").stdout
    assert mir == command("emit-mir", core_example, source=False).stdout
    # A recursion over a borrow frees nothing: of the three recursions,
    # only sum's, which consumes its list, calls free.
    bodies = {name: mir.split(f"fn {name} ")[1].split("\nfn ")[0]
              for name in re.findall(r"fn (recursion\.\d+) ", mir)}
    assert len(bodies) == 3, mir
    assert sum("call free(" in body for body in bodies.values()) == 1, mir
    assert mir.count("fn drop.List ") == 1, mir
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 59 and not result.stdout and not result.stderr

    for name, body in SOURCE_INVALID.items():
        path = temporary / f"borrow-{name}.jh"
        path.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert str(path) in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"borrow-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False)
        assert not obj.exists()

    for name, body in CORE_INVALID.items():
        path = temporary / f"borrow-{name}.jhc"
        path.write_text(core_prefix + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert "core:" in diagnostic.stderr, (name, diagnostic.stderr)

    for name, text in UNSOUND.items():
        path = temporary / f"borrow-unsound-{name}.jhc"
        path.write_text(text)
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        obj = temporary / f"borrow-unsound-{name}.o"
        command("emit-obj", path, "-o", str(obj), source=False, success=False)
        assert not obj.exists(), name
    polymorphic = temporary / "borrow-polymorphic.jhc"
    polymorphic.write_text(POLYMORPHIC)
    command("check", polymorphic, source=False)

    # More valid programs: lets, a borrow in one branch, a borrow inside a
    # match arm, a tree read twice, and a let without borrows.
    valid = prefix + """
enum Tree {
    Leaf(i64)
    Node(Tree, List, Tree)
}
fn leaves(t: ref Tree) -> i64 { induct(fn(u) { i64 }, fn(x) { x }, fn(l, m, r, a, b) { a + total(m) + b }, t) }
fn left_or(t: ref Tree, missing: i64) -> i64 { match t { Leaf(x) => missing, Node(l, m, r) => leaves(l) } }
fn grow(x: i64) -> Tree { Tree.Node(Tree.Leaf(x), repeat(2, 1), Tree.Node(Tree.Leaf(3), List.Nil, Tree.Leaf(4))) }
fn branch(i: u64, xs: List) -> i64 { if_lt(i, 5, fn(p) { total(xs) }, sum(xs)) }
fn arm(t: Tree) -> i64 {
    match t {
        Leaf(x) => x
        Node(l, m, r) => {
            let n = total(m)
            n + sum(m)
        }
    }
}
export fn trees(x: i64, i: u64) -> i64 {
    let t = grow(x)
    let a = leaves(t)
    let b = left_or(t, 0)
    let plain = a + b
    plain + arm(t) + branch(i, repeat(3, x))
}
"""
    valid_path = temporary / "borrow-valid.jh"
    valid_path.write_text(valid)
    command("check", valid_path, "--lib")
    obj = temporary / "borrow-valid.o"
    command("emit-obj", valid_path, "--lib", "-O0", "-o", str(obj))
    native, allocations, frees = counted(obj, "borrow-valid")
    native.trees.argtypes = [ctypes.c_int64, ctypes.c_uint64]
    native.trees.restype = ctypes.c_int64
    for x in (0, 5, -3):
        for i in (0, 4, 5, 9):
            # leaves: x + 2 + 3 + 4; left_or: x; arm: total and sum of m;
            # branch: total or sum of three x's alike.
            assert native.trees(x, i) == (x + 9) + x + 4 + 3 * x, (x, i)
            assert allocations.value == frees.value, (x, i)

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

    rng = random.Random(0x65)
    ns = [0, 1, 2, 3, 9, *(rng.randrange(0, 200) for _ in range(4))]
    xs = [0, 1, -1, 5, *(rng.randrange(-(1 << 40), 1 << 40) for _ in range(2))]
    indices = [0, 1, 2, 3, (1 << 64) - 1]
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            for is_source, suffix in ((True, "jh"), (False, "jhc")):
                obj = temporary / f"borrow-{target}{level}-{suffix}.o"
                options = ["--lib"] if is_source else []
                command("emit-obj", example if is_source else core_example, *options,
                        "--target", target, level, "-o", str(obj), source=is_source)
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                native, allocations, frees = counted(obj, f"borrow{level}-{suffix}")
                native.stats.argtypes = [ctypes.c_uint64, ctypes.c_int64]
                native.stats.restype = ctypes.c_int64
                native.count.argtypes = [ctypes.c_uint64]
                native.count.restype = ctypes.c_uint64
                native.pick.argtypes = [ctypes.c_uint64, ctypes.c_int64]
                native.pick.restype = ctypes.c_int64
                for n in ns:
                    for x in xs[:4]:
                        before = allocations.value
                        expected = 2 * n * x + (x if n > 1 else -1)
                        assert native.stats(n, x) == checked("stats", n, x) == expected, (n, x)
                        # One list of n + 1 nodes, read twice, then consumed.
                        assert allocations.value - before == n + 1
                        assert allocations.value == frees.value
                    assert native.count(n) == checked("count", n) == n
                    assert allocations.value == frees.value
                for i in indices:
                    for x in xs:
                        expected = ([x, x, 40][i] if i < 3 else -1) + x
                        assert native.pick(i, x) == checked("pick", i, x) == expected, (i, x)
                        assert allocations.value == frees.value
    print(f"dependent borrows: paired source/core execution, borrowed recursion, counted frees, {len(SOURCE_INVALID)} source, {len(CORE_INVALID)} core and {len(UNSOUND)} soundness rejections passed")
