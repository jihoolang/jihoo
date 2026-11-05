"""Recursive data on the heap and structural recursion, called by tests/core.py."""
import ctypes
import json
import os
import platform
import random
import re
import shlex
import struct

from core_buffer import COUNTER

MAX = (1 << 64) - 1
IMAX = (1 << 63) - 1


def validate_list(compiler, root, temporary, environment, run, definitions, evaluate, nodes):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    def counted(obj, name):
        """A shared library of obj whose malloc and free are counted."""
        counter = temporary / "list-counter.c"
        counter.write_text(COUNTER)
        library = temporary / f"{name}.so"
        cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
        run([*cc, "-shared", "-fPIC", str(obj), str(counter), "-o", str(library),
             "-Wl,--wrap=malloc", "-Wl,--wrap=free"])
        native = ctypes.CDLL(str(library))
        return native, ctypes.c_long.in_dll(native, "allocations"), ctypes.c_long.in_dll(native, "frees")

    example = root / "examples/core_list.jh"
    core_example = root / "examples/core_list.jhc"
    source_text = example.read_text()
    core_text = core_example.read_text()
    prefix = source_text.split("export fn total")[0]
    core_prefix = core_text.split("(export total")[0]
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable",
                   "JIHOO_LD": "/unavailable"}
    command("check", example, env=unavailable)
    command("check", core_example, source=False, env=unavailable)
    mir = command("emit-mir", example, "--lib").stdout
    assert mir == command("emit-mir", core_example, source=False).stdout
    # Three exports, malloc and free, and one recursive function per
    # recursion that runs: sum, doubled and length, and the drop in head_or.
    assert mir.count("fn ") == 9 and mir.count("fn recursion.") == 4, mir
    for name in re.findall(r"fn (recursion\.\d+) ", mir):
        assert re.search(rf"call {re.escape(name)}\(", mir.split(f"fn {name} ")[1].split("\nfn ")[0]), name
    assert mir.count("assert ") == mir.count('"allocation failed"'), mir
    for absent in ("Lt", "closure", "List"):
        assert absent not in mir, (absent, mir)
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 38 and not result.stdout and not result.stderr

    # Arithmetic traps inside a recursion; a list built from literals is
    # built once and consumed.
    trap = temporary / "list-trap.jh"
    trap.write_text(prefix + f"fn main() -> i64 {{ sum(doubled(repeat(1, {IMAX}))) }}\n")
    for level in ("-O0", "-O2"):
        assert command("run", trap, level, success=False).returncode == 132, level
    literal = temporary / "list-literal.jh"
    literal.write_text(prefix + "fn main() -> i64 { sum(List.Cons(1, List.Cons(2, List.Nil))) + head_or(List.Cons(4, List.Nil), 0) }\n")
    for level in ("-O0", "-O2"):
        assert command("run", literal, level, success=False).returncode == 7, level

    valid = prefix + """
fn tail(xs: List) -> List {
    match xs {
        Nil => List.Nil
        Cons(x, rest) => rest
    }
}
enum Tree {
    Leaf(i64)
    Node(Tree, Tree)
}
fn tree_sum(t: Tree) -> i64 { induct(fn(u) { i64 }, fn(x) { x }, fn(l, r, a, b) { a + b }, t) }
fn leaves(t: Tree) -> u64 { induct(fn(u) { u64 }, fn(x) { 1 }, fn(l, r, a, b) { a + b }, t) }
fn mirror(t: Tree) -> Tree { induct(fn(u) { Tree }, fn(x) { Tree.Leaf(x) }, fn(l, r, a, b) { Tree.Node(b, a) }, t) }
// Sums of variables are compared in canonical order, so this is refl.
fn comm(x: u64, y: u64) -> Eq(x + y, y + x) { refl(x + y) }
fn mirror_leaves(t: Tree) -> Eq(leaves(mirror(t)), leaves(t)) {
    induct(fn(u) { Eq(leaves(mirror(u)), leaves(u)) }, fn(x) { refl(1) }, fn(l, r, a, b) {
        transport(fn(k) { Eq(leaves(mirror(r)) + leaves(mirror(l)), k) }, comm(leaves(r), leaves(l)),
            transport(fn(k) { Eq(leaves(mirror(r)) + leaves(mirror(l)), leaves(r) + k) }, a,
                transport(fn(k) { Eq(leaves(mirror(r)) + leaves(mirror(l)), k + leaves(mirror(l))) }, b,
                    refl(leaves(mirror(r)) + leaves(mirror(l))))))
    }, t)
}
// A list of indices proved below n, read from a table of length n.
enum Indices(n: u64) {
    None
    More(refine(fn(j) { Lt(j, n) }), Indices(n))
}
fn gather(n: erased(u64), xs: [i64; n], is: Indices(n)) -> i64 {
    induct(fn(t) { i64 }, 0, fn(j, rest, ih) { index(xs, witness(j), proof(j)) + ih }, is)
}
fn indices(i: u64) -> Indices(4) {
    if_lt(i, 4, fn(p) { Indices.More(pack(i, p), Indices.More(pack(0, decide_lt(0, 4)), Indices.None)) }, Indices.None)
}
fn length_tail(xs: List) -> Lt(length(tail(xs)), length(xs) + 1) {
    induct(fn(t) { Lt(length(tail(t)), length(t) + 1) }, decide_lt(0, 1), fn(x, rest, ih) { lt_add(0, 2, length(rest), decide_lt(0, 2)) }, xs)
}
export fn trees(x: i64) -> i64 { tree_sum(mirror(Tree.Node(Tree.Leaf(x), Tree.Node(Tree.Leaf(1), Tree.Leaf(2))))) }
export fn mixed(n: u64, x: i64, i: u64) -> i64 {
    sum(tail(repeat(n, x))) + gather(4, [10, 20, 30, 40], indices(i)) + head_or(tail(tail(repeat(n, 3))), 0)
}
"""
    valid_path = temporary / "list-valid.jh"
    valid_path.write_text(valid)
    command("check", valid_path, "--lib")

    source_invalid = {
        "leak-tail": "fn bad(xs: List) -> i64 { match xs { Nil => 0, Cons(x, rest) => x } }",
        "used-twice": "fn bad(xs: List) -> i64 { sum(xs) + sum(xs) }",
        "rest-at-runtime": "fn bad(xs: List) -> i64 { induct(fn(t) { i64 }, 0, fn(x, rest, ih) { sum(rest) }, xs) }",
        "recursion-capture": "fn bad(xs: List, ys: List) -> i64 { induct(fn(t) { i64 }, sum(ys), fn(x, rest, ih) { ih + drop(ys) }, xs) }",
        "unequal-arms": "fn bad(xs: List, ys: List) -> i64 { match xs { Nil => sum(ys), Cons(x, rest) => x + drop(rest) } }",
        "unused-result": "fn bad(xs: List) -> List { induct(fn(t) { List }, List.Nil, fn(x, rest, ih) { List.Nil }, xs) }",
        "export-result": "export fn bad(n: u64) -> List { repeat(n, 0) }",
        "export-argument": "export fn bad(xs: List) -> i64 { sum(xs) }",
        "erased-at-runtime": "fn bad(xs: erased(List)) -> i64 { sum(xs) }",
        "false-induction": "fn bad(xs: List) -> Eq(length(xs), 0) { induct(fn(t) { Eq(length(t), 0) }, refl(0), fn(x, rest, ih) { ih }, xs) }",
        "changed-parameter": "enum Bad(n: u64) {\n    Nil\n    Cons(i64, Bad(n + 1))\n}",
        "partial-node": "fn bad() -> List { List.Cons(1) }",
        "array-element": "fn bad() -> i64 { index([List.Nil], 0, decide_lt(0, 1)) }",
        "wrong-case-arity": "fn bad(xs: List) -> i64 { induct(fn(t) { i64 }, 0, fn(x, ih) { ih }, xs) }",
        "flat-field": "enum Flat {\n    A\n}\nenum Heap {\n    Nil\n    Cons(Flat, Heap)\n}",
        "loop-capture": "fn bad(xs: List) -> i64 { fold(3, 0, fn(i, p, acc) { acc + sum(xs) }) }",
        "out-of-bounds-index": "enum Is(n: u64) {\n    None\n    More(refine(fn(j) { Lt(j, n + 1) }), Is(n))\n}\nfn bad(n: erased(u64), xs: [i64; n], is: Is(n)) -> i64 { induct(fn(t) { i64 }, 0, fn(j, rest, ih) { index(xs, witness(j), proof(j)) + ih }, is) }",
    }
    for name, body in source_invalid.items():
        path = temporary / f"list-{name}.jh"
        path.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert str(path) in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"list-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False)
        assert not obj.exists()

    core_invalid = {
        "rest-at-runtime": "(def bad (pi xs List I64) (lam xs List (induct List (lam t List I64) (int 0) (lam x I64 (lam rest List (lam ih I64 ih))) xs)))",
        "case-erased-tail": "(def bad (pi xs List I64) (lam xs List (case List (lam t List I64) (int 0) (lam x I64 (lam0 rest List x)) xs)))",
        "case-flat": "(data Two (A Two) (B Two))\n(def bad (pi t Two I64) (lam t Two (case Two (lam u Two I64) (int 0) (int 1) t)))",
        "erased-result": "(def bad (pi xs List I64) (lam xs List (induct List (lam t List I64) (int 0) (lam x I64 (lam0 rest List (lam0 ih I64 x))) xs)))",
        "used-twice": "(def bad (pi xs List I64) (lam xs List (add (app sum xs) (app sum xs))))",
        "recursion-capture": "(def bad (pi xs List (pi ys List I64)) (lam xs List (lam ys List (induct List (lam t List I64) (app sum ys) (lam x I64 (lam0 rest List (lam ih I64 (add ih (app drop ys))))) xs))))",
        "erased-recursive": "(data L (E L) (C (pi x I64 (pi0 t L L))))",
        "large-motive": "(def bad (pi xs List (Type 0)) (lam xs List (induct List (lam t List (Type 0)) I64 (lam x I64 (lam0 rest List (lam ih (Type 0) ih))) xs)))",
    }
    for name, body in core_invalid.items():
        path = temporary / f"list-{name}.jhc"
        path.write_text(core_prefix + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert "core:" in diagnostic.stderr, (name, diagnostic.stderr)

    reference = {}
    for _, name, _, body in definitions(core_text):
        reference[name] = evaluate(body, reference.copy())

    def checked(name, *args):
        """Evaluate an export independently; every node it built is taken apart once."""
        start = len(nodes)
        value = reference[name]
        for a in args:
            value = value(a)
        assert all(not n.alive for n in nodes[start:]), (name, args, "leak")
        return value

    rng = random.Random(0x60)
    # The Python evaluator recurses per node: lists stay short.
    ns = [0, 1, 2, 3, 7, 100, *(rng.randrange(0, 300) for _ in range(5))]
    xs = [0, 1, -1, 7, -9, 1 << 40, *(rng.randrange(-(1 << 40), 1 << 40) for _ in range(4))]
    formatted = temporary / "list-formatted.jh"
    formatted.write_text(command("fmt", example).stdout)
    assert mir == command("emit-mir", formatted, "--lib").stdout
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            for is_source, suffix in ((True, "jh"), (False, "jhc")):
                obj = temporary / f"list-{target}{level}-{suffix}.o"
                options = ["--lib"] if is_source else []
                command("emit-obj", example if is_source else core_example, *options,
                        "--target", target, level, "-o", str(obj), source=is_source)
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                native, allocations, frees = counted(obj, f"list{level}-{suffix}")
                native.total.argtypes = [ctypes.c_uint64, ctypes.c_int64]
                native.total.restype = ctypes.c_int64
                native.count.argtypes = [ctypes.c_uint64]
                native.count.restype = ctypes.c_uint64
                native.first.argtypes = [ctypes.c_uint64, ctypes.c_int64]
                native.first.restype = ctypes.c_int64
                for n in ns:
                    for x in xs[:4]:
                        before = allocations.value
                        assert native.total(n, x) == checked("total", n, x) == 2 * n * x, (n, x)
                        # repeat and doubled each build n + 1 nodes.
                        assert allocations.value - before == 2 * (n + 1) and allocations.value == frees.value
                        assert native.first(n, x) == checked("first", n, x) == (x if n > 0 else -1)
                        assert allocations.value == frees.value
                    assert native.count(n) == checked("count", n) == n
                    assert allocations.value == frees.value
    valid_obj = temporary / "list-valid.o"
    command("emit-obj", valid_path, "--lib", "-O0", "-o", str(valid_obj))
    native, allocations, frees = counted(valid_obj, "list-valid")
    native.trees.argtypes = [ctypes.c_int64]
    native.trees.restype = ctypes.c_int64
    native.mixed.argtypes = [ctypes.c_uint64, ctypes.c_int64, ctypes.c_uint64]
    native.mixed.restype = ctypes.c_int64
    for x in (0, 5, -3):
        assert native.trees(x) == x + 3 and allocations.value == frees.value
    for n in (0, 1, 2, 3, 10):
        for i in (0, 2, 3, 4, MAX):
            expected = (max(n, 1) - 1) * 5 + ([10, 20, 30, 40][i] + 10 if i < 4 else 0) + (3 if n > 2 else 0)
            assert native.mixed(n, 5, i) == expected, (n, i)
            assert allocations.value == frees.value, (n, i)
    print(f"dependent lists: paired source/core execution, counted nodes, structural recursion, {len(source_invalid)} source and {len(core_invalid)} core rejections passed")
