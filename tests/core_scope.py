"""Frees inserted where an owner's scope ends, called by tests/core.py.

The source elaborator inserts a free for each owned value that a scope, or
one of its alternatives, does not use. Each implicit program here must
compile to the same MIR as the program with those frees written out, and
the kernel must still reject what no inserted free can repair.
"""
import ctypes
import json
import os
import platform
import random
import shlex
import struct

from core_buffer import COUNTER

PAIRS = {
    # A parameter the body never uses is freed before it.
    "unused-parameter": (
        "fn f(b: buffer(3), x: i64) -> i64 { x }",
        "fn f(b: buffer(3), x: i64) -> i64 { free(b, x) }",
        "f(alloc(3, x), x)",
    ),
    # Several, in parameter order, the first innermost.
    "unused-parameters": (
        "fn f(b: buffer(3), xs: List, x: i64) -> i64 { x }",
        "fn f(b: buffer(3), xs: List, x: i64) -> i64 { free(xs, free(b, x)) }",
        "f(alloc(3, x), repeat(2, x), x)",
    ),
    "continuation": (
        "fn f(x: i64) -> i64 { load(alloc(3, x), 0, decide_lt(0, 3), fn(v, b) { v }) }",
        "fn f(x: i64) -> i64 { load(alloc(3, x), 0, decide_lt(0, 3), fn(v, b) { free(b, v) }) }",
        "f(x)",
    ),
    "one-branch": (
        "fn f(i: u64, b: buffer(3)) -> i64 { if_lt(i, 3, fn(p) { free(b, 1) }, 0) }",
        "fn f(i: u64, b: buffer(3)) -> i64 { if_lt(i, 3, fn(p) { free(b, 1) }, free(b, 0)) }",
        "f(i, alloc(3, x))",
    ),
    "two-in-branch": (
        "fn f(i: u64, b: buffer(3), xs: List) -> i64 { if_lt(i, 3, fn(p) { free(b, sum(xs)) }, 0) }",
        "fn f(i: u64, b: buffer(3), xs: List) -> i64 { if_lt(i, 3, fn(p) { free(b, sum(xs)) }, free(xs, free(b, 0))) }",
        "f(i, alloc(3, x), repeat(3, x))",
    ),
    "flat-match": (
        "fn f(t: Two, b: buffer(3)) -> i64 { match t { A => free(b, 1), B => 0 } }",
        "fn f(t: Two, b: buffer(3)) -> i64 { match t { A => free(b, 1), B => free(b, 0) } }",
        "f(if_lt(i, 3, fn(p) { Two.A }, Two.B), alloc(3, x))",
    ),
    "flat-induct": (
        "fn f(t: Two, xs: List) -> i64 { induct(fn(u) { i64 }, sum(xs), 0, t) }",
        "fn f(t: Two, xs: List) -> i64 { induct(fn(u) { i64 }, sum(xs), free(xs, 0), t) }",
        "f(if_lt(i, 3, fn(p) { Two.A }, Two.B), repeat(2, x))",
    ),
    "loop-body": (
        "fn f(x: i64) -> i64 { fold(3, x, fn(i, p, acc) { load(alloc(1, 0), 0, decide_lt(0, 1), fn(v, b) { acc + v }) }) }",
        "fn f(x: i64) -> i64 { fold(3, x, fn(i, p, acc) { load(alloc(1, 0), 0, decide_lt(0, 1), fn(v, b) { free(b, acc + v) }) }) }",
        "f(x)",
    ),
    "unused-field": (
        "fn f(xs: List) -> i64 { match xs { Nil => 0, Cons(x, rest) => x } }",
        "fn f(xs: List) -> i64 { match xs { Nil => 0, Cons(x, rest) => free(rest, x) } }",
        "f(repeat(i, x))",
    ),
    "unused-hypothesis": (
        "fn f(xs: List) -> List { induct(fn(t) { List }, List.Nil, fn(x, rest, ih) { List.Nil }, xs) }",
        "fn f(xs: List) -> List { induct(fn(t) { List }, List.Nil, fn(x, rest, ih) { free(ih, List.Nil) }, xs) }",
        "sum(f(repeat(i, x)))",
    ),
    # Inner alternatives first: the match frees ys in the arm without
    # it, then the branch frees xs where the match does not run.
    "nested": (
        "fn f(i: u64, xs: List, ys: List) -> i64 { if_lt(i, 3, fn(p) { match xs { Nil => sum(ys), Cons(x, rest) => x + sum(rest) } }, sum(ys)) }",
        "fn f(i: u64, xs: List, ys: List) -> i64 { if_lt(i, 3, fn(p) { match xs { Nil => sum(ys), Cons(x, rest) => free(ys, x + sum(rest)) } }, free(xs, sum(ys))) }",
        "f(i, repeat(2, x), repeat(3, 1))",
    ),
    "tree": (
        "fn f(t: Tree) -> i64 { match t { Leaf(x) => x, Node(l, m, r) => sum(m) } }",
        "fn f(t: Tree) -> i64 { match t { Leaf(x) => x, Node(l, m, r) => free(r, free(l, sum(m))) } }",
        "f(Tree.Node(Tree.Leaf(x), repeat(i, 2), Tree.Node(Tree.Leaf(1), List.Nil, Tree.Leaf(2))))",
    ),
}

DECLARATIONS = """
enum Two {
    A
    B
}
enum Tree {
    Leaf(i64)
    Node(Tree, List, Tree)
}
"""

# What no inserted free can repair: the kernel rejects it.
SOURCE_INVALID = {
    "used-twice": "fn bad(xs: List) -> i64 { sum(xs) + sum(xs) }",
    "scrutinee-again": "fn bad(xs: List) -> i64 { match xs { Nil => 0, Cons(x, rest) => sum(xs) + sum(rest) } }",
    "use-after-free": "fn bad(b: buffer(3)) -> i64 { free(b, load(b, 0, decide_lt(0, 3), fn(x, c) { x })) }",
    "double-free": "fn bad(xs: List) -> i64 { free(xs, free(xs, 0)) }",
    "branch-then-after": "fn bad(i: u64, b: buffer(3)) -> i64 { if_lt(i, 3, fn(p) { free(b, 1) }, 0) + free(b, 0) }",
    "free-scalar": "fn bad(x: i64) -> i64 { free(x, 0) }",
    "free-flat": "enum Two {\n    A\n}\nfn bad(t: Two) -> i64 { free(t, 0) }",
    "loop-capture": "fn bad(xs: List) -> i64 { fold(3, 0, fn(i, p, acc) { acc + sum(xs) }) }",
    "recursion-capture": "fn bad(xs: List, ys: List) -> i64 { induct(fn(t) { i64 }, sum(ys), fn(x, rest, ih) { ih + sum(ys) }, xs) }",
    "free-arity": "fn bad(xs: List) -> i64 { free(xs) }",
}

CORE_INVALID = {
    "leak": "(def bad (pi xs List I64) (lam xs List (int 0)))",
    "drop-flat": "(data Two (A Two) (B Two))\n(def bad (pi t Two I64) (lam t Two (drop Two t (int 0))))",
    "drop-other": "(data Tree (Leaf Tree) (Node (pi l Tree (pi r Tree Tree))))\n(def bad (pi xs List I64) (lam xs List (drop Tree xs (int 0))))",
    "drop-buffer": "(def bad (pi b (Buffer 1) I64) (lam b (Buffer 1) (drop List b (int 0))))",
    "drop-twice": "(def bad (pi xs List I64) (lam xs List (drop List xs (drop List xs (int 0)))))",
    "drop-after-use": "(def bad (pi xs List I64) (lam xs List (drop List xs (app sum xs))))",
    "drop-unknown": "(def bad (pi xs List I64) (lam xs List (drop Nope xs (int 0))))",
    "free-heap": "(def bad (pi xs List I64) (lam xs List (free xs (int 0))))",
}


def validate_scope(compiler, root, temporary, environment, run, definitions, evaluate, buffers, nodes):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    def counted(obj, name):
        """A shared library of obj whose malloc and free are counted."""
        counter = temporary / "scope-counter.c"
        counter.write_text(COUNTER)
        library = temporary / f"{name}.so"
        cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
        run([*cc, "-shared", "-fPIC", str(obj), str(counter), "-o", str(library),
             "-Wl,--wrap=malloc", "-Wl,--wrap=free"])
        native = ctypes.CDLL(str(library))
        return native, ctypes.c_long.in_dll(native, "allocations"), ctypes.c_long.in_dll(native, "frees")

    example = root / "examples/core_scope.jh"
    core_example = root / "examples/core_scope.jhc"
    source_text = example.read_text()
    core_text = core_example.read_text()
    prefix = source_text.split("// The first element alone")[0]
    core_prefix = core_text.split("(def head_or")[0]
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable",
                   "JIHOO_LD": "/unavailable"}
    command("check", example, env=unavailable)
    command("check", core_example, source=False, env=unavailable)
    # The frees the elaborator inserts are exactly the ones written out.
    mir = command("emit-mir", example, "--lib").stdout
    assert mir == command("emit-mir", core_example, source=False).stdout
    # Two exports, malloc and free, one drop function for List and the
    # recursions of repeat's consumers: sum twice and firsts.
    assert mir.count("fn ") == 8 and mir.count("fn drop.List ") == 1, mir
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 28 and not result.stdout and not result.stderr

    for name, (implicit, explicit, call) in PAIRS.items():
        texts = []
        for body in (implicit, explicit):
            path = temporary / f"scope-{name}.jh"
            path.write_text(prefix + DECLARATIONS + body +
                            f"\nexport fn probe(x: i64, i: u64) -> i64 {{ {call} }}\n")
            texts.append(command("emit-mir", path, "--lib").stdout)
        assert texts[0] == texts[1], (name, texts[0], texts[1])
        # The implicit program frees exactly what it allocates.
        path = temporary / f"scope-{name}.jh"
        path.write_text(prefix + DECLARATIONS + implicit +
                        f"\nexport fn probe(x: i64, i: u64) -> i64 {{ {call} }}\n")
        obj = temporary / f"scope-{name}.o"
        command("emit-obj", path, "--lib", "-O0", "-o", str(obj))
        if platform.machine() in ("x86_64", "AMD64", "aarch64", "arm64"):
            native, allocations, frees = counted(obj, f"scope-{name}")
            native.probe.argtypes = [ctypes.c_int64, ctypes.c_uint64]
            native.probe.restype = ctypes.c_int64
            for x in (0, 4, -7):
                for i in (0, 1, 2, 3, 9):
                    native.probe(x, i)
                    assert allocations.value > 0 and allocations.value == frees.value, (name, x, i)

    for name, body in SOURCE_INVALID.items():
        path = temporary / f"scope-{name}.jh"
        path.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert str(path) in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"scope-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False)
        assert not obj.exists()

    for name, body in CORE_INVALID.items():
        path = temporary / f"scope-{name}.jhc"
        path.write_text(core_prefix + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert "core:" in diagnostic.stderr, (name, diagnostic.stderr)

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

    rng = random.Random(0x64)
    ns = [0, 1, 2, 3, 9, *(rng.randrange(0, 200) for _ in range(4))]
    xs = [0, 1, -1, 5, 1 << 40, *(rng.randrange(-(1 << 40), 1 << 40) for _ in range(3))]
    indices = [0, 1, 2, 3, 9, 10, 11, (1 << 64) - 1]
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            for is_source, suffix in ((True, "jh"), (False, "jhc")):
                obj = temporary / f"scope-{target}{level}-{suffix}.o"
                options = ["--lib"] if is_source else []
                command("emit-obj", example if is_source else core_example, *options,
                        "--target", target, level, "-o", str(obj), source=is_source)
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                native, allocations, frees = counted(obj, f"scope{level}-{suffix}")
                native.first.argtypes = [ctypes.c_uint64, ctypes.c_int64]
                native.first.restype = ctypes.c_int64
                native.total.argtypes = [ctypes.c_uint64, ctypes.c_int64, ctypes.c_uint64]
                native.total.restype = ctypes.c_int64
                for n in ns:
                    for x in xs[:4]:
                        assert native.first(n, x) == checked("first", n, x) == (x if n else -1)
                        assert allocations.value == frees.value
                        for i in indices[:5] if level == "-O0" else indices:
                            before = allocations.value
                            expected = ((n * x if i < 10 else 0) + (x if i < 3 else -1) +
                                        (1 if n else 0))
                            assert native.total(n, x, i) == checked("total", n, x, i) == expected
                            # Three lists of n + 1 nodes (Nil is one), a buffer,
                            # and firsts' Nil and two nodes per element, of
                            # which it frees all but the last two.
                            made = 3 * (n + 1) + 1 + 2 * n + 1
                            assert allocations.value - before == made, (n, x, i)
                            assert allocations.value == frees.value
    print(f"dependent scopes: paired source/core execution, {len(PAIRS)} implicit/explicit pairs, counted frees, {len(SOURCE_INVALID)} source and {len(CORE_INVALID)} core rejections passed")
