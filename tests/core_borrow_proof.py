"""Borrows in types and evidence, called by tests/core.py.

A function that reads a borrow applies in types and proofs to any value
of its type: `(borrow x)` is a borrow of x that only types and evidence
may contain. Conversion reads known nodes through views and computes
lends, so proofs about borrowing functions hold by computation or by
induction, and the kernel rejects such a borrow in code that runs.
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
    "false-computation": "fn bad(x: i64) -> Eq(length(pair(x)), 3) { refl(3) }",
    "false-lend": "fn bad(x: i64) -> Eq(count_pair(x), 1) { refl(1) }",
    "neutral": "fn bad(xs: List) -> Eq(length(doubled(xs)), length(xs)) { refl(length(xs)) }",
    "false-precondition": "fn bad(x: i64) -> i64 { head(List.Nil, decide_lt(0, 1)) }",
    "missing-precondition": "fn bad(xs: List) -> i64 { head(xs, decide_lt(0, 1)) }",
    "unproved-doubled": "fn bad(xs: List, p: erased(Lt(0, length(xs)))) -> i64 { head(doubled(xs), p) }",
    "runtime-temporary": "fn bad(x: i64) -> u64 { length(pair(x)) }",
}

CORE_INVALID = {
    "runtime-borrow": "(def bad (pi x I64 U64) (lam x I64 (app length (borrow (Cons x Nil)))))",
    "runtime-view": "(def bad (pi x I64 I64) (lam x I64 (view List I64 (int 0) (lam y I64 (lam rest (Ref List) y)) (borrow (Cons x Nil)))))",
    "borrow-scalar": "(def bad (pi x I64 (pi0 q (Eq (app length (borrow x)) 0) I64)) (lam x I64 (lam0 q (Eq (app length (borrow x)) 0) x)))",
    "borrow-borrow": "(def bad (pi xs (Ref List) (Eq (app length (borrow xs)) 0)) (lam xs (Ref List) (refl 0)))",
    "false-view": "(def bad (Eq (app length (borrow (Cons (int 1) Nil))) 0) (refl 0))",
    "false-lend": "(def bad (Eq (lend (Cons (int 1) Nil) (lam r (Ref List) (app length r)) (lam a U64 (lam xs List (drop List xs a)))) 0) (refl 0))",
}


def validate_borrow_proof(compiler, root, temporary, environment, run, definitions, evaluate,
                          buffers, nodes):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    def counted(obj, name):
        """A shared library of obj whose malloc and free are counted."""
        counter = temporary / "borrow-proof-counter.c"
        counter.write_text(COUNTER)
        library = temporary / f"{name}.so"
        cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
        run([*cc, "-shared", "-fPIC", str(obj), str(counter), "-o", str(library),
             "-Wl,--wrap=malloc", "-Wl,--wrap=free"])
        native = ctypes.CDLL(str(library))
        return native, ctypes.c_long.in_dll(native, "allocations"), ctypes.c_long.in_dll(native, "frees")

    example = root / "examples/core_borrow_proof.jh"
    core_example = root / "examples/core_borrow_proof.jhc"
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
    # The proofs and preconditions are erased: length never runs, and the
    # only recursion is doubled's.
    assert mir.count("fn recursion.") == 1, mir
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 15 and not result.stdout and not result.stderr

    for name, body in SOURCE_INVALID.items():
        path = temporary / f"borrow-proof-{name}.jh"
        path.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert str(path) in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"borrow-proof-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False)
        assert not obj.exists()

    for name, body in CORE_INVALID.items():
        path = temporary / f"borrow-proof-{name}.jhc"
        path.write_text(core_prefix + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert "core:" in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"borrow-proof-{name}.o"
        command("emit-obj", path, "-o", str(obj), source=False, success=False)
        assert not obj.exists(), name

    # More valid programs: a borrowed buffer's length in a proof, a lemma
    # whose type mentions its borrow applied to a list built in place, a
    # proof through lends in lets, and a precondition passed on.
    valid = prefix + """
fn total(xs: ref List) -> i64 { induct(fn(t) { i64 }, 0, fn(x, rest, ih) { x + ih }, xs) }
fn same(xs: ref List) -> Eq(length(xs), length(xs)) { refl(length(xs)) }
fn same_pair(x: i64) -> Eq(length(pair(x)), length(pair(x))) { same(pair(x)) }
fn three() -> Eq(length(List.Cons(1, pair(2))), 3) { refl(3) }
fn sum_pair(x: i64) -> i64 {
    let xs = pair(x)
    let s = total(xs)
    let n = length(xs)
    s + 1
}
fn sum_pair_value() -> Eq(length(pair(sum_pair(4))), 2) { refl(2) }
fn inline() -> i64 { index([42], 0, decide_lt(length(List.Nil), 1)) }
export fn more(x: i64) -> i64 { sum_pair(x) + head_doubled(pair(x), decide_lt(0, 2)) + inline() }
"""
    valid_path = temporary / "borrow-proof-valid.jh"
    valid_path.write_text(valid)
    command("check", valid_path, "--lib")
    obj = temporary / "borrow-proof-valid.o"
    command("emit-obj", valid_path, "--lib", "-O0", "-o", str(obj))
    native, allocations, frees = counted(obj, "borrow-proof-valid")
    native.more.argtypes = [ctypes.c_int64]
    native.more.restype = ctypes.c_int64
    for x in (0, 5, -3, 1 << 40):
        assert native.more(x) == 2 * x + 1 + 2 * x + 42, x
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

    rng = random.Random(0x66)
    ns = [0, 1, 2, 9, *(rng.randrange(0, 200) for _ in range(3))]
    xs = [0, 1, -1, 5, *(rng.randrange(-(1 << 40), 1 << 40) for _ in range(2))]
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            for is_source, suffix in ((True, "jh"), (False, "jhc")):
                obj = temporary / f"borrow-proof-{target}{level}-{suffix}.o"
                options = ["--lib"] if is_source else []
                command("emit-obj", example if is_source else core_example, *options,
                        "--target", target, level, "-o", str(obj), source=is_source)
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                native, allocations, frees = counted(obj, f"borrow-proof{level}-{suffix}")
                native.demo.argtypes = [ctypes.c_uint64, ctypes.c_int64]
                native.demo.restype = ctypes.c_int64
                for n in ns:
                    for x in xs:
                        before, created = allocations.value, len(nodes)
                        assert native.demo(n, x) == checked("demo", n, x) == 3 * x, (n, x)
                        # As many nodes as the evaluator builds at run time:
                        # pair's three, n + 2 and their doubled copy (LLVM
                        # removes one allocation at -O2). Those built for
                        # evidence are not program memory.
                        made = allocations.value - before
                        # Never more than the pure model's nodes: lowering
                        # reuses a node a case took apart, and -O2 removes more.
                        assert len(nodes) - created == 3 + 2 * (n + 2), (n, x)
                        assert 0 < made <= len(nodes) - created, (n, x, made)
                        assert allocations.value == frees.value
    print(f"dependent borrows in proofs: paired source/core execution, counted frees, {len(SOURCE_INVALID)} source and {len(CORE_INVALID)} core rejections passed")
