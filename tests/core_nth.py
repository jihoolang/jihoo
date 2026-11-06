"""Views whose result depends on the borrow, called by tests/core.py.

A view's result may be a motive over the borrow, so a real recursion returns
evidence about what it read; it may be a function of arguments that change
along the recursion; a match on a borrowed variable refines the evidence that
mentions it; absurd closes a case with evidence of Lt(i, 0).
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
    "false-base": "fn bad(xs: ref List) -> refine(fn(k) { Eq(k, length(xs)) }) { induct(fn(t) { refine(fn(k) { Eq(k, length(t)) }) }, pack(1, refl(1)), fn(x, rest, ih) { pack(witness(ih) + 1, transport(fn(k) { Eq(witness(ih) + 1, k + 1) }, proof(ih), refl(witness(ih) + 1))) }, xs) }",
    "false-step": "fn bad(xs: ref List) -> refine(fn(k) { Eq(k, length(xs)) }) { induct(fn(t) { refine(fn(k) { Eq(k, length(t)) }) }, pack(0, refl(0)), fn(x, rest, ih) { pack(witness(ih), proof(ih)) }, xs) }",
    "unrefined": "fn bad(xs: ref List, ys: ref List, p: erased(Lt(0, length(ys)))) -> i64 { match xs { Nil => absurd(p), Cons(x, rest) => x } }",
    "unchecked-nth": "fn bad(xs: ref List, i: u64) -> i64 { nth(xs, i, decide_lt(0, 0)) }",
    "wrong-hypothesis": "fn bad(xs: ref List, i: u64, p: erased(Lt(i, length(xs)))) -> i64 { induct(fn(t, i: u64, p: erased(Lt(i, length(t)))) { i64 }, fn(i, p) { absurd(p) }, fn(x, rest, ih, i, p) { ih(i, p) }, xs)(i, p) }",
    "absurd-without-evidence": "fn bad(xs: ref List) -> i64 { absurd(0) }",
    "absurd-true": "fn bad(i: u64, p: erased(Lt(i, 1))) -> i64 { absurd(p) }",
    "absurd-no-type": "fn bad(p: erased(Lt(0, 0))) -> i64 { let v = absurd(p)\n v }",
    "partial": "fn bad(xs: ref List) -> i64 { induct(fn(t, i: u64) { i64 }, fn(i) { 0 }, fn(x, rest, ih, i) { ih }, xs)(0) }",
    "too-few-binders": "fn bad(xs: ref List) -> i64 { induct(fn(t, i: u64) { i64 }, fn(i) { 0 }, fn(x, rest) { 0 }, xs)(0) }",
    "owned-in-function-case": "fn bad(xs: ref List, b: buffer(1)) -> i64 { induct(fn(t, i: u64) { i64 }, fn(i) { free(b, 0) }, fn(x, rest, ih, i) { free(b, 0) }, xs)(0) }",
}

CORE_INVALID = {
    "value-motive": "(def bad (pi xs (Ref List) U64) (lam xs (Ref List) (view List (lam t List U64) 0 (lam x I64 (lam rest (Ref List) 1)) xs)))",
    "other-motive": "(data Other (Done Other) (More (pi o Other Other))) (def bad (pi xs (Ref List) U64) (lam xs (Ref List) (view List (lam t (Ref Other) U64) 0 (lam x I64 (lam rest (Ref List) 1)) xs)))",
    "erased-motive": "(def bad (pi xs (Ref List) U64) (lam xs (Ref List) (view List (lam0 t (Lt 0 1) U64) 0 (lam x I64 (lam rest (Ref List) 1)) xs)))",
    "type-motive": "(def bad (pi xs (Ref List) (Type 0)) (lam xs (Ref List) (view List (lam r (Ref List) (Type 0)) U64 (lam x I64 (lam rest (Ref List) I64)) xs)))",
    "prop-motive": "(def bad (pi xs (Ref List) (Lt 0 1)) (lam xs (Ref List) (view List (lam r (Ref List) (Lt 0 1)) (decide-lt 0 1) (lam x I64 (lam rest (Ref List) (decide-lt 0 1))) xs)))",
    "runtime-deref-field": "(def bad (pi xs (Ref List) I64) (lam xs (Ref List) (view List I64 (int 0) (lam x I64 (lam rest (Ref List) (drop List (deref rest) x))) xs)))",
    "capture": "(def bad (pi xs (Ref List) (pi b (Buffer 1) I64)) (lam xs (Ref List) (lam b (Buffer 1) (app (lam f (pi i U64 I64) (add (app f 0) (app f 1))) (view List (pi i U64 I64) (lam i U64 (free b (int 0))) (lam x I64 (lam rest (Ref List) (lam i U64 (free b (int 0))))) xs)))))",
    "applied-twice-partial": "(def bad (pi xs (Ref List) (pi b (Buffer 1) I64)) (lam xs (Ref List) (lam b (Buffer 1) (app (lam f (pi0 p (Lt 0 1) (pi i U64 I64)) (add (app f (decide-lt 0 1) 0) (app f (decide-lt 0 1) 1))) (view List (pi0 p (Lt 0 1) (pi i U64 I64)) (lam0 p (Lt 0 1) (lam i U64 (free b (int 0)))) (lam x I64 (lam rest (Ref List) (lam0 p (Lt 0 1) (lam i U64 (free b (int 0)))))) xs)))))",
    "function-escapes-lend": "(def bad (pi xs List (pi i U64 I64)) (lam xs List (lend xs (lam r (Ref List) (view List (pi i U64 I64) (lam i U64 (int 0)) (lam x I64 (lam rest (Ref List) (lam i U64 (app head_or rest (int 0))))) r)) (lam f (pi i U64 I64) (lam y List (drop List y f))))))",
    "absurd-function": "(def bad (pi0 p (Lt 0 0) (pi i U64 I64)) (lam0 p (Lt 0 0) (absurd (pi i U64 I64) p)))",
    "absurd-one": "(def bad (pi0 p (Lt 0 1) I64) (lam0 p (Lt 0 1) (absurd I64 p)))",
    "absurd-evidence-at-runtime": "(def bad (pi i U64 (pi0 p (Lt i i) I64)) (lam i U64 (lam0 p (Lt i i) (absurd I64 p))))",
    "layout-by-value": "(def bad (pi xs (Ref List) (if-lt (app length xs) 1 q U64 I64)) (lam xs (Ref List) (view List (lam r (Ref List) (if-lt (app length r) 1 q U64 I64)) 0 (lam x I64 (lam rest (Ref List) x)) xs)))",
    "wrong-node": "(def bad (pi xs (Ref List) (Refine (lam k U64 (Eq k (app length xs))))) (lam xs (Ref List) (view List (lam r (Ref List) (Refine (lam k U64 (Eq k (app length r))))) (pack (lam k U64 (Eq k 0)) 0 (refl 0)) (lam x I64 (lam rest (Ref List) (pack (lam k U64 (Eq k (app length rest))) (app length rest) (refl (app length rest))))) xs)))",
}

# Programs the kernel accepts and lowering does not run: rejected, no object.
UNLOWERED = {
    "case-not-a-lambda": "(export bad (pi x U64 I64) (lam x U64 (app (lam xs List (lend xs (lam r (Ref List) (app (view List (pi i U64 I64) (lam i U64 (int 0)) (lam y I64 (lam rest (Ref List) (if-lt 0 x q (lam i U64 (int 1)) (lam i U64 (int 2))))) r) 0)) (lam a I64 (lam y List (drop List y a))))) (Cons (int 1) Nil))))",
}

# Why each is rejected: a rejection for another reason would test nothing.
REASONS = {
    "false-base": "type mismatch",
    "false-step": "type mismatch",
    "unrefined": "absurd needs evidence",
    "unchecked-nth": "decide-lt needs a true",
    "wrong-hypothesis": "type mismatch",
    "absurd-without-evidence": "absurd needs evidence",
    "absurd-true": "absurd needs evidence",
    "absurd-no-type": "absurd needs an expected type",
    "partial": "type mismatch",
    "too-few-binders": "wrong number of lambda parameters",
    "owned-in-function-case": "cannot use an outer owned value",
    "value-motive": "motive takes the borrow",
    "other-motive": "motive takes the borrow",
    "erased-motive": "motive is fn(r)",
    "type-motive": "result is runtime data",
    "prop-motive": "result is runtime data",
    "runtime-deref-field": "value is evidence only",
    "capture": "cannot capture an owned value",
    "applied-twice-partial": "cannot capture an owned value",
    "function-escapes-lend": "cannot outlive its lend",
    "absurd-function": "result is not a function",
    "absurd-one": "absurd needs evidence",
    "absurd-evidence-at-runtime": "absurd needs evidence",
    "layout-by-value": "one representation",
    "wrong-node": "type mismatch",
    "case-not-a-lambda": "ends in fn(...)",
}

MORE = """
enum Tree {
    Leaf(i64)
    Node(Tree, Tree)
}

fn leaves(t: ref Tree) -> u64 { induct(fn(u) { u64 }, fn(x) { 1 }, fn(l, r, a, b) { a + b }, t) }

fn counted(t: ref Tree) -> refine(fn(k) { Eq(k, leaves(t)) }) {
    induct(fn(u) { refine(fn(k) { Eq(k, leaves(u)) }) }, fn(x) { pack(1, refl(1)) }, fn(l, r, a, b) {
        pack(witness(a) + witness(b), transport(fn(k) { Eq(witness(a) + witness(b), k + leaves(r)) }, proof(a),
            transport(fn(k) { Eq(witness(a) + witness(b), witness(a) + k) }, proof(b),
                refl(witness(a) + witness(b)))))
    }, t)
}

fn grow(x: i64) -> Tree { Tree.Node(Tree.Leaf(x), Tree.Node(Tree.Leaf(x + 1), Tree.Leaf(x + 2))) }

export fn tree_leaves(x: i64) -> u64 {
    let t = grow(x)
    witness(counted(t))
}

// An owned argument threaded through a recursion: the buffer is written at
// each node and given back; the last write wins.
fn fill(xs: ref List, b: buffer(2)) -> buffer(2) {
    induct(fn(t, b: buffer(2)) { buffer(2) }, fn(b) { b }, fn(x, rest, ih, b) {
        ih(store(b, 1, x, decide_lt(1, 2)))
    }, xs)(b)
}

export fn filled(n: u64, x: i64) -> i64 {
    let xs = ascending(n, x)
    let b = fill(xs, alloc(2, 0))
    load(b, 1, decide_lt(1, 2), fn(v, b) { v })
}

// Arguments given by a lambda inside the case, and a hypothesis returned
// unapplied: the elaborator gives the case its arguments.
fn last_or(xs: ref List, missing: i64) -> i64 {
    induct(fn(t, m: i64) { i64 }, fn(m) { m }, fn(x, rest, ih) { fn(m) { ih(x) } }, xs)(missing)
}

fn skip(xs: ref List, missing: i64) -> i64 {
    induct(fn(t, m: i64) { i64 }, fn(m) { m }, fn(x, rest, ih) { ih }, xs)(missing)
}

export fn lasts(n: u64, x: i64) -> i64 {
    let xs = ascending(n, x)
    let a = last_or(xs, 100)
    let b = skip(xs, 1000)
    a + b
}

// A branch with a function result, whose alternatives take the argument.
fn capped(xs: ref List, limit: i64) -> i64 {
    induct(fn(t, m: u64) { i64 }, fn(m) { 0 }, fn(x, rest, ih) {
        fn(m) { if_lt(m, 2, fn(q) { x + ih(m + 1) }, 0) }
    }, xs)(0)
}

export fn first_two(n: u64, x: i64) -> i64 {
    let xs = ascending(n, x)
    capped(xs, 0)
}

// A hypothesis called from inside another recursion's case, which must
// receive the call's operands.
fn nested(xs: ref List) -> i64 {
    induct(fn(t, m: i64) { i64 }, fn(m) { m }, fn(x, rest, ih, m) {
        induct(fn(u) { i64 }, ih(m + x), fn(y, more, again) { again + ih(y) }, rest)
    }, xs)(0)
}

export fn nested_sum(n: u64, x: i64) -> i64 {
    let xs = ascending(n, x)
    nested(xs)
}

// An owned value used by the arm of a match that refines evidence: the case
// runs once, given its evidence, so it may use the buffer.
fn head_into(xs: ref List, p: erased(Lt(0, length(xs))), b: buffer(1)) -> i64 {
    match xs {
        Nil => absurd(p)
        Cons(x, rest) => load(b, 0, decide_lt(0, 1), fn(v, b) { v + x })
    }
}

export fn added(n: u64, x: i64) -> i64 {
    let xs = ascending(n, x)
    let k = size(xs)
    if_lt(0, witness(k), fn(q) {
        head_into(xs, transport(fn(m) { Lt(0, m) }, proof(k), q), alloc(1, 7))
    }, -1)
}

// A proof by cases about a borrow, refining evidence, used by a later load.
fn count(xs: ref List) -> u64 { induct(fn(t) { u64 }, 0, fn(x, rest, ih) { ih + 1 }, xs) }

fn counts(xs: ref List, p: erased(Lt(0, length(xs)))) -> Lt(0, count(xs)) {
    match xs {
        Nil => absurd(p)
        Cons(x, rest) => zero_le(count(rest))
    }
}

fn read_first(xs: ref List, p: erased(Lt(0, length(xs)))) -> i64 {
    head(xs, p)
}

export fn proved_first(n: u64, x: i64) -> i64 {
    let xs = ascending(n, x)
    let k = size(xs)
    if_lt(0, witness(k), fn(q) {
        read_first(xs, transport(fn(m) { Lt(0, m) }, proof(k), q))
    }, -1)
}
"""

# A data type whose proof field reads an earlier heap field: a view gives the
# field as a borrow and the proof about what that borrow reads.
INVARIANT = """
(data Box (Hold (pi l List (pi0 p (Lt 0 (app length (borrow l))) Box))) (Empty Box))

(def from_box
  (pi b (Ref Box) I64)
  (lam b (Ref Box)
    (view Box I64
      (lam l (Ref List) (lam0 p (Lt 0 (app length l)) (app head l p)))
      (int -2)
      b)))

(export boxed
  (pi n U64 (pi x I64 I64))
  (lam n U64 (lam x I64
    (app (lam xs List
      (lend xs (lam r (Ref List) (app size r))
        (lam k (Refine (lam m U64 (Eq m (app length (borrow xs))))) (lam y List
          (if-lt 0 (witness k) q
            (app (lam w Box
              (lend w (lam r (Ref Box) (app from_box r))
                (lam a I64 (lam z Box (drop Box z a)))))
              (Hold xs (transport (lam m U64 (Lt 0 m)) (proof k) q)))
            (drop List xs (int -3)))))))
      (app ascending n x)))))
"""


def validate_nth(compiler, root, temporary, environment, run, definitions, evaluate, buffers, nodes):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    def counted(obj, name):
        """A shared library of obj whose malloc and free are counted."""
        counter = temporary / "nth-counter.c"
        counter.write_text(COUNTER)
        library = temporary / f"{name}.so"
        cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
        run([*cc, "-shared", "-fPIC", str(obj), str(counter), "-o", str(library),
             "-Wl,--wrap=malloc", "-Wl,--wrap=free"])
        native = ctypes.CDLL(str(library))
        return native, ctypes.c_long.in_dll(native, "allocations"), ctypes.c_long.in_dll(native, "frees")

    example = root / "examples/core_nth.jh"
    core_example = root / "examples/core_nth.jhc"
    source_text = example.read_text()
    core_text = core_example.read_text()
    prefix = source_text.split("export fn at")[0]
    core_prefix = core_text.split("(export at")[0]
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable",
                   "JIHOO_LD": "/unavailable"}
    command("check", example, env=unavailable)
    command("check", core_example, source=False, env=unavailable)
    mir = command("emit-mir", example, "--lib").stdout
    assert mir == command("emit-mir", core_example, source=False).stdout
    # The only checks are allocations': nth and head read without a bounds
    # check, and absurd's case is unreachable.
    checks = [line for line in mir.splitlines() if "assert" in line or "panic" in line]
    assert checks and all('"allocation failed"' in line for line in checks), mir
    assert "unreachable" in mir, mir
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 3 and not result.stdout and not result.stderr, result

    for name, body in SOURCE_INVALID.items():
        path = temporary / f"nth-{name}.jh"
        path.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert str(path) in diagnostic.stderr, (name, diagnostic.stderr)
        assert REASONS[name] in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"nth-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False)
        assert not obj.exists(), name

    for name, body in CORE_INVALID.items():
        path = temporary / f"nth-{name}.jhc"
        path.write_text(core_prefix + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert REASONS[name] in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"nth-{name}.o"
        command("emit-obj", path, "-o", str(obj), source=False, success=False)
        assert not obj.exists(), name

    for name, body in UNLOWERED.items():
        path = temporary / f"nth-{name}.jhc"
        path.write_text(core_prefix + body + "\n")
        obj = temporary / f"nth-{name}.o"
        rejected = command("emit-obj", path, "-o", str(obj), source=False, success=False)
        assert REASONS[name] in rejected.stderr, (name, rejected.stderr)
        assert not obj.exists(), name

    # More valid programs, against what they should compute.
    valid = temporary / "nth-more.jh"
    valid.write_text(prefix + MORE)
    command("check", valid, "--lib")
    invariant = temporary / "nth-invariant.jhc"
    invariant.write_text(core_prefix + INVARIANT)
    command("check", invariant, source=False)
    for level in ("-O0", "-O2"):
        obj = temporary / f"nth-more{level}.o"
        command("emit-obj", valid, "--lib", level, "-o", str(obj))
        native, allocations, frees = counted(obj, f"nth-more{level}")
        for name, args, result in (("tree_leaves", [ctypes.c_int64], ctypes.c_uint64),
                                   ("filled", [ctypes.c_uint64, ctypes.c_int64], ctypes.c_int64),
                                   ("lasts", [ctypes.c_uint64, ctypes.c_int64], ctypes.c_int64),
                                   ("first_two", [ctypes.c_uint64, ctypes.c_int64], ctypes.c_int64),
                                   ("nested_sum", [ctypes.c_uint64, ctypes.c_int64], ctypes.c_int64),
                                   ("added", [ctypes.c_uint64, ctypes.c_int64], ctypes.c_int64),
                                   ("proved_first", [ctypes.c_uint64, ctypes.c_int64], ctypes.c_int64)):
            getattr(native, name).argtypes = args
            getattr(native, name).restype = result

        def nested_model(values):
            def go(items, m):
                if not items:
                    return m
                x, rest = items[0], items[1:]
                result = go(rest, m + x)
                for y in reversed(rest):
                    result = result + go(rest, y)
                return result
            return go(values, 0)

        assert native.tree_leaves(5) == 3
        assert allocations.value == frees.value
        for n in (0, 1, 2, 3, 6):
            for x in (0, 5, -9, 1 << 30):
                # The list is x + n, ..., x + 1.
                values = [x + n - i for i in range(n)]
                assert native.filled(n, x) == (values[-1] if values else 0), (n, x)
                last = values[-1] if values else None
                assert native.lasts(n, x) == (last if n else 100) + (1000), (n, x)
                assert native.first_two(n, x) == sum(values[:2]), (n, x)
                if n <= 3:
                    assert native.nested_sum(n, x) == nested_model(values), (n, x)
                expected = values[0] + 7 if n else -1
                assert native.added(n, x) == expected, (n, x)
                assert native.proved_first(n, x) == (values[0] if n else -1), (n, x)
                assert allocations.value == frees.value, (n, x)

    obj = temporary / "nth-invariant.o"
    command("emit-obj", invariant, "-O0", "-o", str(obj), source=False)
    native, allocations, frees = counted(obj, "nth-invariant")
    native.boxed.argtypes = [ctypes.c_uint64, ctypes.c_int64]
    native.boxed.restype = ctypes.c_int64
    assert native.boxed(0, 4) == -3 and native.boxed(3, 4) == 7
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

    rng = random.Random(0x69)
    ns = [0, 1, 2, 3, 7, *(rng.randrange(0, 60) for _ in range(2))]
    xs = [0, 1, -1, *(rng.randrange(-(1 << 40), 1 << 40) for _ in range(2))]
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            for is_source, suffix in ((True, "jh"), (False, "jhc")):
                obj = temporary / f"nth-{target}{level}-{suffix}.o"
                options = ["--lib"] if is_source else []
                command("emit-obj", example if is_source else core_example, *options,
                        "--target", target, level, "-o", str(obj), source=is_source)
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                native, allocations, frees = counted(obj, f"nth{level}-{suffix}")
                native.at.argtypes = [ctypes.c_uint64, ctypes.c_uint64, ctypes.c_int64]
                native.at.restype = ctypes.c_int64
                native.first.argtypes = [ctypes.c_uint64, ctypes.c_int64]
                native.first.restype = ctypes.c_int64
                for n in ns:
                    for x in xs:
                        assert native.first(n, x) == checked("first", n, x) == (x + n if n else -1)
                        for i in {0, 1, n // 2, n - 1 if n else 0, n, n + 1, (1 << 64) - 1}:
                            expected = x + n - i if i < n else -1
                            assert native.at(n, i, x) == checked("at", n, i, x) == expected, (n, i, x)
                        assert allocations.value == frees.value, (n, x)
    print(f"dependent views: paired source/core execution, counted frees, {len(SOURCE_INVALID)} source and {len(CORE_INVALID) + len(UNLOWERED)} core rejections passed")
