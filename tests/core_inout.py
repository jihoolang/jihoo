"""Inout parameters, called by tests/core.py.

A function with an inout parameter takes the owner and gives it back with its
result: Back(T, fn(x) { A }), made by give and taken apart by take. The owner
is moved in and out, so nothing else can reach it while it changes, and the
existing count of uses checks it. f(&x) rebinds x, and old(x) is its first
value in types and evidence.
"""
import ctypes
import json
import random
import shlex
import os

from core_buffer import COUNTER

PRELUDE = """#![dependent_core]
enum List {
    Nil
    Cons(i64, List)
}
fn length(xs: ref List) -> u64 { induct(fn(t) { u64 }, 0, fn(x, rest, ih) { ih + 1 }, xs) }
fn set(n: erased(u64), inout b: buffer(n), i: u64, p: erased(Lt(i, n)), v: i64) { store(&b, i, v, p) }
fn read(n: erased(u64), b: ref buffer(n), i: u64, p: erased(Lt(i, n))) -> i64 { index(b, i, p) }
fn both(inout a: buffer(4), c: ref buffer(4)) -> i64 { index(c, 0, decide_lt(0, 4)) }
fn pair(inout a: buffer(4), inout c: buffer(4)) { }
"""

# Each must be rejected, with this reason.
SOURCE_INVALID = {
    "not-var": ("fn bad() -> i64 { let b = alloc(4, 0)\n set(4, &b, 0, decide_lt(0, 4), 1)\n 0 }", "needs a var or an inout"),
    "missing-amp": ("fn bad() -> i64 { var b = alloc(4, 0)\n let u = set(4, b, 0, decide_lt(0, 4), 1)\n 0 }", "an inout parameter takes &x"),
    "extra-amp": ("fn bad() -> i64 { var b = alloc(4, 0)\n read(4, &b, 0, decide_lt(0, 4)) }", "only an inout parameter takes &x"),
    "alias-read": ("fn bad() -> i64 { var b = alloc(4, 0)\n both(&b, b) }", "core:"),
    "alias-twice": ("fn bad() -> i64 { var b = alloc(4, 0)\n pair(&b, &b)\n 0 }", "passed as &x once"),
    "consumed": ("fn bad(n: erased(u64), inout b: buffer(n)) { free(b, 0)\n}", "core:"),
    "freed-then-given": ("fn bad(inout b: buffer(4)) -> i64 { free(b, 0) }", "more than once"),
    "not-owned": ("fn bad(inout x: i64) -> i64 { x }", "is a buffer or heap data"),
    "evidence": ("fn bad(inout p: erased(Lt(0, 1))) -> i64 { 0 }", "is a buffer or heap data"),
    "export": ("export fn bad(inout b: buffer(4)) -> i64 { 0 }", "core:"),
    "in-argument": ("fn get(inout b: buffer(4)) -> i64 { 1 }\nfn id(x: i64) -> i64 { x }\nfn bad() -> i64 { var b = alloc(4, 0)\n let c = alloc(4, 0)\n let v = id(get(&b))\n v }", "a call with &x"),
    "in-sum": ("fn get(inout b: buffer(4)) -> i64 { 1 }\nfn bad() -> i64 { var b = alloc(4, 0)\n get(&b) + 1 }", "a call with &x"),
    "in-let-branch": ("fn bad(i: u64) -> i64 { var b = alloc(4, 0)\n let v = if_lt(i, 4, fn(q) { store(&b, i, 1, q)\n 0 }, 1)\n v }", "cannot change b here"),
    "in-loop": ("fn bad(n: u64) -> i64 { var b = alloc(4, 0)\n fold(n, 0, fn(i, p, acc) { store(&b, 0, 1, decide_lt(0, 4))\n acc }) }", "cannot change b here"),
    "old-at-runtime": ("fn bad(inout b: buffer(4), i: u64) -> i64 { index(old(b), 0, decide_lt(0, 4)) }", "old is evidence only"),
    "false-ensures": ("fn bad(inout xs: List) -> Eq(length(xs), length(old(xs)) + 1) { refl(length(old(xs))) }", "core:"),
    "new-is-not-old": ("fn grow(inout xs: List) -> Lt(0, 1) { decide_lt(0, 1) }\nfn bad(inout xs: List) -> Eq(length(xs), length(old(xs))) {\n let q = grow(&xs)\n refl(length(xs))\n}", "core:"),
    "stale-fact": ("fn grow(inout xs: List) -> Lt(0, 1) { decide_lt(0, 1) }\nfn need(xs: ref List, p: erased(Eq(length(xs), 0))) -> i64 { 0 }\nfn bad(xs0: List, p: erased(Eq(length(xs0), 0))) -> i64 {\n var xs = xs0\n let q = grow(&xs)\n need(xs, p)\n}", "core:"),
    "assign-let": ("fn bad() -> i64 { let b = alloc(4, 0)\n b = alloc(4, 1)\n 0 }", "needs a var or an inout"),
    "assign-other-type": ("fn bad(inout b: buffer(4)) { b = alloc(5, 0)\n}", "core:"),
    "assign-in-let": ("fn bad(i: u64, inout xs: List) -> i64 {\n let v = if_lt(i, 4, fn(q) {\n xs = List.Nil\n 1\n }, 0)\n v\n}", "cannot change xs here"),
    "assign-in-loop": ("fn bad(n: u64, inout xs: List) { let v = fold(n, 0, fn(i, p, acc) {\n xs = List.Nil\n acc\n })\n}", "cannot change xs here"),
    "assign-read": ("fn bad(inout xs: List) -> u64 {\n xs = List.Nil\n length(xs)\n}", "after assigning"),
    "assign-reuse-old": ("fn bad(inout xs: List) {\n xs = List.Cons(1, xs)\n xs = List.Cons(1, xs)\n free(xs, 0)\n}", "core:"),
    "match-without-assign": ("fn bad(inout xs: List) -> i64 {\n match xs {\n Nil => 0\n Cons(h, t) => h\n }\n}", "core:"),
    "false-after-match": ("fn bad(inout xs: List) -> Eq(length(xs), 0) {\n match xs {\n Nil => {\n xs = List.Nil\n refl(0)\n }\n Cons(h, t) => {\n xs = t\n refl(0)\n }\n }\n}", "core:"),
    "var-scalar": ("fn bad() -> i64 { var x = 1\n x }", "a var holds"),
    "statement": ("fn bad() -> i64 { 1\n 2 }", "dependent_core blocks"),
    "reserved": ("fn old(x: i64) -> i64 { x }", "reserved"),
}

# Each must be rejected by the kernel, whatever an elaborator writes.
CORE_PRELUDE = """(data List (Nil List) (Cons (pi x I64 (pi xs List List))))
"""
B4 = "(Buffer 4)"
BACK = f"(Back {B4} (lam x {B4} I64))"
GIVE_M = f"(lam x {B4} I64)"
CORE_INVALID = {
    "not-owned": (f"(def bad (pi x I64 (Back I64 (lam y I64 I64))) (lam x I64 (give (lam y I64 I64) x (int 0))))", "buffer or heap data"),
    "wrong-result": (f"(def bad (pi b {B4} {BACK}) (lam b {B4} (give {GIVE_M} b 0)))", "type mismatch"),
    "flag-erased": (f"(def bad (pi b {B4} (Back0 {B4} (lam x {B4} I64))) (lam b {B4} (give0 {GIVE_M} b (int 0))))", "erased"),
    "flag-kept": (f"(def bad (pi b {B4} (Back {B4} (lam x {B4} (Lt 0 1)))) (lam b {B4} (give (lam x {B4} (Lt 0 1)) b (decide-lt 0 1))))", "erased"),
    "borrow-result": (f"(def bad (pi b {B4} (Back {B4} (lam x {B4} (Ref {B4})))) (lam b {B4} (give (lam x {B4} (Ref {B4})) b b)))", "holds no borrow"),
    "function-result": (f"(def bad (pi b {B4} (Back {B4} (lam x {B4} (pi y I64 I64)))) (lam b {B4} (give (lam x {B4} (pi y I64 I64)) b (lam y I64 y))))", "holds no borrow"),
    "given-twice": (f"(def bad (pi b {B4} (Back {B4} (lam x {B4} {BACK}))) (lam b {B4} (give (lam x {B4} {BACK}) b (give {GIVE_M} b (int 0)))))", "more than once"),
    "take-unused": (f"(def bad (pi e {BACK} I64) (lam e {BACK} (take e (lam x {B4} (lam a I64 a)))))", "must be used"),
    "take-twice": (f"(def bad (pi e {BACK} I64) (lam e {BACK} (take e (lam x {B4} (lam a I64 (free x (free x a)))))))", "more than once"),
    "dropped": (f"(def bad (pi e {BACK} I64) (lam e {BACK} (int 0)))", "must be used"),
    "used-twice": (f"(def bad (pi e {BACK} I64) (lam e {BACK} (take e (lam x {B4} (lam a I64 (free x (take e (lam y {B4} (lam c I64 (free y c))))))))))", "more than once"),
    "take-escape": (f"(def bad (pi e (Back {B4} (lam x {B4} U64)) U64) (lam e (Back {B4} (lam x {B4} U64)) (take e (lam x {B4} (lam a U64 (free x (refl a)))))))", ""),
    "take-function": (f"(def bad (pi e {BACK} (pi y I64 I64)) (lam e {BACK} (take e (lam x {B4} (lam a I64 (free x (lam y I64 y)))))))", "not a function"),
    "take-scalar": (f"(def bad (pi x I64 I64) (lam x I64 (take x (lam y I64 (lam a I64 a)))))", "owner given back"),
    "take-wrong-owner": (f"(def bad (pi e {BACK} I64) (lam e {BACK} (take e (lam x (Buffer 5) (lam a I64 (free x a))))))", "owner and its result"),
    "take-erased": (f"(def bad (pi e {BACK} I64) (lam e {BACK} (take e (lam x {B4} (lam0 a (Lt 0 1) (free x (int 0)))))))", "erased as it was given"),
    "lend-back": (f"(def bad (pi e {BACK} I64) (lam e {BACK} (lend e (lam r (Ref {BACK}) (int 0)) (lam a I64 (lam y {BACK} (take y (lam x {B4} (lam c I64 (free x c)))))))))", "only an owned value is lent"),
    "capture": (f"(def bad (pi e {BACK} (pi y I64 I64)) (lam e {BACK} (lam y I64 (take e (lam x {B4} (lam a I64 (free x a)))))))\n(def worse (pi e {BACK} (pi z (pi y I64 I64) I64) ) (lam e {BACK} (lam z (pi y I64 I64) (app z (int 0)))))", ""),
    "free-back": (f"(def bad (pi e {BACK} I64) (lam e {BACK} (free e (int 0))))", "expected a buffer"),
    "store-back": (f"(def bad (pi e {BACK} {BACK}) (lam e {BACK} (store e 0 (int 0) (decide-lt 0 4))))", "expected a buffer"),
    "loop": (f"(def bad (pi b {B4} (pi n U64 {BACK})) (lam b {B4} (lam n U64 (fold n (give {GIVE_M} b (int 0)) (lam i U64 (lam0 p (Lt i n) (lam acc {BACK} acc)))))))", "accumulator"),
    "ref-of-back": (f"(def bad (pi r (Ref {BACK}) I64) (lam r (Ref {BACK}) (int 0)))", "buffer or heap data"),
}

# Programs the elaborator must keep working: branches, nested owners, a value
# in a tail branch and heap data, each with a result compared natively.
VALID = PRELUDE + """
fn bump(n: erased(u64), inout b: buffer(n), i: u64, p: erased(Lt(i, n)), by: i64) -> i64 {
    let before = index(b, i, p)
    store(&b, i, before + by, p)
    before
}
// A change in a tail branch, and none in the other: both give b back.
fn maybe(inout b: buffer(4), i: u64, v: i64) -> i64 {
    if_lt(i, 4, fn(q) {
        store(&b, i, v, q)
        1
    }, 0)
}
// The tuple of owner and result crosses a branch rather than being inlined.
fn choose(inout b: buffer(4), i: u64, k: u64) -> i64 {
    if_lt(k, 2, fn(q) { maybe(&b, i, 7) }, maybe(&b, i, 9))
}
fn swap(inout a: buffer(4), inout c: buffer(4), i: u64, p: erased(Lt(i, 4))) -> i64 {
    let x = index(a, i, p)
    let y = index(c, i, p)
    store(&a, i, y, p)
    store(&c, i, x, p)
    x - y
}
// Heap data through a function that gives it back; the length is known to stay.
fn same(inout xs: List) -> Eq(length(xs), length(old(xs))) { refl(length(xs)) }
fn total(xs: ref List) -> i64 { induct(fn(t) { i64 }, 0, fn(x, rest, ih) { x + ih }, xs) }
fn cons(n: u64, x: i64) -> List {
    fold(n, List.Nil, fn(i, p, acc) { List.Cons(x, acc) })
}
export fn branches(i: u64, k: u64, x: i64) -> i64 {
    var b = alloc(4, x)
    let r = choose(&b, i, k)
    let s = index(b, 0, decide_lt(0, 4))
    let t = index(b, 3, decide_lt(3, 4))
    r * 100 + s * 10 + t
}
export fn swapped(x: i64, y: i64) -> i64 {
    var a = alloc(4, x)
    var c = alloc(4, y)
    let d = swap(&a, &c, 1, decide_lt(1, 4))
    let u = index(a, 1, decide_lt(1, 4))
    let v = index(c, 1, decide_lt(1, 4))
    d * 100 + u * 10 + v
}
export fn listed(n: u64, x: i64) -> i64 {
    var xs = cons(n, x)
    let q = same(&xs)
    total(xs)
}
fn push(inout xs: List, x: i64) -> Eq(length(xs), length(old(xs)) + 1) {
    xs = List.Cons(x, xs)
    refl(length(old(xs)) + 1)
}
fn twice(inout xs: List, x: i64) -> Eq(length(xs), length(old(xs)) + 2) {
    let p = push(&xs, x)
    let q = push(&xs, x)
    transport(fn(m) { Eq(length(xs), m + 1) }, p, q)
}
fn set_head(inout xs: List, v: i64) -> Eq(length(xs), length(old(xs))) {
    match xs {
        Nil => {
            xs = List.Nil
            refl(0)
        }
        Cons(h, t) => {
            xs = List.Cons(v, t)
            refl(length(t) + 1)
        }
    }
}
fn pop(inout xs: List, missing: i64) -> i64 {
    match xs {
        Nil => {
            xs = List.Nil
            missing
        }
        Cons(h, t) => {
            xs = t
            h
        }
    }
}
fn add_all(inout xs: List, by: i64) {
    xs = induct(fn(t) { List }, List.Nil, fn(x, rest, ih) { List.Cons(x + by, ih) }, xs)
}
// Assigning before the last statement frees the old value and goes on.
fn reset(inout xs: List, x: i64) -> i64 {
    xs = List.Nil
    let p = push(&xs, x)
    total(xs)
}
export fn lists(x: i64) -> i64 {
    var xs = List.Nil
    let p = push(&xs, x)
    let q = twice(&xs, x + 1)
    let r = set_head(&xs, 100)
    let top = pop(&xs, -1)
    let s = total(xs)
    top * 1000 + s
}
export fn rebuilt(n: u64, x: i64) -> i64 {
    var xs = cons(n, x)
    let r = set_head(&xs, 7)
    add_all(&xs, 1)
    total(xs)
}
export fn assigned(n: u64, x: i64) -> i64 {
    var xs = cons(n, x)
    reset(&xs, x)
}
export fn unused_after(x: i64) -> i64 {
    var b = alloc(4, x)
    bump(4, &b, 0, decide_lt(0, 4), 1)
}
// One owner changes while another is read.
fn copy(inout to: buffer(4), from: ref buffer(4), i: u64, p: erased(Lt(i, 4))) -> i64 {
    let v = index(from, i, p)
    store(&to, i, v, p)
    v
}
export fn copied(x: i64, y: i64) -> i64 {
    var a = alloc(4, x)
    let c = alloc(4, y)
    let v = copy(&a, c, 2, decide_lt(2, 4))
    let w = index(a, 2, decide_lt(2, 4))
    let u = index(a, 1, decide_lt(1, 4))
    v * 100 + w * 10 + u + index(c, 2, decide_lt(2, 4))
}
"""


def validate_inout(compiler, root, temporary, environment, run, definitions, evaluate, buffers,
                   nodes):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    def counted(obj, name):
        """A shared library of obj whose malloc and free are counted."""
        counter = temporary / "inout-counter.c"
        counter.write_text(COUNTER)
        library = temporary / f"{name}.so"
        cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
        run([*cc, "-shared", "-fPIC", str(obj), str(counter), "-o", str(library),
             "-Wl,--wrap=malloc", "-Wl,--wrap=free"])
        native = ctypes.CDLL(str(library))
        return native, ctypes.c_long.in_dll(native, "allocations"), ctypes.c_long.in_dll(native, "frees")

    example = root / "examples/core_inout.jh"
    core_example = root / "examples/core_inout.jhc"
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable",
                   "JIHOO_LD": "/unavailable"}
    command("check", example, env=unavailable)
    command("check", core_example, source=False, env=unavailable)
    mir = command("emit-mir", example, "--lib").stdout
    assert mir == command("emit-mir", core_example, source=False).stdout
    # Evidence erased and changes in place: only the allocations check.
    checks = [line for line in mir.splitlines() if "assert" in line or "panic" in line]
    assert checks and all('"allocation failed"' in line for line in checks), mir
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 15 and not result.stdout and not result.stderr

    failures = []
    for name, (body, reason) in SOURCE_INVALID.items():
        path = temporary / f"inout-{name}.jh"
        path.write_text(PRELUDE + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", success=False)
        if diagnostic.returncode != 1 or "error" not in diagnostic.stderr or reason not in diagnostic.stderr:
            failures.append((name, diagnostic.returncode, diagnostic.stderr))

    for name, (body, reason) in CORE_INVALID.items():
        path = temporary / f"inout-{name}.jhc"
        path.write_text(CORE_PRELUDE + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, source=False, success=False)
        if diagnostic.returncode != 1 or "core:" not in diagnostic.stderr or reason not in diagnostic.stderr:
            failures.append((name, diagnostic.returncode, diagnostic.stderr))
    # Rejections written by an independent review of these rules.
    rejected = root / "tests/core_rejected"
    for name, reason in json.loads((rejected / "expected.json").read_text()).items():
        path = rejected / name
        if name.endswith(".jh"):
            diagnostic = command("check", path, "--lib", success=False)
        else:
            diagnostic = command("check", path, source=False, success=False)
        if diagnostic.returncode != 1 or reason not in diagnostic.stderr:
            failures.append((name, diagnostic.returncode, diagnostic.stderr))
    assert not failures, "\n".join(f"{n} exit {c}: {e}" for n, c, e in failures)

    path = temporary / "inout-valid.jh"
    path.write_text(VALID)
    command("check", path, "--lib")
    generator = random.Random(1)
    for level in ("-O0", "-O2"):
        obj = temporary / f"inout-valid{level}.o"
        command("emit-obj", path, "--lib", level, "-o", str(obj))
        native, allocations, frees = counted(obj, f"inout-valid{level}")
        for name, types in (("branches", [ctypes.c_uint64, ctypes.c_uint64, ctypes.c_int64]),
                            ("swapped", [ctypes.c_int64, ctypes.c_int64]),
                            ("listed", [ctypes.c_uint64, ctypes.c_int64]),
                            ("copied", [ctypes.c_int64, ctypes.c_int64]),
                            ("lists", [ctypes.c_int64]),
                            ("rebuilt", [ctypes.c_uint64, ctypes.c_int64]),
                            ("assigned", [ctypes.c_uint64, ctypes.c_int64]),
                            ("unused_after", [ctypes.c_int64])):
            getattr(native, name).argtypes = types
            getattr(native, name).restype = ctypes.c_int64
        for _ in range(200):
            i, k, x = generator.randrange(0, 6), generator.randrange(0, 4), generator.randrange(-9, 10)
            y = generator.randrange(-9, 10)
            cells = [x] * 4
            written = 0
            if i < 4:
                cells[i] = 7 if k < 2 else 9
                written = 1
            assert native.branches(i, k, x) == written * 100 + cells[0] * 10 + cells[3], (i, k, x)
            assert allocations.value == frees.value
            assert native.swapped(x, y) == (x - y) * 100 + y * 10 + x, (x, y)
            assert allocations.value == frees.value
            n = generator.randrange(0, 6)
            assert native.listed(n, x) == n * x
            assert allocations.value == frees.value
            assert native.copied(x, y) == y * 100 + y * 10 + x + y, (x, y)
            assert allocations.value == frees.value
            ls = [x + 1, x + 1, x]
            ls[0] = 100
            top = ls.pop(0)
            assert native.lists(x) == top * 1000 + sum(ls), x
            assert allocations.value == frees.value
            # A node rebuilt at its own size is changed in place: only the
            # n + 1 nodes of the list, with its Nil, are allocated.
            before = allocations.value
            expected = (x + 1) * (n - 1) + 8 if n > 0 else 0
            assert native.rebuilt(n, x) == expected, (n, x)
            assert allocations.value - before == n + 1, (n, allocations.value - before)
            assert allocations.value == frees.value
            assert native.assigned(n, x) == x, (n, x)
            assert allocations.value == frees.value
            assert native.unused_after(x) == x
            assert allocations.value == frees.value
