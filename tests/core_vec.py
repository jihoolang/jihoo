"""The vector of lib/dependent/vec.jh, called by tests/core.py.

A vector is heap data holding a buffer whose length is an earlier field, with
evidence that its length is within its capacity. Its contracts are types: reads
need evidence, and each change says what it does to the length. Native runs are
compared with a model on lists, with counted allocations.
"""
import ctypes
import os
import random
import shlex

from core_buffer import COUNTER

PRELUDE = """#![dependent_core]
import dependent.vec
fn lt_of(v: ref vec.Vec, i: u64, n: u64, e: erased(Eq(vec.len(v), n)), p: erased(Lt(i, n))) -> Lt(i, vec.len(v)) {
    transport(fn(m) { Lt(i, m) }, vec.eq_sym(vec.len(v), n, e), p)
}
"""

SOURCE_INVALID = {
    "get-no-evidence": ("fn bad(v: ref vec.Vec) -> i64 { vec.get(v, 0, decide_lt(0, 1)) }", "type mismatch"),
    "get-at-length": ("fn bad(v: ref vec.Vec, e: erased(Eq(vec.len(v), 1))) -> i64 { vec.get(v, 1, lt_of(v, 1, 1, e, decide_lt(0, 1))) }", "type mismatch"),
    "get-other": ("fn bad(v: ref vec.Vec, w: ref vec.Vec, i: u64, p: erased(Lt(i, vec.len(w)))) -> i64 { vec.get(v, i, p) }", "type mismatch"),
    "stale-after-clear": ("fn bad(inout v: vec.Vec, i: u64, p: erased(Lt(i, vec.len(v)))) -> i64 {\n let c = vec.clear(&v)\n vec.get(v, i, p)\n}", "type mismatch"),
    "stale-after-drop": ("fn bad(inout v: vec.Vec, i: u64, p: erased(Lt(i, vec.len(v))), q: erased(Lt(0, vec.len(v)))) -> i64 {\n let d = vec.drop_last(&v, q)\n vec.get(v, i, p)\n}", "type mismatch"),
    "drop-empty": ("fn bad(inout v: vec.Vec) -> Lt(0, 1) {\n let c = vec.clear(&v)\n let d = vec.drop_last(&v, decide_lt(0, 1))\n decide_lt(0, 1)\n}", "type mismatch"),
    "false-push": ("fn bad(inout v: vec.Vec) -> Eq(vec.len(v), vec.len(old(v)) + 2) {\n let a = vec.push(&v, 1)\n a\n}", "type mismatch"),
    "false-room": ("fn bad() -> vec.Vec { vec.Vec { len: 5, cap: 1, data: alloc(1, 0), room: decide_lt(5, 2) } }", "true closed inequality"),
    "wrong-buffer": ("fn bad(cap: u64) -> vec.Vec { vec.Vec { len: 0, cap, data: alloc(cap + 1, 0), room: zero_le(cap) } }", "type mismatch"),
    "missing-field": ("fn bad(cap: u64) -> vec.Vec { vec.Vec { len: 0, cap, data: alloc(cap, 0) } }", "gives every field"),
    "extra-field": ("fn bad(cap: u64) -> vec.Vec { vec.Vec { len: 0, cap, data: alloc(cap, 0), room: zero_le(cap), more: 1 } }", "gives every field"),
    "field-twice": ("fn bad(v: vec.Vec) -> i64 {\n match v {\n vec.Vec { len, cap, data, room } => {\n free(data, free(data, 0))\n }\n }\n}", "more than once"),
    "borrowed-free": ("fn bad(v: ref vec.Vec) -> i64 {\n match v {\n vec.Vec { len, cap, data, room } => free(data, 0)\n }\n}", "expected a buffer"),
    "borrowed-store": ("fn bad(v: ref vec.Vec) -> i64 {\n match v {\n vec.Vec { len, cap, data, room } => free(store(data, 0, 1, decide_lt(0, 1)), 0)\n }\n}", "expected a buffer"),
    "store-past-cap": ("fn bad(v: vec.Vec) -> vec.Vec {\n match v {\n vec.Vec { len, cap, data, room } => {\n store(&data, cap, 1, room)\n vec.Vec { len, cap, data, room }\n }\n }\n}", "type mismatch"),
    "unknown-module": ("fn bad(v: ref nope.Vec) -> i64 { 0 }", "unsupported type"),
}

MODULE_INVALID = {
    # A marked module imports only marked modules, and an ordinary module none.
    "marked-imports-ordinary": ("#![dependent_core]\nimport plain\nfn main() -> i64 { 0 }\n", "imports only dependent_core"),
    "ordinary-imports-marked": ("import dependent.vec\nfn main() -> i64 { 0 }\n", "legacy frontend"),
}

CORE_PRELUDE = """(data Box (MkBox (pi len U64 (pi cap U64 (pi data (Buffer cap) (pi0 room (Lt len (uadd cap 1)) Box))))))
"""
B = "Box"
CORE_INVALID = {
    "scalar-after-buffer": ("(data Bad (MkBad (pi f (pi x I64 I64) Bad)))", "data fields"),
    "borrow-field": ("(data Bad (MkBad (pi r (Ref (Buffer 1)) Bad)))", "data fields"),
    "proof-buffer": ("(inductive Bad 0 (MkBad (pi b (Buffer 1) (Bad))))", "must be u64"),
    "unsized-field": (f"(def bad (pi b (Buffer 1) {B}) (lam b (Buffer 1) (MkBox 0 2 b (zero-le 2))))", "type mismatch"),
    "false-room": (f"(def bad (pi b (Buffer 1) {B}) (lam b (Buffer 1) (MkBox 5 1 b (decide-lt 5 2))))", "true closed"),
    "drop-field": (f"(def bad (pi x {B} I64) (lam x {B} (case {B} (lam y {B} I64) (lam len U64 (lam cap U64 (lam data (Buffer cap) (lam0 room (Lt len (uadd cap 1)) (int 0))))) x)))", "must be used"),
    "use-field-twice": (f"(def bad (pi x {B} I64) (lam x {B} (case {B} (lam y {B} I64) (lam len U64 (lam cap U64 (lam data (Buffer cap) (lam0 room (Lt len (uadd cap 1)) (free data (free data (int 0))))))) x)))", "more than once"),
    # A case analysis may have a function result only of evidence, all given.
    "case-unapplied": (f"(def bad (pi x {B} (pi0 p (Lt 0 1) I64)) (lam x {B} (case {B} (lam y {B} (pi0 p (Lt 0 1) I64)) (lam len U64 (lam cap U64 (lam data (Buffer cap) (lam0 room (Lt len (uadd cap 1)) (lam0 p (Lt 0 1) (free data (int 0))))))) x)))", "not a function"),
    "case-runtime-argument": (f"(def bad (pi x {B} (pi a I64 I64)) (lam x {B} (lam a I64 (app (case {B} (lam y {B} (pi z I64 I64)) (lam len U64 (lam cap U64 (lam data (Buffer cap) (lam0 room (Lt len (uadd cap 1)) (lam z I64 (free data z)))))) x) a))))", "not a function"),
    "case-partial": (f"(def bad (pi x {B} (pi0 p (Lt 0 1) (pi0 q (Lt 0 2) I64))) (lam x {B} (lam0 p (Lt 0 1) (app (case {B} (lam y {B} (pi0 p (Lt 0 1) (pi0 q (Lt 0 2) I64))) (lam len U64 (lam cap U64 (lam data (Buffer cap) (lam0 room (Lt len (uadd cap 1)) (lam0 p (Lt 0 1) (lam0 q (Lt 0 2) (free data (int 0)))))))) x) p))))", "all of its evidence"),
}

VALID = PRELUDE + """
// n copies of x through a loop, which grows the vector from nothing.
fn filled(n: u64, x: i64) -> vec.Vec {
    fold(n, vec.new(), fn(i, p, acc) {
        let a = vec.push(&acc, x)
        acc
    })
}
fn total(v: ref vec.Vec) -> i64 {
    let n = vec.size(v)
    fold(witness(n), 0, fn(i, p, acc) { acc + vec.get(v, i, transport(fn(m) { Lt(i, m) }, proof(n), p)) })
}
export fn grown(n: u64, x: i64) -> i64 {
    let v = filled(n, x)
    total(v)
}
export fn capacity_of(n: u64) -> u64 {
    let v = filled(n, 1)
    vec.capacity(v)
}
// Room for all of them: no new buffer.
export fn reserved(x: i64) -> i64 {
    var v = vec.with_capacity(3)
    let a = vec.push(&v, x)
    let b = vec.push(&v, x + 1)
    let c = vec.push(&v, x + 2)
    total(v)
}
"""
VALID += """// A script with evidence for every read.
fn set_first(inout v: vec.Vec, x: i64, e: erased(Eq(vec.len(v), 2))) -> Eq(vec.len(v), 2) {
    let s = vec.set(&v, 0, x, lt_of(v, 0, 2, e, decide_lt(0, 2)))
    transport(fn(m) { Eq(vec.len(v), m) }, e, s)
}
export fn script(x: i64, y: i64, z: i64) -> i64 {
    var v = vec.with_capacity(1)
    let e = vec.clear(&v)
    let a = vec.push(&v, x)
    let one = transport(fn(m) { Eq(vec.len(v), m + 1) }, e, a)
    let b = vec.push(&v, y)
    let two = transport(fn(m) { Eq(vec.len(v), m + 1) }, one, b)
    let first = vec.get(v, 0, lt_of(v, 0, 2, two, decide_lt(0, 2)))
    let still = set_first(&v, first + z, two)
    let last = vec.last(v, lt_of(v, 0, 2, still, decide_lt(0, 2)))
    let d = vec.drop_last(&v, lt_of(v, 0, 2, still, decide_lt(0, 2)))
    let c = vec.push(&v, last * 2)
    last * 100 + total(v)
}
"""


def validate_vec(compiler, root, temporary, environment, run):
    def command(action, path, *options, source=True, success=True):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success, env=environment)

    example = root / "examples/core_vec.jh"
    command("check", example)
    mir = command("emit-mir", example, "--lib").stdout
    # Reads and writes have evidence: only allocations check.
    checks = [line for line in mir.splitlines() if "assert" in line or "panic" in line]
    assert checks and all('"allocation failed"' in line for line in checks), mir
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 43 and not result.stdout and not result.stderr

    failures = []
    for name, (body, reason) in SOURCE_INVALID.items():
        path = temporary / f"vec-{name}.jh"
        path.write_text(PRELUDE + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", success=False)
        if diagnostic.returncode != 1 or reason not in diagnostic.stderr:
            failures.append((name, diagnostic.returncode, diagnostic.stderr))
    (temporary / "plain.jh").write_text("pub fn f() -> i64 { 0 }\n")
    for name, (text, reason) in MODULE_INVALID.items():
        path = temporary / f"vec-{name}.jh"
        path.write_text(text)
        diagnostic = command("check", path, success=False)
        if diagnostic.returncode != 1 or reason not in diagnostic.stderr:
            failures.append((name, diagnostic.returncode, diagnostic.stderr))
    for name, (body, reason) in CORE_INVALID.items():
        path = temporary / f"vec-{name}.jhc"
        path.write_text(CORE_PRELUDE + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, source=False, success=False)
        if diagnostic.returncode != 1 or "core:" not in diagnostic.stderr or reason not in diagnostic.stderr:
            failures.append((name, diagnostic.returncode, diagnostic.stderr))
    assert not failures, "\n".join(f"{n} exit {c}: {e}" for n, c, e in failures)

    # Programs from an independent review. Each returns 0, and a core program
    # linked with the counter exits with 97 if an allocation is not freed once.
    accepted = root / "tests/core_accepted"
    counter = temporary / "accepted-counter.c"
    counter.write_text(COUNTER + """
#include <unistd.h>
__attribute__((destructor)) static void balanced(void) { if (allocations != frees) _exit(97); }
""")
    cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
    for path in sorted(accepted.rglob("*.jh*")):
        if path.parent.name == "modules" and path.name not in ("diamond.jh",):
            continue
        for level in ("-O0", "-O2"):
            if path.suffix == ".jh":
                command("run", path, level)
            else:
                obj = temporary / f"accepted-{path.stem}{level}.o"
                command("emit-obj", path, level, "-o", str(obj), source=False)
                exe = temporary / f"accepted-{path.stem}{level}"
                run([*cc, str(obj), str(counter), "-o", str(exe),
                     "-Wl,--wrap=malloc", "-Wl,--wrap=free"])
                run([str(exe)])

    path = temporary / "vec-valid.jh"
    path.write_text(VALID)
    command("check", path, "--lib")
    generator = random.Random(2)
    for level in ("-O0", "-O2"):
        obj = temporary / f"vec-valid{level}.o"
        command("emit-obj", path, "--lib", level, "-o", str(obj))
        counter = temporary / "vec-counter.c"
        counter.write_text(COUNTER)
        library = temporary / f"vec-valid{level}.so"
        cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
        run([*cc, "-shared", "-fPIC", str(obj), str(counter), "-o", str(library),
             "-Wl,--wrap=malloc", "-Wl,--wrap=free"])
        native = ctypes.CDLL(str(library))
        allocations = ctypes.c_long.in_dll(native, "allocations")
        frees = ctypes.c_long.in_dll(native, "frees")
        native.grown.argtypes = [ctypes.c_uint64, ctypes.c_int64]
        native.grown.restype = ctypes.c_int64
        native.capacity_of.argtypes = [ctypes.c_uint64]
        native.capacity_of.restype = ctypes.c_uint64
        native.reserved.argtypes = [ctypes.c_int64]
        native.reserved.restype = ctypes.c_int64
        native.script.argtypes = [ctypes.c_int64] * 3
        native.script.restype = ctypes.c_int64
        for n in [0, 1, 2, 3, 4, 7, 8, 15, 16, 100, 1000]:
            cap = 0
            growths = 0
            while cap < n:
                cap = cap + cap + 1
                growths += 1
            x = generator.randrange(-50, 50)
            before = allocations.value
            assert native.grown(n, x) == n * x, n
            # The first node and buffer, and a buffer and a node per growth. A
            # push with room rebuilds the node in place and allocates nothing.
            made = allocations.value - before
            # At -O2 LLVM may remove an allocation altogether.
            assert made == 2 + 2 * growths or (level == "-O2" and made < 2 + 2 * growths), (n, made)
            assert allocations.value == frees.value, n
            assert native.capacity_of(n) == cap, n
            assert allocations.value == frees.value, n
        for _ in range(100):
            x, y, z = (generator.randrange(-1000, 1000) for _ in range(3))
            before = allocations.value
            assert native.reserved(x) == 3 * x + 3
            made = allocations.value - before
            assert made == 2 or (level == "-O2" and made < 2), made
            model = []
            model.append(x)
            model.append(y)
            model[0] += z
            last = model[-1]
            model.pop()
            model.append(last * 2)
            assert native.script(x, y, z) == last * 100 + sum(model), (x, y, z)
            assert allocations.value == frees.value
