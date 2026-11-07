"""Contextual source elaboration, without new trusted-core rules."""
import ctypes
import json
import os
import platform
import shlex
import struct

from core_buffer import COUNTER


PROGRAM = """#![dependent_core]
enum List { Nil; Cons(i64, List) }
fn identity(n: u64) -> u64 { n }
fn sym(a: u64, b: u64, p: erased(Eq(a, b))) -> Eq(b, a) {
    transport(fn(k: u64) { Eq(k, a) }, p, refl(a))
}
fn repeat(n: u64, x: i64) -> List {
    fold(n, List.Nil, fn(i: u64, p: erased(Lt(i, n)), acc: List) -> List { List.Cons(x, acc) })
}
fn sum(xs: List) -> i64 {
    induct(fn(t: List) { i64 }, 0, fn(x: i64, rest: List, ih: i64) -> i64 { x + ih }, xs)
}
fn length(xs: ref List) -> u64 {
    induct(fn(t: List) { u64 }, 0, fn(x: i64, rest: ref List, ih: u64) { ih + 1 }, xs)
}
export fn borrowed(n: u64) -> u64 {
    let xs = repeat(n, 1)
    let a = 1 + length(xs)
    let b = length(xs) + 2
    a + b
}
export fn numeric(n: u64) -> u64 {
    let a = 1 + n
    let b = (1 + 2) + a
    let c = 18446744073709551615 + identity(0)
    let d = 1 + (2 + identity(b))
    d
}
export fn signed(n: i64) -> i64 { let a = (1 + 2) * n; a - 1 }
export fn defaults() -> i64 { let a = 1 + 2; a }
export fn total(n: u64, x: i64) -> i64 { sum(repeat(n, x)) }
export fn count(n: u64) -> u64 {
    fold(n, fn(k: u64) { u64 }, 0,
        fn(i: u64, p: Lt(i, n), acc: u64) -> u64 { acc + 1 })
}
export fn pick(i: u64) -> i64 {
    if_lt(i, 3, fn(p: erased(Lt(i, 1 + 2))) {
        if_eq(i, i, fn(q: Eq(i, i)) { index([10, 20, 30], i, p) }, -2)
    }, -1)
}
// An erased constructor field stays erased even with a bare domain annotation.
trait Step(n: u64) { fn done(n: u64, p: erased(Lt(n, 4))) -> Step(n) }
fn bound(n: u64, s: erased(Step(n))) -> Lt(n, 4) {
    induct(fn(k: u64) { Lt(k, 4) }, fn(k: u64, p: Lt(k, 4)) -> Lt(k, 4) { p }, s)
}
export fn proved() -> i64 { index([1, 2, 3, 4], 2, bound(2, done(2, decide_lt(2, 4)))) }
"""

PROGRAM += """
enum Choice { Number(u64); Empty }
export fn branch(n: u64) -> u64 {
    let x = if_lt(n, 3, fn(p: Lt(n, 3)) -> u64 { n + 1 }, 9)
    let y = if_eq(n, 0, fn(p) { x }, 2)
    y
}
export fn matched(n: u64) -> u64 {
    let choice = if_lt(n, 3, fn(p) { Choice.Number(n) }, Choice.Empty)
    let x = match choice { Choice.Empty => 9; Choice.Number(k) => k + 1 }
    x
}
export fn owned_match(n: u64) -> i64 {
    let xs = repeat(n, 7)
    let x = match xs { List.Nil => 0; List.Cons(v, rest) => v }
    x
}
fn borrowed_match(xs: ref List) -> i64 {
    let x = match xs { List.Cons(v, rest) => v; List.Nil => 0 }
    x
}
export fn view_match(n: u64) -> i64 { let xs = repeat(n, 7); borrowed_match(xs) }
fn proof_branch(n: u64) -> Eq(n, n) {
    let p = if_eq(n, n, fn(q) -> Eq(n, n) { q }, refl(n))
    p
}
fn proof_match(e: Choice) -> Eq(0, 0) {
    let p = match e { Choice.Number(k) => refl(0); Choice.Empty => refl(0) }
    p
}
enum PairChoice { Pair(u64, u64); None }
fn outer_type(n: u64, e: PairChoice) -> buffer(n) {
    let b = match e { PairChoice.None => alloc(n, 9); PairChoice.Pair(a, b) => alloc(n, 7) }
    b
}
export fn outer_match(n: u64) -> i64 {
    let b = outer_type(n, PairChoice.Pair(1, 2))
    free(b, 7)
}
fn borrowed_proof(xs: ref List) -> Eq(0, 0) {
    let p: Eq(0, 0) = match xs { List.Nil => refl(0); List.Cons(x, rest) => refl(0) }
    p
}
export fn borrowed_branch(n: u64) -> u64 {
    let xs = repeat(n, 7)
    let v = if_lt(n, 3, fn(p) { length(xs) }, 9)
    v
}
export fn branch_buffer(n: u64) -> i64 {
    let b = if_lt(n, 3, fn(p) -> buffer(1) { alloc(1, 7) }, alloc(1, 9))
    load(b, 0, decide_lt(0, 1), fn(x, b) { free(b, x) })
}
"""

# Independently spell out every contextual type as the existing source syntax.
UNTYPED = PROGRAM
for annotated, untyped in (
    ("fn(k: u64)", "fn(k)"),
    ("fn(t: List)", "fn(t)"),
    ("fn(i: u64, p: erased(Lt(i, n)), acc: List) -> List", "fn(i, p, acc)"),
    ("fn(x: i64, rest: List, ih: i64) -> i64", "fn(x, rest, ih)"),
    ("fn(x: i64, rest: ref List, ih: u64)", "fn(x, rest, ih)"),
    ("fn(i: u64, p: Lt(i, n), acc: u64) -> u64", "fn(i, p, acc)"),
    ("fn(p: erased(Lt(i, 1 + 2)))", "fn(p)"),
    ("fn(q: Eq(i, i))", "fn(q)"),
    ("fn(k: u64, p: Lt(k, 4)) -> Lt(k, 4)", "fn(k, p)"),
):
    UNTYPED = UNTYPED.replace(annotated, untyped)
for name in ("a", "b", "c", "d"):
    # Only the numeric function; signed/default arithmetic remains unannotated.
    start, rest = UNTYPED.split("export fn signed", 1)
    UNTYPED = start.replace(f"let {name} =", f"let {name}: u64 =") + "export fn signed" + rest

UNTYPED = UNTYPED.replace("fn(p: Lt(n, 3)) -> u64", "fn(p)")
UNTYPED = UNTYPED.replace("fn(q) -> Eq(n, n)", "fn(q)")
UNTYPED = UNTYPED.replace("fn(p) -> buffer(1)", "fn(p)")
UNTYPED = UNTYPED.replace("let x = if_lt(n, 3", "let x: u64 = if_lt(n, 3")
UNTYPED = UNTYPED.replace("let y = if_eq", "let y: u64 = if_eq")
UNTYPED = UNTYPED.replace("let choice =", "let choice: Choice =")
UNTYPED = UNTYPED.replace("let x = match choice", "let x: u64 = match choice")
UNTYPED = UNTYPED.replace("let x = match xs", "let x: i64 = match xs")
UNTYPED = UNTYPED.replace("let p = if_eq", "let p: Eq(n, n) = if_eq")
UNTYPED = UNTYPED.replace("let p = match e", "let p: Eq(0, 0) = match e")
UNTYPED = UNTYPED.replace("let b = match e", "let b: buffer(n) = match e")
UNTYPED = UNTYPED.replace("let v = if_lt", "let v: u64 = if_lt")
UNTYPED = UNTYPED.replace("let b = if_lt", "let b: buffer(1) = if_lt")


INVALID = {
    "mixed-left": "fn bad(n: u64, x: i64) -> i64 { let v = n + x; 0 }",
    "mixed-right": "fn bad(n: u64, x: i64) -> i64 { let v = x + n; 0 }",
    "negative-unsigned": "fn bad(n: u64) -> i64 { let v = -1 + n; 0 }",
    "unsigned-product": "fn bad(n: u64) -> i64 { let v = 2 * n; 0 }",
    "unsigned-subtraction": "fn bad(n: u64) -> i64 { let v = 2 - n; 0 }",
    "signed-overflow": "fn bad() -> i64 { let v = 9223372036854775808 + 1; v }",
    "wrong-case-domain": "fn bad() -> i64 { fold(3, 0, fn(i: i64, p, acc) { acc }) }",
    "wrong-case-result": "fn bad() -> i64 { fold(3, 0, fn(i, p, acc) -> u64 { acc }) }",
    "wrong-case-proof": "fn bad() -> i64 { fold(3, 0, fn(i, p: Lt(i, 4), acc) { acc }) }",
    "erase-runtime": "fn bad() -> i64 { fold(3, 0, fn(i: erased(u64), p, acc) { acc }) }",
    "wrong-family-domain": "fn bad() -> Eq(0, 0) { transport(fn(k: i64) { Eq(k, 0) }, refl(0), refl(0)) }",
    "erase-family": "fn bad() -> Eq(0, 0) { transport(fn(k: erased(u64)) { Eq(k, 0) }, refl(0), refl(0)) }",
    "wrong-branch-proof": "fn bad(i: u64) -> i64 { if_lt(i, 3, fn(p: Lt(i, 4)) { 0 }, 1) }",
    "proof-is-not-runtime": "fn bad(i: u64) -> i64 { if_lt(i, 3, fn(p: Lt(i, 3)) { p }, 1) }",
    "annotation-cannot-forge": "fn bad(i: u64) -> i64 { if_lt(i, 3, fn(p: Lt(i, 3)) { index([1], i, p) }, 1) }",
    "wrong-motive-domain": "enum E { A } fn bad(x: E) -> i64 { induct(fn(t: u64) { i64 }, 0, x) }",
    "duplicate-case": "fn bad() -> i64 { fold(3, 0, fn(i: u64, p, i) { 0 }) }",
    "duplicate-family": "trait P(a: u64, b: u64) { fn c() -> P(0, 0) } fn bad(p: erased(P(0, 0))) -> Eq(0, 0) { induct(fn(k: u64, k: u64) { Eq(k, k) }, refl(0), p) }",
    "duplicate-motive": "enum List { Nil; Cons(i64, List) } fn bad(xs: ref List) -> i64 { induct(fn(t: List, t: u64) { i64 }, fn(i) { 0 }, fn(x, rest, ih, i) { 0 }, xs)(0) }",
    "duplicate-motive-argument": "enum List { Nil; Cons(i64, List) } fn bad(xs: ref List) -> i64 { induct(fn(t: List, i: u64, i: u64) { i64 }, fn(i, j) { 0 }, fn(x, rest, ih, i, j) { 0 }, xs)(0, 0) }",
    "unknown-in-annotation": "fn bad() -> i64 { fold(3, 0, fn(i, p: Lt(missing, 3), acc) { acc }) }",
    # Conversion alone would erase these ill-typed sub proofs. Check the
    # source annotation first, even though it is absent from the final core.
    "invalid-parameter-evidence": "fn bad() -> i64 { load(alloc(1, 7), 0, decide_lt(0, 1), fn(x: i64, b: buffer(sub(2, 1, decide_lt(0, 1)))) { free(b, x) }) }",
    "invalid-result-evidence": "fn bad() -> buffer(1) { load(alloc(1, 7), 0, decide_lt(0, 1), fn(x, b) -> buffer(sub(2, 1, decide_lt(0, 1))) { b }) }",
    "invalid-family-evidence": "fn bad() -> Eq(0, 0) { transport(fn(k: buffer(sub(2, 1, decide_lt(0, 1)))) { Eq(0, 0) }, refl(0), refl(0)) }",
}

INVALID.update({
    "conditional-wrong-result": "fn bad(n: u64) -> i64 { if_lt(n, 3, fn(p) -> u64 { n }, 0) }",
    "conditional-ignored-annotation": "fn bad(n: u64, x: i64) -> i64 { let v = if_lt(n, 3, fn(p) -> u64 { x }, x); v }",
    "borrowed-proof-needs-context": "enum List { Cons(i64, List); Nil } fn bad(xs: ref List) -> Eq(0, 0) { let p = match xs { List.Cons(x, rest) => refl(0); List.Nil => refl(0) }; p }",
    "conditional-mixed": "fn bad(n: u64, x: i64) -> i64 { let v = if_lt(n, 3, fn(p) { n }, x); 0 }",
    "conditional-invalid-result-proof": "fn bad(n: u64) -> i64 { let v = if_lt(n, 3, fn(p) -> buffer(sub(2, 1, decide_lt(0, 1))) { alloc(1, 7) }, alloc(1, 7)); 0 }",
    "match-escaping-field": "enum E { A(u64); B } fn bad(e: E) -> i64 { let p = match e { E.A(n) => refl(n); E.B => refl(0) }; 0 }",
    "match-mixed": "enum E { A(u64); B } fn bad(e: E, x: i64) -> i64 { let v = match e { E.A(n) => n; E.B => x }; 0 }",
    "match-duplicate-inferred": "enum E { A; B } fn bad(e: E) -> i64 { let v = match e { E.A => 0; E.A => 1 }; v }",
    "match-missing-inferred": "enum E { A; B } fn bad(e: E) -> i64 { let v = match e { E.A => 0 }; v }",
})


def validate_context(compiler, root, temporary, environment, run):
    def command(action, path, *options, success=True, env=environment):
        return run([compiler, action, str(path), *options], success=success, env=env)

    path = temporary / "context.jh"
    path.write_text(PROGRAM)
    reference = temporary / "context-explicit.jh"
    reference.write_text(UNTYPED)
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable"}
    command("check", path, "--lib", env=unavailable)
    mir = command("emit-mir", path, "--lib").stdout
    assert mir == command("emit-mir", reference, "--lib").stdout
    formatted = temporary / "context-formatted.jh"
    formatted.write_text(command("fmt", path).stdout)
    assert command("emit-mir", formatted, "--lib").stdout == mir
    assert command("fmt", formatted).stdout == formatted.read_text()
    # Propositions and their annotations do not appear in runtime MIR.
    assert all(word not in mir for word in ("Lt(", "Eq(", "decide_lt", "transport"))
    counter = temporary / "context-counter.c"
    counter.write_text(COUNTER)
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            obj = temporary / f"context-{target}{level}.o"
            command("emit-obj", path, "--lib", "--target", target, level, "-o", str(obj))
            assert struct.unpack_from("<H", obj.read_bytes(), 18)[0] == machine
            if target != host:
                continue
            library = temporary / f"context{level}.so"
            run([*shlex.split(os.environ.get("JIHOO_CC", "clang")), "-shared", "-fPIC", str(obj), str(counter), "-Wl,--wrap=malloc", "-Wl,--wrap=free", "-o", str(library)])
            native = ctypes.CDLL(str(library))
            allocations = ctypes.c_long.in_dll(native, "allocations")
            frees = ctypes.c_long.in_dll(native, "frees")
            for name, arguments, result in (
                ("numeric", [ctypes.c_uint64], ctypes.c_uint64),
                ("branch", [ctypes.c_uint64], ctypes.c_uint64),
                ("matched", [ctypes.c_uint64], ctypes.c_uint64),
                ("owned_match", [ctypes.c_uint64], ctypes.c_int64),
                ("view_match", [ctypes.c_uint64], ctypes.c_int64),
                ("branch_buffer", [ctypes.c_uint64], ctypes.c_int64),
                ("outer_match", [ctypes.c_uint64], ctypes.c_int64),
                ("borrowed_branch", [ctypes.c_uint64], ctypes.c_uint64),
                ("count", [ctypes.c_uint64], ctypes.c_uint64),
                ("borrowed", [ctypes.c_uint64], ctypes.c_uint64),
                ("signed", [ctypes.c_int64], ctypes.c_int64),
                ("total", [ctypes.c_uint64, ctypes.c_int64], ctypes.c_int64),
                ("pick", [ctypes.c_uint64], ctypes.c_int64),
                ("defaults", [], ctypes.c_int64),
                ("proved", [], ctypes.c_int64),
            ):
                function = getattr(native, name)
                function.argtypes, function.restype = arguments, result
            for n in (0, 1, 7, 50):
                assert native.numeric(n) == n + 7
                assert native.branch(n) == (1 if n == 0 else 2)
                assert native.matched(n) == (n + 1 if n < 3 else 9)
                assert native.owned_match(n) == (7 if n else 0)
                assert native.view_match(n) == (7 if n else 0)
                assert native.branch_buffer(n) == (7 if n < 3 else 9)
                assert native.outer_match(n) == 7
                assert native.borrowed_branch(n) == (n if n < 3 else 9)
                assert native.count(n) == n
                assert native.borrowed(n) == 2 * n + 3
                for x in (-9, 0, 11):
                    assert native.total(n, x) == n * x
                    assert native.signed(x) == 3 * x - 1
            for n in (1 << 63, (1 << 64) - 8):
                assert native.numeric(n) == n + 7
            for i in (0, 1, 2, 3, 1 << 63, (1 << 64) - 1):
                assert native.pick(i) == ([10, 20, 30][i] if i < 3 else -1)
            assert native.defaults() == 3 and native.proved() == 3
            assert allocations.value == frees.value

    for name, body in INVALID.items():
        bad = temporary / f"context-{name}.jh"
        bad.write_text("#![dependent_core]\n" + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", bad, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert "core:" in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"context-{name}.o"
        command("emit-obj", bad, "--lib", "-o", str(obj), success=False,
                env={**environment, "JIHOO_NO_ELAB": "1"})
        assert not obj.exists()

    # New unsigned inference must retain traps, including an unused local.
    trap = temporary / "context-overflow.jh"
    for expression in (
        "18446744073709551615 + one()",
        "if_lt(0, 1, fn(p) { 18446744073709551615 + one() }, 0)",
        "match E.A { E.A => 18446744073709551615 + one(); E.B => 0 }",
    ):
        trap.write_text("#![dependent_core]\nenum E { A; B }\nfn one() -> u64 { 1 }\n"
                        f"fn main() -> i64 {{ let x = {expression}; 0 }}\n")
        for level in ("-O0", "-O2"):
            result = command("run", trap, level, success=False)
            assert result.returncode == 132, (expression, level, result.returncode, result.stderr)
    print(f"dependent context: annotated/unannotated MIR, both targets, runtime/traps and {len(INVALID)} rejections passed")
