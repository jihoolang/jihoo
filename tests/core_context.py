"""Contextual source elaboration, without new trusted-core rules."""
import ctypes
import json
import os
import platform
import shlex
import struct


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
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            obj = temporary / f"context-{target}{level}.o"
            command("emit-obj", path, "--lib", "--target", target, level, "-o", str(obj))
            assert struct.unpack_from("<H", obj.read_bytes(), 18)[0] == machine
            if target != host:
                continue
            library = temporary / f"context{level}.so"
            run([*shlex.split(os.environ.get("JIHOO_CC", "clang")), "-shared", str(obj), "-o", str(library)])
            native = ctypes.CDLL(str(library))
            for name, arguments, result in (
                ("numeric", [ctypes.c_uint64], ctypes.c_uint64),
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
    trap.write_text("#![dependent_core]\nfn one() -> u64 { 1 }\n"
                    "fn main() -> i64 { let x = 18446744073709551615 + one(); 0 }\n")
    for level in ("-O0", "-O2"):
        result = command("run", trap, level, success=False)
        assert result.returncode == 132, (level, result.returncode, result.stderr)
    print(f"dependent context: annotated/unannotated MIR, both targets, runtime/traps and {len(INVALID)} rejections passed")
