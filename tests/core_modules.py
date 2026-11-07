"""Dependent-module identity, public interfaces and private representation boundaries."""
import ctypes
import json
import os
import platform
import shlex
import struct

from core_buffer import COUNTER

LIBRARY = """#![dependent_core]
fn helper(x: i64) -> i64 { x + OFFSET }
fn main() -> i64 { 99 }
pub enum Choice { Value(i64); Empty }
pub fn make(x: i64) -> Choice { Choice.Value(helper(x)) }
pub fn read(x: Choice) -> i64 { match x { Value(v) => v; Empty => -1 } }
pub enum List { Nil; Cons(i64, List) }
pub fn list(x: i64) -> List { List.Cons(x, List.Nil) }
pub fn sum(xs: ref List) -> i64 { induct(fn(t) { i64 }, 0, fn(x, rest, ih) { x + ih }, xs) }
pub trait P(n: u64) { fn evidence(n: u64) -> P(n) }
pub fn accept(n: u64, p: erased(P(n))) -> u64 { n }
pub struct Box { pub visible: i64, secret: i64, data: buffer(1) }
pub fn box(x: i64) -> Box { Box { visible: x, secret: OFFSET, data: alloc(1, x) } }
pub fn inspect(x: ref Box) -> i64 { match x { Box { visible, secret, .. } => visible + secret } }
pub struct Open { pub x: i64, pub y: i64 }
enum Hidden { Wrap(i64) }
pub fn opaque(x: i64) -> Hidden { Hidden.Wrap(x) }
pub fn unwrap(x: Hidden) -> i64 { match x { Wrap(v) => v } }
trait HiddenProof { fn private_evidence() -> HiddenProof }
pub fn opaque_proof() -> HiddenProof { private_evidence() }
pub fn use_proof(p: erased(HiddenProof)) -> i64 { 7 }
pub export fn ABI() -> i64 { OFFSET }
"""

ROOT = """#![dependent_core]
IMPORTS
fn helper(x: i64) -> i64 { x + 30 }
fn read_a(x: a.Choice) -> i64 { match x { a.Choice.Value(v) => v; a.Choice.Empty => -1 } }
export fn combined(x: i64) -> i64 {
    let first: a.Choice = a.make(x)
    let second: b.Choice = b.make(x)
    read_a(first) + b.read(second) + helper(x)
}
export fn partial(x: i64) -> i64 {
    let first = a.box(x)
    let second = b.box(x)
    let extra = b.inspect(second)
    match first { a.Box { visible, .. } => visible + extra }
}
export fn lists(x: i64) -> i64 {
    let first = a.list(x)
    let second = b.list(x + 1)
    let left = a.sum(first)
    let right = b.sum(second)
    left + right
}
export fn opaque(x: i64) -> i64 { a.unwrap(a.opaque(x)) + a.use_proof(a.opaque_proof()) }
export fn refinement(n: u64) -> u64 {
    let x: refine(fn(k) { a.P(k) }) = pack(n, a.evidence(n))
    a.accept(witness(x), transport(fn(k) { a.P(k) }, refl(witness(x)), proof(x)))
}
export fn alias_proof(n: u64) -> u64 { other.accept(n, a.evidence(n)) }
export fn bridged() -> i64 { bridge.through() }
fn main() -> i64 { combined(2) + partial(2) + lists(2) + opaque(2) - 104 }
"""

INVALID = {
    "private-function": ("fn bad() -> i64 { a.helper(1) }", "unknown name"),
    "unqualified-import": ("fn bad() -> i64 { only_a() }", "unknown name"),
    "wrong-module-function": ("fn bad() -> i64 { b.only_a() }", "unknown name"),
    "wrong-module-type": ("fn bad(x: b.OnlyA) -> i64 { 0 }", "unsupported type"),
    "wrong-module-proof": ("fn bad() -> b.Truth { b.fact() }", "unsupported type"),
    "qualified-builtin": ("fn bad(n: a.u64) -> i64 { 0 }", "unsupported type"),
    "private-type": ("fn bad(x: a.Hidden) -> i64 { 0 }", "unsupported type"),
    "private-constructor": ("fn bad() -> i64 { a.use_proof(a.private_evidence()) }", "unknown name"),
    "cross-family": ("fn bad(n: u64) -> u64 { a.accept(n, b.evidence(n)) }", "type mismatch"),
    "cross-data": ("fn bad() -> i64 { a.read(b.make(1)) }", "type mismatch"),
    "wrong-qualified-pattern": ("fn bad(x: a.Choice) -> i64 { match x { b.Choice.Value(v) => v; Empty => 0 } }", "match has no arm"),
    "local-family-pattern": ("enum Choice { Value(i64); Empty } fn bad(x: a.Choice) -> i64 { match x { Choice.Value(v) => v; Empty => 0 } }", "match has no arm"),
    "wrong-struct-pattern": ("fn bad(x: a.Box) -> i64 { match x { b.Box { visible, .. } => visible } }", "match has no arm"),
    "unknown-pattern-module": ("fn bad(x: a.Box) -> i64 { match x { missing.Box { visible, .. } => visible } }", "match has no arm"),
    "private-construction": ("fn bad() -> a.Box { a.Box { visible: 1, secret: 2, data: alloc(1, 0) } }", "private struct field"),
    "positional-construction": ("fn bad() -> a.Box { a.Box.Box(1, 2, alloc(1, 0)) }", "private struct field"),
    "private-pattern": ("fn bad(x: a.Box) -> i64 { match x { a.Box { secret, .. } => secret } }", "private struct field"),
    "private-wildcard-pattern": ("fn bad(x: a.Box) -> i64 { match x { a.Box { secret: _, .. } => 0 } }", "private struct field"),
    "positional-pattern": ("fn bad(x: a.Box) -> i64 { match x { a.Box.Box(v, secret, data) => secret } }", "struct pattern uses named fields"),
    "private-induction": ("fn bad(x: a.Box) -> i64 { induct(fn(t) { i64 }, fn(v, secret, data) { secret }, x) }", "private struct field"),
    "private-borrowed-induction": ("fn bad(x: ref a.Box) -> i64 { induct(fn(t) { i64 }, fn(v, secret, data) { secret }, x) }", "private struct field"),
    "opaque-match": ("fn bad() -> i64 { let x = a.opaque(3); match x { Wrap(v) => v } }", "private type"),
    "opaque-induction": ("fn bad() -> i64 { let x = a.opaque(3); induct(fn(t) { i64 }, fn(v) { v }, x) }", "private type"),
    "opaque-proof-induction": ("fn bad() -> Eq(0, 0) { induct(fn() { Eq(0, 0) }, refl(0), a.opaque_proof()) }", "private type"),
    "wildcard-value": ("fn bad(x: a.Box) -> i64 { match x { a.Box { .. } => free(_, 0) } }", "discarded binding"),
    "wildcard-borrow": ("fn bad(x: a.Box) -> i64 { match x { a.Box { .. } => index(_, 0, decide_lt(0, 1)) } }", "discarded binding"),
    "wildcard-old": ("fn bad(x: ref a.Box) -> Eq(0, 0) { match x { a.Box { .. } => refl(old(_)) } }", "unknown name"),
    "unknown-field": ("fn bad(x: a.Open) -> i64 { match x { a.Open { missing: _, .. } => 0 } }", "unknown struct pattern field"),
    "duplicate-field": ("fn bad(x: a.Open) -> i64 { match x { a.Open { x: first, x: second, .. } => first } }", "duplicate struct pattern field"),
    "shadowed-import": ("fn bad() -> i64 { let a = 1; a.only_a() }", "calls require a named function"),
    "alias-definition-collision": ("fn a() -> i64 { 0 }", "duplicate definition"),
}


def validate_modules(compiler, root, temporary, environment, run):
    directory = temporary / "dependent-modules"
    directory.mkdir()
    (directory / "a.jh").write_text(LIBRARY.replace("OFFSET", "10").replace("ABI", "abi_a") + """
pub fn only_a() -> i64 { 11 }
pub enum OnlyA { Unique }
pub trait Truth { fn fact() -> Truth }
""")
    (directory / "b.jh").write_text(LIBRARY.replace("OFFSET", "20").replace("ABI", "abi_b"))
    (directory / "bridge.jh").write_text("#![dependent_core]\npub import a\npub fn through() -> i64 { a.only_a() }\n")

    def command(action, path, *options, success=True, env=environment):
        return run([compiler, action, str(path), *options], success=success, env=env)

    counter = directory / "counter.c"
    counter.write_text(COUNTER)
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable"}
    for order, imports in enumerate(("import a\nimport b\nimport a as other\nimport bridge", "import b\nimport a as other\nimport a\nimport bridge")):
        path = directory / f"main-{order}.jh"
        path.write_text(ROOT.replace("IMPORTS", imports))
        command("check", path, env=unavailable)
        for target, machine in (("x86_64", 62), ("aarch64", 183)):
            for level in ("-O0", "-O2"):
                obj = directory / f"modules-{order}-{target}{level}.o"
                command("emit-obj", path, "--lib", "--target", target, level, "-o", str(obj))
                assert struct.unpack_from("<H", obj.read_bytes(), 18)[0] == machine
                if target != host:
                    continue
                library = directory / f"modules-{order}{level}.so"
                run([*shlex.split(os.environ.get("JIHOO_CC", "clang")), "-shared", "-fPIC", str(obj),
                     str(counter), "-Wl,--wrap=malloc", "-Wl,--wrap=free", "-o", str(library)])
                native = ctypes.CDLL(str(library))
                allocations = ctypes.c_long.in_dll(native, "allocations")
                frees = ctypes.c_long.in_dll(native, "frees")
                for name in ("combined", "partial", "lists", "opaque"):
                    function = getattr(native, name)
                    function.argtypes, function.restype = [ctypes.c_int64], ctypes.c_int64
                for name in ("refinement", "alias_proof"):
                    function = getattr(native, name)
                    function.argtypes, function.restype = [ctypes.c_uint64], ctypes.c_uint64
                for x in (-20, 0, 2, 40):
                    assert native.combined(x) == 3 * x + 60
                    assert native.partial(x) == 2 * x + 20
                    assert native.lists(x) == 2 * x + 1
                    assert native.opaque(x) == x + 7
                    assert allocations.value == frees.value
                for n in (0, 1, 1 << 63, (1 << 64) - 1):
                    assert native.refinement(n) == n and native.alias_proof(n) == n
                assert native.abi_a() == 10 and native.abi_b() == 20
                assert native.bridged() == 11
        for level in ("-O0", "-O2"):
            command("run", path, level)
        formatted = directory / f"formatted-{order}.jh"
        formatted.write_text(command("fmt", path).stdout)
        assert command("emit-mir", path, "--lib").stdout == command("emit-mir", formatted, "--lib").stdout

    rejected = dict(INVALID)
    for name, expression in (
        ("transitive-qualified", "bridge.only_a()"),
        ("transitive-bare", "only_a()"),
        ("transitive-alias", "a.only_a()"),
        ("transitive-reexport", "bridge.a.only_a()"),
    ):
        rejected[name] = ("import bridge\nfn bad() -> i64 { " + expression + " }", None)
    for name, body in (
        ("duplicate-alias", "import a as x\nimport b as x"),
        ("reserved-alias", "import a as u64"),
    ):
        rejected[name] = (body, "duplicate or reserved import alias")
    (directory / "export_a.jh").write_text("#![dependent_core]\nexport fn duplicate() -> i64 { 1 }\n")
    (directory / "export_b.jh").write_text("#![dependent_core]\nexport fn duplicate() -> i64 { 2 }\n")
    rejected["duplicate-symbol"] = ("import export_a\nimport export_b", "duplicate exported symbol")
    for name, (body, expected) in rejected.items():
        bad = directory / f"bad-{name}.jh"
        prefix = "#![dependent_core]\n" + ("" if name.startswith("transitive-") else "import a\nimport b\n")
        bad.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", bad, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        if expected:
            assert expected in diagnostic.stderr, (name, diagnostic.stderr)
        obj = directory / f"bad-{name}.o"
        command("emit-obj", bad, "--lib", "-o", str(obj), success=False,
                env={**environment, "JIHOO_NO_ELAB": "1"})
        assert not obj.exists()
    print(f"dependent modules: alias identity, both targets, privacy, counted frees and {len(rejected)} rejections passed")
