"""Declared inductive propositions, called by tests/core.py."""
import ctypes
import json
import os
import platform
import random
import re
import shlex
import struct


def validate_inductive(compiler, root, temporary, environment, run, definitions, evaluate):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    example = root / "examples/core_inductive.jh"
    core_example = root / "examples/core_inductive.jhc"
    source_text = example.read_text()
    core_text = core_example.read_text()
    prefix = source_text.split("export fn cost")[0]
    core_prefix = core_text.split("(export cost")[0]
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable",
                   "JIHOO_LD": "/unavailable"}
    command("check", example, env=unavailable)
    command("check", core_example, source=False, env=unavailable)
    mir = command("emit-mir", example, "--lib").stdout
    assert mir == command("emit-mir", core_example, source=False).stdout
    # Two real comparisons and two loads; no evidence, cases or bounds checks.
    assert mir.count("fn ") == 1 and mir.count("switch ") == 2 and mir.count("[_") == 2, mir
    for absent in ("assert", "call", "Reach", "Edge", "Lt", "Eq", "induct", "closure"):
        assert absent not in mir, (absent, mir)
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 30 and not result.stdout and not result.stderr

    # Families without indices, an uninhabited family and a family used
    # by a later one. `absurd` is accepted because Never has no constructor;
    # nothing can call it with evidence.
    extra = prefix + """
trait Ready {
    fn ready() -> Ready
}
trait Never {}
fn absurd(n: erased(Never)) -> Lt(1, 0) { induct(fn() { Lt(1, 0) }, n) }
fn ready_bound(r: erased(Ready)) -> Lt(0, 3) { induct(fn() { Lt(0, 3) }, decide_lt(0, 3), r) }
trait Walk(b: u64) {
    fn here() -> Walk(0)
    fn hop(a: u64, b: u64, w: erased(Walk(a)), seen: erased(Reach(a)), e: erased(Edge(a, b))) -> Walk(b)
}
fn walk_reach(b: u64, w: erased(Walk(b))) -> Reach(b) {
    induct(fn(x) { Reach(x) }, start(), fn(a, b, w, seen, e, ih) { step(a, b, ih, e) }, w)
}
trait Tree(n: u64) {
    fn leaf() -> Tree(0)
    fn fork(a: u64, l: erased(Tree(a)), b: u64, r: erased(Tree(b))) -> Tree(b)
}
fn tree_zero(n: u64, t: erased(Tree(n))) -> Eq(n, 0) {
    induct(fn(x) { Eq(x, 0) }, refl(0), fn(a, l, b, r, left, right) { right }, t)
}
export fn ready_cost() -> i64 { index([10, 20, 30], 0, ready_bound(ready())) }
export fn path_cost(b: u64) -> i64 {
    if_eq(b, 2, fn(e) { node(b, same(2, b, walk_reach(2, hop(0, 2, here(), start(), e02())), sym(b, 2, e))) }, -1)
}
"""
    extra_path = temporary / "inductive-extra.jh"
    extra_path.write_text(extra)
    command("check", extra_path, "--lib")
    extra_mir = command("emit-mir", extra_path, "--lib").stdout
    assert "assert" not in extra_mir and "call" not in extra_mir, extra_mir

    source_invalid = {
        "relevant-field": "trait Bad(a: u64) { fn bad(x: i64) -> Bad(0) }",
        "array-field": "trait Bad(a: u64) { fn bad(n: u64, xs: [i64; n]) -> Bad(n) }",
        "unerased-recursive": "trait Bad(a: u64) { fn bad(h: Bad(0)) -> Bad(0) }",
        "unerased-proof": "trait Bad(a: u64) { fn bad(h: Lt(0, 1)) -> Bad(0) }",
        "wrong-result": "trait Bad(a: u64) { fn bad() -> Lt(0, 1) }",
        "other-result": "trait Bad(a: u64) { fn bad() -> Edge(0, 1) }",
        "result-arity": "trait Bad(a: u64) { fn bad() -> Bad(0, 1) }",
        "field-arity": "trait Bad(a: u64) { fn bad(h: erased(Bad(0, 0))) -> Bad(0) }",
        "signed-index": "trait Bad(a: i64) { fn bad() -> Bad(0) }",
        "untyped-index": "trait Bad(a) { fn bad() -> Bad(0) }",
        "signed-result-index": "trait Bad(a: u64) { fn bad(x: i64) -> Bad(x) }",
        "body": "trait Bad(a: u64) { fn bad() -> Bad(0) { 0 } }",
        "missing-result": "trait Bad(a: u64) { fn bad() }",
        "inout-field": "trait Bad(a: u64) { fn bad(inout x: u64) -> Bad(x) }",
        "duplicate-index": "trait Bad(a: u64, a: u64) { fn bad() -> Bad(0, 0) }",
        "duplicate-field": "trait Bad(a: u64) { fn bad(x: u64, x: u64) -> Bad(x) }",
        "duplicate-constructor": "trait Bad(a: u64) { fn start() -> Bad(0) }",
        "duplicate-family": "trait Edge(a: u64) { fn bad() -> Edge(0) }",
        "family-definition": "trait node(a: u64) { fn bad() -> node(0) }",
        "constructor-definition": "fn e01() -> i64 { 0 }",
        "reserved-family": "trait index(a: u64) { fn bad() -> index(0) }",
        "reserved-constructor": "trait Bad(a: u64) { fn induct() -> Bad(0) }",
        "attribute": "#[derive(Clone)]\ntrait Bad(a: u64) { fn bad() -> Bad(0) }",
        "supertrait": "trait Bad(a: u64): Edge { fn bad() -> Bad(0) }",
        "non-constructor-item": "trait Bad(a: u64) { type Item }",
        "forward-family": "fn bad(p: erased(Later(0))) -> Lt(0, 1) { decide_lt(0, 1) }\ntrait Later(a: u64) { fn later() -> Later(0) }",
        "false-constructor": "fn bad() -> Reach(2) { step(0, 2, start(), e01()) }",
        "false-index": "fn bad() -> Edge(1, 0) { e01() }",
        "partial-constructor": "fn bad() -> Reach(1) { step(0, 1, start()) }",
        "extra-field": "fn bad() -> Edge(0, 1) { e01(0) }",
        "bare-constructor": "fn bad() -> Reach(0) { start }",
        "family-value": "fn bad() -> Reach(0) { Reach(0) }",
        "missing-case": "fn bad(r: erased(Reach(1))) -> Lt(1, 3) { induct(fn(x) { Lt(x, 3) }, decide_lt(0, 3), fn(a, b, r, e, ih) { edge_bound(a, b, e) }, r) }",
        "extra-case": "fn bad(e: erased(Edge(0, 1))) -> Lt(1, 3) { induct(fn(x, y) { Lt(y, 3) }, decide_lt(1, 3), decide_lt(2, 3), decide_lt(2, 3), decide_lt(2, 3), e) }",
        "false-case": "fn bad(b: u64, r: erased(Reach(b))) -> Lt(b, 3) { induct(fn(x) { Lt(x, 3) }, decide_lt(0, 3), fn(a, b, r, e, ih) { edge_bound(a, b, e) }, fn(a, b, r, e, ih) { ih }, r) }",
        "wrong-edge-case": "fn bad(a: u64, b: u64, e: erased(Edge(a, b))) -> Lt(b, 2) { induct(fn(x, y) { Lt(y, 2) }, decide_lt(1, 2), decide_lt(1, 2), decide_lt(1, 2), e) }",
        "forged-hypothesis": "fn wrong(a: u64, b: u64, r: erased(Reach(a)), e: erased(Eq(a, b)), ih: erased(Lt(b, 3))) -> Lt(b, 3) { ih }\nfn bad(b: u64, r: erased(Reach(b))) -> Lt(b, 3) { induct(fn(x) { Lt(x, 3) }, decide_lt(0, 3), fn(a, b, r, e, ih) { edge_bound(a, b, e) }, wrong, r) }",
        "case-arity": "fn bad(b: u64, r: erased(Reach(b))) -> Lt(b, 3) { induct(fn(x) { Lt(x, 3) }, decide_lt(0, 3), fn(a, b, r, e) { edge_bound(a, b, e) }, fn(a, b, r, e, ih) { transport(fn(k) { Lt(k, 3) }, e, ih) }, r) }",
        "case-scope": "fn bad(b: u64, r: erased(Reach(b))) -> Lt(b, 3) { induct(fn(x) { Lt(x, 3) }, decide_lt(0, 3), fn(a, b, r, e, ih) { edge_bound(a, b, e) }, fn(a, b, r, e, ih) { transport(fn(k) { Lt(k, 3) }, e, ih) }, ih) }",
        "motive-arity": "fn bad(b: u64, r: erased(Reach(b))) -> Lt(b, 3) { induct(fn(x, y) { Lt(x, 3) }, decide_lt(0, 3), fn(a, b, r, e, ih) { edge_bound(a, b, e) }, fn(a, b, r, e, ih) { transport(fn(k) { Lt(k, 3) }, e, ih) }, r) }",
        "data-motive": "export fn bad() -> u64 { induct(fn(x) { u64 }, 0, fn(a, b, r, e, ih) { 0 }, fn(a, b, r, e, ih) { 0 }, start()) }",
        "wrong-family": "fn bad(e: erased(Eq(0, 0))) -> Lt(0, 3) { induct(fn(x) { Lt(x, 3) }, decide_lt(0, 3), e) }",
        "runtime-evidence": "fn bad(r: erased(Reach(0))) -> u64 { r }",
        "runtime-condition": "fn bad(r: erased(Reach(0))) -> i64 { if_eq(r, 0, fn(e) { 0 }, 1) }",
        "relevant-parameter": "fn bad(r: Reach(0)) -> i64 { 0 }",
        "unreachable-node": "fn bad() -> Lt(3, 3) { reach_bound(3, step(2, 3, at_two(), e12())) }",
        "hidden-false-evidence": "fn ignore(r: erased(Reach(3))) -> i64 { 7 }\nexport fn bad() -> i64 { ignore(same(2, 3, at_two(), refl(2))) }",
        "dead-branch": "export fn bad() -> i64 { if_eq(0, 0, fn(e) { 7 }, node(3, step(2, 3, at_two(), e12()))) }",
        "foreign-precondition": "export fn bad(r: erased(Reach(0))) -> i64 { 1 }",
        "foreign-result": "export fn bad() -> Reach(0) { start() }",
        "swapped-hypotheses": "trait Tree(n: u64) { fn leaf() -> Tree(0)\n fn fork(a: u64, l: erased(Tree(a)), b: u64, r: erased(Tree(b))) -> Tree(b) }\nfn bad(n: u64, t: erased(Tree(n))) -> Eq(n, 0) { induct(fn(x) { Eq(x, 0) }, refl(0), fn(a, l, b, r, left, right) { left }, t) }",
        "recursive-case": "fn bad(b: u64, r: erased(Reach(b))) -> Lt(b, 3) { induct(fn(x) { Lt(x, 3) }, decide_lt(0, 3), fn(a, c, s, e, ih) { bad(a, s) }, fn(a, c, s, e, ih) { transport(fn(k) { Lt(k, 3) }, e, ih) }, r) }",
    }
    for name, body in source_invalid.items():
        path = temporary / f"inductive-{name}.jh"
        path.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert str(path) in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"inductive-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False,
                env={**environment, "JIHOO_NO_ELAB": "1"})
        assert not obj.exists()

    # Strict positivity and the other declaration rules, also for shapes
    # the source subset cannot spell, such as a family under an arrow.
    core_invalid = {
        "negative": "(inductive Bad 0 (bad (pi0 h (pi0 x Bad (Lt 0 1)) Bad)))",
        "positive-arrow": "(inductive Bad 0 (bad (pi0 h (pi0 x (Lt 0 1) Bad) Bad)))",
        "relevant-field": "(inductive Bad 0 (bad (pi x I64 Bad)))",
        "array-field": "(inductive Bad 0 (bad (pi x (Array 1) Bad)))",
        "type-field": "(inductive Bad 0 (bad (pi x (Type 0) Bad)))",
        "unerased-recursive": "(inductive Bad 0 (bad (pi h Bad Bad)))",
        "wrong-result": "(inductive Bad 0 (bad (Lt 0 1)))",
        "other-result": "(inductive Bad 0 (bad (Edge 0 1)))",
        "result-arity": "(inductive Bad 1 (bad (Bad 0 1)))",
        "forward-family": "(def early (pi0 p (Later 0) U64) (lam0 p (Later 0) 0)) (inductive Later 1 (later (Later 0)))",
        "false-constructor": "(def bad (Reach 2) (step 0 2 start e01))",
        "partial-constructor": "(def bad (Reach 1) (step 0 1 start))",
        "extra-field": "(def bad (Edge 0 1) (e01 0))",
        "missing-case": "(def bad (Lt 0 3) (induct Reach (lam x U64 (Lt x 3)) (decide-lt 0 3) start))",
        "wrong-family": "(def bad (Lt 0 3) (induct Edge (lam x U64 (lam y U64 (Lt x 3))) (decide-lt 0 3) (decide-lt 1 3) (decide-lt 0 3) start))",
        "data-motive": "(export bad U64 (induct Reach (lam x U64 U64) 0 (lam a U64 (lam b U64 (lam0 r (Reach a) (lam0 e (Edge a b) (lam0 ih U64 0))))) (lam a U64 (lam b U64 (lam0 r (Reach a) (lam0 e (Eq a b) (lam0 ih U64 0))))) start))",
        "forged-hypothesis": "(def bad (pi b U64 (pi0 r (Reach b) (Lt b 3))) (lam b U64 (lam0 r (Reach b) (induct Reach (lam x U64 (Lt x 3)) (decide-lt 0 3) (lam a U64 (lam b U64 (lam0 r (Reach a) (lam0 e (Edge a b) (lam0 ih (Lt b 3) ih))))) (lam a U64 (lam b U64 (lam0 r (Reach a) (lam0 e (Eq a b) (lam0 ih (Lt b 3) ih))))) r))))",
        "runtime-evidence": "(def bad (pi0 r (Reach 0) U64) (lam0 r (Reach 0) r))",
        "relevant-parameter": "(def bad (pi r (Reach 0) I64) (lam r (Reach 0) (int 0)))",
        "dead-branch": "(export bad I64 (if-eq 0 0 e (int 7) (app node 3 (step 2 3 at_two e12))))",
    }
    # Constructor types are checked after normalization: an occurrence
    # that beta reduction removes is no occurrence.
    reducible = temporary / "inductive-reducible.jhc"
    reducible.write_text(core_prefix + "(inductive Ok 1 (ok (pi0 h (Ok 0) (Ok (app (lam x Prop 0) (Ok 0))))))\n"
                         "(export good I64 (int 0))\n")
    command("check", reducible, source=False)
    deep = "start"
    for _ in range(150):
        deep = f"(same 0 0 {deep} (refl 0))"
    core_invalid["resource-limit"] = f"(def bad (Reach 0) {deep})"
    for name, body in core_invalid.items():
        path = temporary / f"inductive-{name}.jhc"
        path.write_text(core_prefix + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert "core:" in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"inductive-core-{name}.o"
        command("emit-obj", path, "-o", str(obj), source=False, success=False)
        assert not obj.exists()

    reference = {}
    for _, name, _, body in definitions(core_text):
        reference[name] = evaluate(body, reference.copy())
    rng = random.Random(0x1ADC)
    values = [0, 1, 2, 3, 4, (1 << 63) - 1, 1 << 63, (1 << 64) - 1,
              *(rng.getrandbits(64) for _ in range(16))]
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    formatted = temporary / "inductive-formatted.jh"
    formatted.write_text(command("fmt", example).stdout)
    assert mir == command("emit-mir", formatted, "--lib").stdout
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            for is_source, suffix in ((True, "jh"), (False, "jhc")):
                obj = temporary / f"inductive-{target}{level}-{suffix}.o"
                options = ["--lib"] if is_source else []
                command("emit-obj", example if is_source else core_example, *options,
                        "--target", target, level, "-o", str(obj), source=is_source)
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                library = temporary / f"inductive{level}-{suffix}.so"
                cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
                run([*cc, "-shared", str(obj), "-o", str(library)])
                native = ctypes.CDLL(str(library))
                native.cost.argtypes = [ctypes.c_uint64]
                native.cost.restype = ctypes.c_int64
                for b in values:
                    expected = reference["cost"](b)
                    assert expected == (30 if b == 2 else 20 if b == 1 else -1)
                    assert native.cost(b) == expected, b
    extra_obj = temporary / "inductive-extra.o"
    command("emit-obj", extra_path, "--lib", "-o", str(extra_obj))
    extra_library = temporary / "inductive-extra.so"
    run([*shlex.split(os.environ.get("JIHOO_CC", "clang")), "-shared", str(extra_obj),
         "-o", str(extra_library)])
    native = ctypes.CDLL(str(extra_library))
    native.ready_cost.restype = ctypes.c_int64
    native.path_cost.argtypes = [ctypes.c_uint64]
    native.path_cost.restype = ctypes.c_int64
    assert native.ready_cost() == 10
    for b in values:
        assert native.path_cost(b) == (30 if b == 2 else -1), b
    print(f"declared inductives: paired source/core execution, strict positivity, erased induction, {len(source_invalid)} source and {len(core_invalid)} core rejections passed")
