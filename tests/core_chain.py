"""Indexed proof construction/induction tests, called by tests/core.py."""
import ctypes
import json
import os
import platform
import random
import re
import shlex
import struct


def validate_chain(compiler, root, temporary, environment, run, read_terms, evaluate):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    example = root / "examples/core_chain.jh"
    core_example = root / "examples/core_chain.jhc"
    source_text = example.read_text()
    core_text = core_example.read_text()
    prefix = source_text.split("export fn lookup")[0]
    core_prefix = core_text.split("(export lookup")[0]
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable",
                   "JIHOO_LD": "/unavailable"}
    command("check", example, env=unavailable)
    command("check", core_example, source=False, env=unavailable)
    mir = command("emit-mir", example, "--lib").stdout
    assert mir == command("emit-mir", core_example, source=False).stdout
    assert mir.count("fn ") == 1 and len(re.findall(r"let mut", mir)) == 13, mir
    assert mir.count("switch ") == 3 and mir.count("[_") == 1, mir
    for absent in ("assert", "call", "Eq", "Lt", "chain", "transport", "closure"):
        assert absent not in mir, (absent, mir)
    llvm = command("emit-llvm", example, "--lib").stdout
    lookup = re.search(r'define[^\n]*@"?lookup"?\([^\n]*\).*?\n}', llvm, re.S)
    assert lookup and re.search(r'@"?lookup"?\(i64[^,)]*, i64[^,)]*, i64[^,)]*\)', lookup[0]), llvm
    assert "malloc" not in lookup[0] and "panic" not in lookup[0]
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 22 and not result.stdout and not result.stderr

    source_invalid = {
        "false-refl": "fn bad() -> EqChain(0, 1) { chain_refl(0) }",
        "false-edge": "fn bad() -> EqChain(0, 1) { chain_step(0, 1, 1, refl(0), chain_refl(1)) }",
        "wrong-tail": "fn bad() -> EqChain(0, 0) { chain_step(0, 0, 0, refl(0), chain_refl(1)) }",
        "wrong-result": "fn bad() -> EqChain(0, 1) { chain_step(0, 0, 0, refl(0), chain_refl(0)) }",
        "wrong-edge-sort": "fn bad() -> EqChain(0, 0) { chain_step(0, 0, 0, decide_lt(0, 1), chain_refl(0)) }",
        "wrong-tail-sort": "fn bad() -> EqChain(0, 0) { chain_step(0, 0, 0, refl(0), refl(0)) }",
        "signed-index": "fn bad(i: i64) -> EqChain(0, 0) { chain_refl(i) }",
        "relevant": "fn bad(p: EqChain(0, 0)) -> i64 { 0 }",
        "runtime": "fn bad(p: erased(EqChain(0, 0))) -> i64 { p }",
        "runtime-condition": "fn bad(p: erased(EqChain(0, 0))) -> i64 { if_eq(p, 0, fn(e) { 0 }, 1) }",
        "motive-data": "export fn bad() -> u64 { chain_induct(fn(x, y) { u64 }, chain_base, chain_case, chain_refl(0)) }",
        "motive-unary": "fn bad() -> Eq(0, 0) { chain_induct(fn(x) { Eq(x, x) }, chain_base, chain_case, chain_refl(0)) }",
        "motive-duplicate": "fn bad() -> Eq(0, 0) { chain_induct(fn(x, x) { Eq(x, x) }, chain_base, chain_case, chain_refl(0)) }",
        "motive-scope": "fn bad() -> Eq(0, 0) { chain_induct(fn(x, y) { Eq(x, y) }, fn(a) { refl(x) }, chain_case, chain_refl(0)) }",
        "wrong-proof-sort": "fn bad() -> Eq(0, 0) { chain_induct(fn(x, y) { Eq(x, y) }, chain_base, chain_case, refl(0)) }",
        "wrong-base": "fn wrong_base(a: u64) -> Eq(0, 0) { refl(0) }\nfn bad() -> Eq(0, 0) { chain_induct(fn(x, y) { Eq(x, y) }, wrong_base, chain_case, chain_refl(0)) }",
        "unused-step": "fn bad() -> Eq(0, 0) { chain_induct(fn(x, y) { Eq(x, y) }, chain_base, fn(a, b, c, e, tail, ih) { refl(1) }, chain_refl(0)) }",
        "forged-hypothesis": "fn wrong_step(a: u64, b: u64, c: u64, e: erased(Eq(a, b)), tail: erased(EqChain(b, c)), ih: erased(Eq(a, c))) -> Eq(a, c) { ih }\nfn bad() -> Eq(0, 0) { chain_induct(fn(x, y) { Eq(x, y) }, chain_base, wrong_step, chain_refl(0)) }",
        "wrong-tail-domain": "fn wrong_step(a: u64, b: u64, c: u64, e: erased(Eq(a, b)), tail: erased(EqChain(a, c)), ih: erased(Eq(b, c))) -> Eq(a, c) { trans(a, b, c, e, ih) }\nfn bad() -> Eq(0, 0) { chain_induct(fn(x, y) { Eq(x, y) }, chain_base, wrong_step, chain_refl(0)) }",
        "runtime-hypothesis": "fn bad() -> Eq(0, 0) { chain_induct(fn(x, y) { Eq(x, y) }, chain_base, fn(a, b, c, e, tail, ih) { if_eq(ih, 0, fn(q) { refl(0) }, refl(0)) }, chain_refl(0)) }",
        "wrong-case-arity": "fn bad() -> Eq(0, 0) { chain_induct(fn(x, y) { Eq(x, y) }, chain_base, fn(a, b, c, e, tail) { chain_eq(a, c, chain_step(a, b, c, e, tail)) }, chain_refl(0)) }",
        "case-scope": "fn bad() -> Eq(0, 0) { chain_induct(fn(x, y) { Eq(x, y) }, chain_base, fn(a, b, c, e, tail, ih) { ih }, tail) }",
        "recursive-case": "fn bad(a: u64, b: u64, p: erased(EqChain(a, b))) -> Eq(a, b) { chain_induct(fn(x, y) { Eq(x, y) }, chain_base, fn(x, y, z, e, tail, ih) { bad(x, z, p) }, p) }",
        "hidden-false-tail": "fn ignore(p: erased(EqChain(0, 1))) -> i64 { 7 }\nexport fn bad() -> i64 { ignore(chain_step(0, 0, 1, refl(0), chain_refl(0))) }",
        "dead-branch": "export fn bad() -> i64 { if_eq(0, 0, fn(e) { 7 }, index([1], 0, transport(fn(k) { Lt(k, 1) }, chain_eq(0, 1, chain_refl(0)), decide_lt(0, 1)))) }",
        "foreign-precondition": "export fn bad(p: erased(EqChain(0, 0))) -> i64 { 1 }",
        "foreign-result": "export fn bad() -> EqChain(0, 0) { chain_refl(0) }",
    }
    for name, body in source_invalid.items():
        path = temporary / f"chain-{name}.jh"
        path.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr)
        assert "core:" in diagnostic.stderr and str(path) in diagnostic.stderr, diagnostic.stderr
        obj = temporary / f"chain-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False,
                env={**environment, "JIHOO_NO_ELAB": "1"})
        assert not obj.exists()

    core_invalid = {
        "false-refl": "(def bad (EqChain 0 1) (chain-refl 0))",
        "false-edge": "(def bad (EqChain 0 1) (chain-step 0 1 1 (refl 0) (chain-refl 1)))",
        "wrong-tail": "(def bad (EqChain 0 0) (chain-step 0 0 0 (refl 0) (chain-refl 1)))",
        "wrong-result": "(def bad (EqChain 0 1) (chain-step 0 0 0 (refl 0) (chain-refl 0)))",
        "wrong-edge-sort": "(def bad (EqChain 0 0) (chain-step 0 0 0 (decide-lt 0 1) (chain-refl 0)))",
        "wrong-tail-sort": "(def bad (EqChain 0 0) (chain-step 0 0 0 (refl 0) (refl 0)))",
        "signed-refl": "(def bad (EqChain 0 0) (chain-refl (int 0)))",
        "signed-index": "(def bad (EqChain (int 0) 0) (chain-refl 0))",
        "relevant": "(def bad (pi p (EqChain 0 0) I64) (lam p (EqChain 0 0) (int 0)))",
        "runtime": "(def bad (pi0 p (EqChain 0 0) I64) (lam0 p (EqChain 0 0) p))",
        "data-motive": "(export bad U64 (chain-induct (lam x U64 (lam y U64 U64)) chain_base chain_case (chain-refl 0)))",
        "universe-motive": "(def bad (Type 0) (chain-induct (lam x U64 (lam y U64 (Type 0))) chain_base chain_case (chain-refl 0)))",
        "wrong-proof-sort": "(def bad (Eq 0 0) (chain-induct (lam x U64 (lam y U64 (Eq x y))) chain_base chain_case (refl 0)))",
        "wrong-base": "(def bad (Eq 0 0) (chain-induct (lam x U64 (lam y U64 (Eq x y))) (lam a U64 (refl 0)) chain_case (chain-refl 0)))",
        "unused-step": "(def bad (Eq 0 0) (chain-induct (lam x U64 (lam y U64 (Eq x y))) chain_base 0 (chain-refl 0)))",
        "forged-hypothesis": "(def wrong_step (pi a U64 (pi b U64 (pi c U64 (pi0 e (Eq a b) (pi0 tail (EqChain b c) (pi0 ih (Eq a c) (Eq a c))))))) (lam a U64 (lam b U64 (lam c U64 (lam0 e (Eq a b) (lam0 tail (EqChain b c) (lam0 ih (Eq a c) ih)))))))\n(def bad (Eq 0 0) (chain-induct (lam x U64 (lam y U64 (Eq x y))) chain_base wrong_step (chain-refl 0)))",
        "dead-branch": "(export bad I64 (if-eq 0 0 e (int 7) (index (array (int 1)) 0 (transport (lam k U64 (Lt k 1)) (app chain_eq 0 1 (chain-refl 0)) (decide-lt 0 1)))))",
    }
    # Resource exhaustion must reject deep proof constructors, not truncate
    # a chain or replace an unchecked induction by a trusted theorem.
    deep = "(chain-refl 0)"
    for _ in range(150):
        deep = f"(chain-step 0 0 0 (refl 0) {deep})"
    core_invalid["resource-limit"] = f"(def bad (EqChain 0 0) {deep})"
    for name, body in core_invalid.items():
        path = temporary / f"chain-{name}.jhc"
        path.write_text(core_prefix + body)
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr)
        assert "core:" in diagnostic.stderr
        obj = temporary / f"chain-core-{name}.o"
        command("emit-obj", path, "-o", str(obj), source=False, success=False)
        assert not obj.exists()

    source = source_text.split("fn main()")[0]
    core_source = core_text
    names = []
    for length in (0, 1, 4):
        name = f"long_{length}"
        names.append(name)
        proof, core_proof = "chain_refl(i)", "(chain-refl i)"
        for _ in range(length):
            proof = f"chain_step(i, i, i, refl(i), {proof})"
            core_proof = f"(chain-step i i i (refl i) {core_proof})"
        source += f"export fn {name}(i: u64) -> i64 {{ if_lt(i, 3, fn(p) {{ get(3, [11, 22, 33], i, transport(fn(k) {{ Lt(k, 3) }}, chain_eq(i, i, {proof}), p)) }}, -1) }}\n"
        core_source += f"(export {name} (pi i U64 I64) (lam i U64 (if-lt i 3 p (app get 3 (array (int 11) (int 22) (int 33)) i (transport (lam k U64 (Lt k 3)) (app chain_eq i i {core_proof}) p)) (int -1))))\n"
    path = temporary / "chain-program.jh"
    core_path = temporary / "chain-program.jhc"
    path.write_text(source)
    core_path.write_text(core_source)

    # Captured endpoints/evidence test weakening under all six step
    # binders. Clone uses a different proposition family, EqChain itself.
    capture_source = prefix + """
fn keep(i: u64, n: u64, a: u64, b: u64, p: erased(Lt(i, n)), q: erased(EqChain(a, b))) -> Lt(i, n) {
    chain_induct(fn(x, y) { Lt(i, n) }, fn(x) { p }, fn(x, y, z, e, tail, ih) { ih }, q)
}
fn clone(a: u64, b: u64, p: erased(EqChain(a, b))) -> EqChain(a, b) {
    chain_induct(fn(x, y) { EqChain(x, y) }, fn(x) { chain_refl(x) },
        fn(x, y, z, e, tail, ih) { chain_step(x, y, z, e, ih) }, p)
}
export fn captured(i: u64) -> i64 {
    if_lt(i, 3, fn(p) { get(3, [11, 22, 33], i, keep(i, 3, i, i, p, chain_step(i, i, i, refl(i), chain_refl(i)))) }, -1)
}
export fn cloned(n: u64, i: u64) -> i64 {
    if_eq(n, 3, fn(e) { if_lt(i, n, fn(p) {
        get(3, [11, 22, 33], i, transport(fn(k) { Lt(i, k) },
            chain_eq(n, 3, clone(n, 3, chain_step(n, 3, 3, e, chain_refl(3)))), p))
    }, -1) }, -2)
}
"""
    capture_core = core_prefix + """
(def keep (pi i U64 (pi n U64 (pi a U64 (pi b U64 (pi0 p (Lt i n) (pi0 q (EqChain a b) (Lt i n)))))))
 (lam i U64 (lam n U64 (lam a U64 (lam b U64 (lam0 p (Lt i n) (lam0 q (EqChain a b)
  (chain-induct (lam x U64 (lam y U64 (Lt i n))) (lam x U64 p)
   (lam x U64 (lam y U64 (lam z U64 (lam0 e (Eq x y) (lam0 tail (EqChain y z) (lam0 ih (Lt i n) ih)))))) q))))))))
(def clone (pi a U64 (pi b U64 (pi0 p (EqChain a b) (EqChain a b))))
 (lam a U64 (lam b U64 (lam0 p (EqChain a b)
  (chain-induct (lam x U64 (lam y U64 (EqChain x y))) (lam x U64 (chain-refl x))
   (lam x U64 (lam y U64 (lam z U64 (lam0 e (Eq x y) (lam0 tail (EqChain y z) (lam0 ih (EqChain y z) (chain-step x y z e ih))))))) p)))))
(export captured (pi i U64 I64) (lam i U64 (if-lt i 3 p
 (app get 3 (array (int 11) (int 22) (int 33)) i (app keep i 3 i i p (chain-step i i i (refl i) (chain-refl i)))) (int -1))))
(export cloned (pi n U64 (pi i U64 I64)) (lam n U64 (lam i U64 (if-eq n 3 e (if-lt i n p
 (app get 3 (array (int 11) (int 22) (int 33)) i (transport (lam k U64 (Lt i k))
  (app chain_eq n 3 (app clone n 3 (chain-step n 3 3 e (chain-refl 3)))) p)) (int -1)) (int -2)))))
"""
    capture_path = temporary / "chain-captured.jh"
    capture_core_path = temporary / "chain-captured.jhc"
    capture_path.write_text(capture_source)
    capture_core_path.write_text(capture_core)
    programs = [(path, core_path, core_source, ["lookup", *names]),
                (capture_path, capture_core_path, capture_core, ["captured", "cloned"])]
    rng = random.Random(0xC4A1)
    values = [0, 1, 2, 3, 4, (1 << 63) - 1, 1 << 63, (1 << 64) - 1,
              *(rng.getrandbits(64) for _ in range(8))]
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for number, (path, core_path, text, names) in enumerate(programs):
        command("check", path, "--lib")
        command("check", core_path, source=False)
        paired_mir = command("emit-mir", path, "--lib").stdout
        assert paired_mir == command("emit-mir", core_path, source=False).stdout
        assert "assert" not in paired_mir and "call" not in paired_mir and "chain" not in paired_mir
        formatted = temporary / f"chain-formatted-{number}.jh"
        formatted.write_text(command("fmt", path).stdout)
        assert paired_mir == command("emit-mir", formatted, "--lib").stdout
        reference = {}
        for _, name, _, body in read_terms(text):
            reference[name] = evaluate(body, reference.copy())
        for target, machine in (("x86_64", 62), ("aarch64", 183)):
            for level in ("-O0", "-O2"):
                for is_source, suffix in ((True, "jh"), (False, "jhc")):
                    obj = temporary / f"chain-{number}-{target}{level}-{suffix}.o"
                    options = ["--lib"] if is_source else []
                    command("emit-obj", path if is_source else core_path, *options,
                            "--target", target, level, "-o", str(obj), source=is_source)
                    data = obj.read_bytes()
                    assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                    if target != host:
                        continue
                    library = temporary / f"chain-{number}{level}-{suffix}.so"
                    cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
                    run([*cc, "-shared", str(obj), "-o", str(library)])
                    native = ctypes.CDLL(str(library))
                    for name in names:
                        function = getattr(native, name)
                        arity = 3 if name == "lookup" else 2 if name == "cloned" else 1
                        function.argtypes = [ctypes.c_uint64] * arity
                        function.restype = ctypes.c_int64
                        arguments = ((a, b, i) for a in values for b in values for i in values[:8]) if arity == 3 else (
                            ((a, b) for a in values for b in values) if arity == 2 else ((a,) for a in values))
                        for args in arguments:
                            expected = reference[name]
                            for value in args:
                                expected = expected(value)
                            assert function(*args) == expected, (name, args)
    print(f"dependent induction: paired source/core execution, captured cases, erased recursive proofs, {len(source_invalid)} source and {len(core_invalid)} core rejections passed")
