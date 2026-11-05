"""Equality/transport regressions, called by the ordinary core suite."""
import ctypes
import json
import os
import platform
import random
import re
import shlex
import struct


def validate_equality(compiler, root, temporary, environment, run, definitions, evaluate):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    example = root / "examples/core_equality.jh"
    core_example = root / "examples/core_equality.jhc"
    unavailable = {**environment, "JIHOO_LLVM": "/unavailable", "JIHOO_CC": "/unavailable",
                   "JIHOO_LD": "/unavailable"}
    command("check", example, env=unavailable)
    command("check", core_example, source=False, env=unavailable)
    mir = command("emit-mir", example, "--lib").stdout
    assert mir == command("emit-mir", core_example, source=False).stdout
    assert mir.count("fn ") == 1 and len(re.findall(r"let mut", mir)) == 10, mir
    assert mir.count("switch ") == 2 and mir.count("[_") == 1, mir
    assert " == " in mir and " < " in mir
    for absent in ("assert", "call", "Eq", "Lt", "transport", "refl", "closure"):
        assert absent not in mir, (absent, mir)
    llvm = command("emit-llvm", example, "--lib").stdout
    lookup = re.search(r'define[^\n]*@"?lookup"?\([^\n]*\).*?\n}', llvm, re.S)
    assert lookup and re.search(r'@"?lookup"?\(i64[^,)]*, i64[^,)]*\)', lookup[0]), llvm
    assert "malloc" not in lookup[0] and "panic" not in lookup[0]
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 11 and not result.stdout and not result.stderr

    source_helper = """
fn get(n: u64, xs: [i64; n], i: u64, p: erased(Lt(i, n))) -> i64 { index(xs, i, p) }
"""
    core_helper = """
(def get (pi n U64 (pi xs (Array n) (pi i U64 (pi0 p (Lt i n) I64))))
 (lam n U64 (lam xs (Array n) (lam i U64 (lam0 p (Lt i n) (index xs i p))))))
"""
    source_invalid = {
        "false-refl": "fn bad() -> Eq(0, 1) { refl(0) }",
        "symbolic-refl": "fn bad(a: u64, b: u64) -> Eq(a, b) { refl(a) }",
        "relevant": "fn bad(e: Eq(0, 0)) -> i64 { 0 }",
        "runtime": "fn bad(e: erased(Eq(0, 0))) -> i64 { e }",
        "runtime-condition": "fn bad(e: erased(Eq(0, 0))) -> i64 { if_eq(e, 0, fn(p) { 0 }, 1) }",
        "runtime-array": "fn bad(e: erased(Eq(0, 0))) -> [i64; 1] { [e] }",
        "data-family": "export fn bad() -> u64 { transport(fn(k) { u64 }, refl(0), 0) }",
        "array-family": "export fn bad() -> [i64; 1] { transport(fn(k) { [i64; k] }, refl(1), [1]) }",
        "non-equality": "fn bad() -> Lt(0, 1) { transport(fn(k) { Lt(k, 1) }, decide_lt(0, 1), decide_lt(0, 1)) }",
        "wrong-source": "fn bad(n: u64, m: u64, e: erased(Eq(n, m)), p: erased(Lt(0, m))) -> Lt(0, m) { transport(fn(k) { Lt(0, k) }, e, p) }",
        "reversed": "fn bad(n: u64, m: u64, e: erased(Eq(m, n)), p: erased(Lt(0, n))) -> Lt(0, m) { transport(fn(k) { Lt(0, k) }, e, p) }",
        "wrong-result": "fn bad(n: u64, m: u64, e: erased(Eq(n, m)), p: erased(Lt(0, n))) -> Lt(1, m) { transport(fn(k) { Lt(0, k) }, e, p) }",
        "wrong-proof": "fn bad() -> Eq(0, 1) { transport(fn(k) { Eq(0, 1) }, refl(0), refl(0)) }",
        "no-reflection": source_helper + "export fn bad(n: u64, i: u64) -> i64 { if_eq(n, 3, fn(e) { if_lt(i, n, fn(p) { get(3, [1, 2, 3], i, p) }, -1) }, -2) }",
        "false-branch-scope": "export fn bad(i: u64) -> i64 { if_eq(i, 0, fn(e) { 0 }, e) }",
        "family-scope": "fn bad() -> Eq(0, 0) { transport(fn(k) { Eq(k, 0) }, refl(k), refl(0)) }",
        "family-shadow": "fn bad(a: u64) -> Eq(a, a) { transport(fn(a) { Eq(a, 0) }, refl(a), refl(a)) }",
        "shadowed-evidence": source_helper + "export fn bad(n: u64, i: u64) -> i64 { if_eq(n, 3, fn(e) { if_eq(n, 4, fn(e) { if_lt(i, n, fn(p) { get(3, [1, 2, 3], i, transport(fn(k) { Lt(i, k) }, e, p)) }, -1) }, -2) }, -3) }",
        "dead-branch": "export fn bad() -> i64 { if_eq(0, 0, fn(e) { 7 }, index([1], 0, transport(fn(k) { Lt(k, 1) }, refl(1), decide_lt(0, 1)))) }",
        "dead-erased-argument": "fn ignore(e: erased(Eq(0, 1))) -> i64 { 7 }\nexport fn bad() -> i64 { ignore(refl(0)) }",
        "foreign-evidence": "export fn bad(e: erased(Eq(0, 0))) -> i64 { 1 }",
        "foreign-proposition": "export fn bad() -> Eq(0, 0) { refl(0) }",
        "signed-refl": "fn bad(i: i64) -> Eq(0, 0) { refl(i) }",
        "erased-refl": "fn bad(e: erased(Eq(0, 0))) -> Eq(0, 0) { refl(e) }",
        "family-runtime-proof": "fn bad(e: erased(Eq(0, 0))) -> Eq(0, 0) { transport(fn(k) { Eq(k, e) }, refl(0), refl(0)) }",
        "bad-family-binder": "fn bad() -> Eq(0, 0) { transport(fn(k: u64) { Eq(k, 0) }, refl(0), refl(0)) }",
    }
    for name, body in source_invalid.items():
        path = temporary / f"equality-{name}.jh"
        path.write_text("#![dependent_core]\n" + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr)
        assert "core:" in diagnostic.stderr and str(path) in diagnostic.stderr, diagnostic.stderr
        obj = temporary / f"equality-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False,
                env={**environment, "JIHOO_NO_ELAB": "1"})
        assert not obj.exists()

    core_invalid = {
        "false-refl": "(def bad (Eq 0 1) (refl 0))",
        "symbolic-refl": "(def bad (pi a U64 (pi b U64 (Eq a b))) (lam a U64 (lam b U64 (refl a))))",
        "signed-refl": "(def bad (Eq 0 0) (refl (int 0)))",
        "signed-equality": "(def bad (Eq (int 0) 0) (refl 0))",
        "relevant": "(def bad (pi e (Eq 0 0) I64) (lam e (Eq 0 0) (int 0)))",
        "runtime": "(def bad (pi0 e (Eq 0 0) I64) (lam0 e (Eq 0 0) e))",
        "data-family": "(export bad U64 (transport (lam k U64 U64) (refl 0) 0))",
        "runtime-family": "(export bad U64 (transport (lam k U64 k) (refl 0) 0))",
        "universe-family": "(def bad (Type 0) (transport (lam k U64 (Type 0)) (refl 0) U64))",
        "array-cast": "(export bad (Array 1) (transport (lam k U64 (Array k)) (refl 1) (array (int 1))))",
        "non-equality": "(def bad (Lt 0 1) (transport (lam k U64 (Lt k 1)) (decide-lt 0 1) (decide-lt 0 1)))",
        "wrong-source": "(def bad (Lt 0 1) (transport (lam k U64 (Lt k 1)) (refl 1) (decide-lt 0 1)))",
        "wrong-result": "(def bad (Lt 0 2) (transport (lam k U64 (Lt k 1)) (refl 0) (decide-lt 0 1)))",
        "wrong-proof": "(def bad (Eq 0 1) (transport (lam k U64 (Eq 0 1)) (refl 0) (refl 0)))",
        "family-domain": "(def bad (Eq 0 0) (transport (lam k I64 (Eq 0 0)) (refl 0) (refl 0)))",
        "no-reflection": core_helper + "(export bad (pi n U64 (pi i U64 I64)) (lam n U64 (lam i U64 (if-eq n 3 e (if-lt i n p (app get 3 (array (int 1) (int 2) (int 3)) i p) (int -1)) (int -2)))))",
        "scope": "(export bad (pi i U64 I64) (lam i U64 (if-eq i 0 e (int 0) e)))",
        "dead-branch": "(export bad I64 (if-eq 0 0 e (int 7) (index (array (int 1)) 0 (transport (lam k U64 (Lt k 1)) (refl 1) (decide-lt 0 1)))))",
        "dead-erased-argument": "(export bad I64 (app (lam0 e (Eq 0 1) (int 7)) (refl 0)))",
    }
    for name, body in core_invalid.items():
        path = temporary / f"equality-{name}.jhc"
        path.write_text(body)
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr)
        assert "core:" in diagnostic.stderr
        obj = temporary / f"equality-core-{name}.o"
        command("emit-obj", path, "-o", str(obj), source=False, success=False)
        assert not obj.exists()

    source = example.read_text().split("fn main()")[0] + """
fn trans(a: u64, b: u64, c: u64, p: erased(Eq(a, b)), q: erased(Eq(b, c))) -> Eq(a, c) {
    transport(fn(k) { Eq(a, k) }, q, p)
}
fn id(x: u64) -> u64 { x }
fn id_eq(x: u64) -> Eq(id(x), x) { refl(x) }
export fn index_alias(i: u64, j: u64) -> i64 {
    if_eq(i, j, fn(e) {
        if_lt(i, 3, fn(p) { get(3, [11, 22, 33], j, transport(fn(i) { Lt(i, 3) }, e, p)) }, -1)
    }, -2)
}
export fn chain(n: u64, m: u64, i: u64) -> i64 {
    if_eq(n, m, fn(e) { if_eq(m, 3, fn(f) {
        if_lt(i, n, fn(p) { get(3, [11, 22, 33], i, bound(i, n, 3, trans(n, m, 3, e, f), p)) }, -1)
    }, -2) }, -3)
}
export fn shadow(n: u64, i: u64) -> i64 {
    if_eq(n, 3, fn(e) { if_eq(3, n, fn(e) {
        if_lt(i, n, fn(p) { get(3, [11, 22, 33], i, bound(i, n, 3, sym(3, n, e), p)) }, -1)
    }, -2) }, -3)
}
export fn closed() -> i64 {
    if_eq(0, 0, fn(e) { get(1, [37], 0, transport(fn(k) { Lt(k, 1) }, e, decide_lt(0, 1))) }, -1)
}
export fn false_closed() -> i64 { if_eq(0, 1, fn(e) { 7 }, -1) }
export fn reflexive(i: u64) -> i64 {
    if_lt(i, 3, fn(p) { get(3, [11, 22, 33], i, transport(fn(k) { Lt(k, 3) }, id_eq(i), p)) }, -1)
}
"""
    core_source = core_example.read_text() + """
(def trans (pi a U64 (pi b U64 (pi c U64 (pi0 p (Eq a b) (pi0 q (Eq b c) (Eq a c))))))
 (lam a U64 (lam b U64 (lam c U64 (lam0 p (Eq a b) (lam0 q (Eq b c)
  (transport (lam k U64 (Eq a k)) q p)))))))
(def id (pi x U64 U64) (lam x U64 x))
(def id_eq (pi x U64 (Eq (app id x) x)) (lam x U64 (refl x)))
(export index_alias (pi i U64 (pi j U64 I64))
 (lam i U64 (lam j U64 (if-eq i j e (if-lt i 3 p
  (app get 3 (array (int 11) (int 22) (int 33)) j (transport (lam i U64 (Lt i 3)) e p)) (int -1)) (int -2)))))
(export chain (pi n U64 (pi m U64 (pi i U64 I64)))
 (lam n U64 (lam m U64 (lam i U64 (if-eq n m e (if-eq m 3 f (if-lt i n p
  (app get 3 (array (int 11) (int 22) (int 33)) i (app bound i n 3 (app trans n m 3 e f) p)) (int -1)) (int -2)) (int -3))))))
(export shadow (pi n U64 (pi i U64 I64))
 (lam n U64 (lam i U64 (if-eq n 3 e (if-eq 3 n e (if-lt i n p
  (app get 3 (array (int 11) (int 22) (int 33)) i (app bound i n 3 (app sym 3 n e) p)) (int -1)) (int -2)) (int -3)))))
(export closed I64 (if-eq 0 0 e (app get 1 (array (int 37)) 0
 (transport (lam k U64 (Lt k 1)) e (decide-lt 0 1))) (int -1)))
(export false_closed I64 (if-eq 0 1 e (int 7) (int -1)))
(export reflexive (pi i U64 I64) (lam i U64 (if-lt i 3 p
 (app get 3 (array (int 11) (int 22) (int 33)) i (transport (lam k U64 (Lt k 3)) (app id_eq i) p)) (int -1))))
"""
    path = temporary / "equality-program.jh"
    core_path = temporary / "equality-program.jhc"
    path.write_text(source)
    core_path.write_text(core_source)
    command("check", path, "--lib")
    command("check", core_path, source=False)
    paired_mir = command("emit-mir", path, "--lib").stdout
    assert paired_mir == command("emit-mir", core_path, source=False).stdout
    assert "assert" not in paired_mir and "transport" not in paired_mir and "call" not in paired_mir
    formatted = temporary / "equality-formatted.jh"
    formatted.write_text(command("fmt", path).stdout)
    assert paired_mir == command("emit-mir", formatted, "--lib").stdout
    reference = {}
    for _, name, _, body in definitions(core_source):
        reference[name] = evaluate(body, reference.copy())
    rng = random.Random(0xE9)
    values = [0, 1, 2, 3, 4, (1 << 63) - 1, 1 << 63, (1 << 64) - 1,
              *(rng.getrandbits(64) for _ in range(8))]
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            for is_source, suffix in ((True, "jh"), (False, "jhc")):
                obj = temporary / f"equality-{target}{level}-{suffix}.o"
                options = ["--lib"] if is_source else []
                command("emit-obj", path if is_source else core_path, *options,
                        "--target", target, level, "-o", str(obj), source=is_source)
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                library = temporary / f"equality{level}-{suffix}.so"
                cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
                run([*cc, "-shared", str(obj), "-o", str(library)])
                native = ctypes.CDLL(str(library))
                for name in ("closed", "false_closed"):
                    function = getattr(native, name)
                    function.restype = ctypes.c_int64
                    assert function() == reference[name]
                for name in ("lookup", "index_alias", "shadow"):
                    function = getattr(native, name)
                    function.argtypes = [ctypes.c_uint64, ctypes.c_uint64]
                    function.restype = ctypes.c_int64
                    for a in values:
                        for b in values:
                            assert function(a, b) == reference[name](a)(b), (name, a, b)
                native.chain.argtypes = [ctypes.c_uint64] * 3
                native.chain.restype = ctypes.c_int64
                for n in values:
                    for m in values:
                        for i in values[:8]:
                            assert native.chain(n, m, i) == reference["chain"](n)(m)(i), (n, m, i)
                native.reflexive.argtypes = [ctypes.c_uint64]
                native.reflexive.restype = ctypes.c_int64
                for i in values:
                    assert native.reflexive(i) == reference["reflexive"](i)
    print(f"dependent equality: paired source/core execution, erased transport, {len(source_invalid)} source and {len(core_invalid)} core rejections passed")
