"""Loops whose invariants are types, called by tests/core.py.

fold(n, fn(k) { T(k) }, init, body) has init : T(0), a body from T(i) to
T(i + 1) and the result T(n); into a proposition it is a proof by induction
on the naturals.
"""
import ctypes
import json
import os
import platform
import shlex
import struct

from core_buffer import COUNTER

SOURCE_INVALID = {
    "false-entry": ("fn bad(n: u64) -> refine(fn(c) { Lt(c, n) }) { fold(n, fn(k) { refine(fn(c) { Lt(c, k) }) }, pack(0, decide_lt(0, 0)), fn(i, p, acc) { pack(witness(acc) + 1, lt_add(witness(acc), i, 1, proof(acc))) }) }", "decide-lt needs a true"),
    "not-preserved": ("fn bad(n: u64) -> refine(fn(c) { Lt(c, n + 1) }) { fold(n, fn(k) { refine(fn(c) { Lt(c, k + 1) }) }, pack(0, decide_lt(0, 1)), fn(i, p, acc) { pack(witness(acc) + 2, lt_add(witness(acc), i + 1, 1, proof(acc))) }) }", "type mismatch"),
    "off-by-one": ("fn bad(n: u64, table: [i64; n], limit: u64) -> i64 { let c = matches(n, limit)\n index(table, witness(c), proof(c)) }", "type mismatch"),
    "false-induction": ("fn bad(n: u64) -> Even(n + n + 1) { fold(n, fn(k) { Even(k + k + 1) }, zero(), fn(i, p, acc) { twice(i + i + 1, acc) }) }", "type mismatch"),
    "wrong-step": ("fn bad(n: u64) -> Even(n + n) { fold(n, fn(k) { Even(k + k) }, zero(), fn(i, p, acc) { acc }) }", "type mismatch"),
    "wrong-count": ("fn bad(n: u64) -> Even(n + n) { fold(n + 1, fn(k) { Even(k + k) }, zero(), fn(i, p, acc) { twice(i + i, acc) }) }", "type mismatch"),
    "motive-arity": ("fn bad(n: u64) -> i64 { fold(n, fn(a, b) { i64 }, 0, fn(i, p, acc) { acc }) }", "wrong proof family arity"),
    "owned-capture": ("fn bad(n: u64, b: buffer(1)) -> i64 { fold(n, fn(k) { i64 }, 0, fn(i, p, acc) { load(b, 0, decide_lt(0, 1), fn(v, b) { free(b, v) }) }) }", "a loop body runs many times"),
}

CORE_INVALID = {
    "not-a-function": ("(def bad (pi n U64 I64) (lam n U64 (loop n I64 (int 0) (lam i U64 (lam0 p (Lt i n) (lam acc I64 acc))))))", "motive is fn(k)"),
    "motive-of-borrow": ("(def bad (pi n U64 I64) (lam n U64 (loop n (lam k I64 I64) (int 0) (lam i U64 (lam0 p (Lt i n) (lam acc I64 acc))))))", "motive takes its index"),
    "erased-motive": ("(def bad (pi n U64 I64) (lam n U64 (loop n (lam0 k (Lt 0 1) I64) (int 0) (lam i U64 (lam0 p (Lt i n) (lam acc I64 acc))))))", "motive is fn(k)"),
    "motive-of-types": ("(def bad (pi n U64 (Type 0)) (lam n U64 (loop n (lam k U64 (Type 0)) U64 (lam i U64 (lam0 p (Lt i n) (lam acc (Type 0) acc))))))", "runtime data or evidence"),
    "layout-by-index": ("(def bad (pi n U64 U64) (lam n U64 (loop n (lam k U64 (if-lt k 1 q U64 I64)) 0 (lam i U64 (lam0 p (Lt i n) (lam acc U64 acc))))))", "a scalar, a refinement or an owned value"),
    "function-accumulator": ("(def bad (pi n U64 (pi x U64 U64)) (lam n U64 (loop n (lam k U64 (pi x U64 U64)) (lam x U64 x) (lam i U64 (lam0 p (Lt i n) (lam acc (pi x U64 U64) acc))))))", "a scalar, a refinement or an owned value"),
    "borrow-accumulator": ("(def bad (pi n U64 (pi r (Ref Bag) (Ref Bag))) (lam n U64 (lam r (Ref Bag) (loop n (lam k U64 (Ref Bag)) r (lam i U64 (lam0 p (Lt i n) (lam acc (Ref Bag) acc)))))))", "a scalar, a refinement or an owned value"),
    "erased-at-runtime": ("(def bad (pi n U64 I64) (lam n U64 (loop n (lam k U64 I64) (int 0) (lam i U64 (lam0 p (Lt i n) (lam0 acc I64 acc))))))", "erased binders must be"),
    "proof-kept": ("(def bad (pi n U64 (Even (uadd n n))) (lam n U64 (loop n (lam k U64 (Even (uadd k k))) zero (lam i U64 (lam0 p (Lt i n) (lam acc (Even (uadd i i)) (twice (uadd i i) acc)))))))", "proof binders must be erased"),
    "owned-twice": ("(def bad (pi n U64 (Buffer 1)) (lam n U64 (loop n (lam k U64 (Buffer 1)) (alloc 1 (int 0)) (lam i U64 (lam0 p (Lt i n) (lam acc (Buffer 1) (free acc acc)))))))", "used more than once"),
    "owned-dropped": ("(def bad (pi n U64 (Buffer 1)) (lam n U64 (loop n (lam k U64 (Buffer 1)) (alloc 1 (int 0)) (lam i U64 (lam0 p (Lt i n) (lam acc (Buffer 1) (alloc 1 (int 0))))))))", "an owned value must be used"),
    "unrolled": ("(def bad (Eq (loop 2 (lam k U64 U64) 0 (lam i U64 (lam0 p (Lt i 2) (lam acc U64 (uadd acc 1))))) 2) (refl 2))", "type mismatch"),
}

MORE = """
// An owned accumulator whose type does not change, and one whose evidence
// about its index does.
fn filled(n: u64, x: i64) -> buffer(n + 1) {
    fold(n, fn(k) { buffer(n + 1) }, alloc(n + 1, 0), fn(i, p, acc) {
        store(acc, i, x, lt_le(i, n, n + 1, p, lt_add(0, 2, n, decide_lt(0, 2))))
    })
}

fn last_written(n: u64, x: i64) -> i64 {
    let b = filled(n + 1, x)
    load(b, n, lt_le(n, n + 1, n + 2, lt_add(0, 1, n, decide_lt(0, 1)),
        lt_add(0, 2, n + 1, decide_lt(0, 2))), fn(v, b) { v })
}

export fn written(n: u64, x: i64) -> i64 { last_written(n, x) }

// A let runs a loop once, however many times its value is used.
fn twice_sum(n: u64) -> u64 {
    let s = fold(n, fn(k) { u64 }, 0, fn(i, p, acc) { acc + 1 })
    s + s
}

export fn doubled_count(n: u64) -> u64 { twice_sum(n) }
"""

# A list held with evidence of its length, built by a loop that keeps the
# invariant: T(k) = Sized(k), a heap value with a proof about its own field.
SIZED = """
(data List
  (Nil List)
  (Cons (pi x I64 (pi xs List List))))

(def length
  (pi xs (Ref List) U64)
  (lam xs (Ref List) (view-rec List U64 0
    (lam x I64 (lam rest (Ref List) (lam ih U64 (uadd ih 1)))) xs)))

(data Sized 1 1
  (Make (pi0 n U64 (pi l List (pi0 e (Eq (app length (borrow l)) n) (Sized n))))))

(def build
  (pi n U64 (pi x I64 (Sized n)))
  (lam n U64 (lam x I64
    (loop n (lam k U64 (Sized k))
      (Make 0 Nil (refl 0))
      (lam i U64 (lam0 p (Lt i n) (lam acc (Sized i)
        (case Sized (lam s (Sized i) (Sized (uadd i 1)))
          (lam l List (lam0 e (Eq (app length (borrow l)) i)
            (Make (uadd i 1) (Cons x l)
              (transport (lam m U64 (Eq (uadd (app length (borrow l)) 1) (uadd m 1))) e
                (refl (uadd (app length (borrow l)) 1))))))
          acc))))))))

(def size_of
  (pi n U64 (pi s (Sized n) (Refine (lam m U64 (Eq m n)))))
  (lam n U64 (lam s (Sized n)
    (case Sized (lam t (Sized n) (Refine (lam m U64 (Eq m n))))
      (lam l List (lam0 e (Eq (app length (borrow l)) n)
        (lend l (lam r (Ref List)
            (pack (lam m U64 (Eq m n)) (app length r) e))
          (lam a (Refine (lam m U64 (Eq m n))) (lam y List (drop List y a))))))
      s))))

(export counted
  (pi n U64 (pi x I64 U64))
  (lam n U64 (lam x I64 (witness (app size_of n (app build n x))))))
"""


def validate_invariant(compiler, root, temporary, environment, run, definitions, evaluate, buffers,
                       nodes):
    def command(action, path, *options, source=True, success=True, env=None):
        prefix = [compiler] if source else [compiler, "core"]
        return run([*prefix, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    def counted(obj, name):
        """A shared library of obj whose malloc and free are counted."""
        counter = temporary / "invariant-counter.c"
        counter.write_text(COUNTER)
        library = temporary / f"{name}.so"
        cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
        run([*cc, "-shared", "-fPIC", str(obj), str(counter), "-o", str(library),
             "-Wl,--wrap=malloc", "-Wl,--wrap=free"])
        native = ctypes.CDLL(str(library))
        return native, ctypes.c_long.in_dll(native, "allocations"), ctypes.c_long.in_dll(native, "frees")

    example = root / "examples/core_invariant.jh"
    core_example = root / "examples/core_invariant.jhc"
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
    # The table is read at the count with no bounds check, and the proof by
    # induction leaves no loop: demo has one, doubled has none.
    assert "assert" not in mir and "panic" not in mir, mir
    doubled = mir[mir.index("fn doubled"):]
    assert "switch" not in doubled, mir
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 7 and not result.stdout and not result.stderr, result

    for name, (body, reason) in SOURCE_INVALID.items():
        path = temporary / f"invariant-{name}.jh"
        path.write_text(prefix + body + "\nexport fn good() -> i64 { 0 }\n")
        diagnostic = command("check", path, "--lib", "--no-verify", "--release",
                             "--error-format=json", success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert reason in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"invariant-{name}.o"
        command("emit-obj", path, "--lib", "-o", str(obj), success=False)
        assert not obj.exists(), name

    bag = "(data Bag (Empty Bag) (More (pi b Bag Bag)))\n"
    for name, (body, reason) in CORE_INVALID.items():
        path = temporary / f"invariant-{name}.jhc"
        path.write_text(core_prefix + bag + body + "\n(export good I64 (int 0))\n")
        diagnostic = command("check", path, "--error-format=json", source=False, success=False)
        assert diagnostic.returncode == 1 and json.loads(diagnostic.stderr), name
        assert reason in diagnostic.stderr, (name, diagnostic.stderr)
        obj = temporary / f"invariant-{name}.o"
        command("emit-obj", path, "-o", str(obj), source=False, success=False)
        assert not obj.exists(), name

    valid = temporary / "invariant-more.jh"
    valid.write_text(prefix + MORE)
    command("check", valid, "--lib")
    sized = temporary / "invariant-sized.jhc"
    sized.write_text(SIZED)
    command("check", sized, source=False)
    for level in ("-O0", "-O2"):
        obj = temporary / f"invariant-more{level}.o"
        command("emit-obj", valid, "--lib", level, "-o", str(obj))
        native, allocations, frees = counted(obj, f"invariant-more{level}")
        native.written.argtypes = [ctypes.c_uint64, ctypes.c_int64]
        native.written.restype = ctypes.c_int64
        native.doubled_count.argtypes = [ctypes.c_uint64]
        native.doubled_count.restype = ctypes.c_uint64
        for n in (0, 1, 2, 9):
            assert native.written(n, 11) == 11, n
            assert native.doubled_count(n) == 2 * n, n
            assert allocations.value == frees.value, n
        obj = temporary / f"invariant-sized{level}.o"
        command("emit-obj", sized, level, "-o", str(obj), source=False)
        native, allocations, frees = counted(obj, f"invariant-sized{level}")
        native.counted.argtypes = [ctypes.c_uint64, ctypes.c_int64]
        native.counted.restype = ctypes.c_uint64
        for n in (0, 1, 2, 9):
            assert native.counted(n, 3) == n, n
            assert allocations.value == frees.value, n
    # A loop in a let runs once: one loop in the function, not two.
    mir = command("emit-mir", valid, "--lib").stdout
    twice = mir[mir.index("fn doubled_count"):]
    twice = twice[:twice.index("\n}")]
    assert twice.count("switch") == 1, twice

    reference = {}
    for _, name, _, body in definitions(core_text):
        reference[name] = evaluate(body, reference.copy())
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    table = [5, 6, 7, 8]
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            for is_source, suffix in ((True, "jh"), (False, "jhc")):
                obj = temporary / f"invariant-{target}{level}-{suffix}.o"
                options = ["--lib"] if is_source else []
                command("emit-obj", example if is_source else core_example, *options,
                        "--target", target, level, "-o", str(obj), source=is_source)
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                native, _, _ = counted(obj, f"invariant{level}-{suffix}")
                native.demo.argtypes = [ctypes.c_uint64]
                native.demo.restype = ctypes.c_int64
                native.doubled.argtypes = [ctypes.c_uint64]
                native.doubled.restype = ctypes.c_uint64
                for limit in (0, 1, 2, 3, 4, 100, (1 << 64) - 1):
                    expected = table[min(limit, 3)]
                    assert native.demo(limit) == reference["demo"](limit) == expected, limit
                for n in (0, 1, 5, 200):
                    assert native.doubled(n) == reference["doubled"](n) == 2 * n, n
    print(f"dependent loop invariants: paired source/core execution, counted frees, {len(SOURCE_INVALID)} source and {len(CORE_INVALID)} core rejections passed")
