#!/usr/bin/env python3
"""Check the native dependent-core path, including erasure and executable code."""
import argparse
import ctypes
import json
import os
from pathlib import Path
import platform
import random
import re
import shlex
import struct
import subprocess
import tempfile


def run(command, *, success=True, **kwargs):
    result = subprocess.run(command, text=True, capture_output=True, timeout=120, **kwargs)
    if (result.returncode == 0) != success:
        raise AssertionError(f"{command!r}: {result.returncode}\n{result.stdout}\n{result.stderr}")
    return result


def read_terms(text):
    tokens = iter(re.findall(r"\(|\)|[^\s()]+", re.sub(r";[^\n]*", "", text)))

    def read(token):
        if token != "(":
            assert token != ")"
            return token
        result = []
        for token in tokens:
            if token == ")":
                return result
            result.append(read(token))
        raise AssertionError("unclosed reference term")

    return [read(token) for token in tokens]


# Constructor name -> (family name, case index, field count, recursive positions).
CONSTRUCTORS = {}
FAMILIES = {}
# Data type name -> number of parameters, which cases do not receive.
PARAMS = {}
# Every buffer the evaluator allocated, to check that each is freed once.
BUFFERS = []


class Buffer:
    def __init__(self, values):
        self.values = values
        self.alive = True


# Data types with a recursive field live on the heap; every node is taken
# apart exactly once.
BOXED = set()
NODES = []
# Above zero while evaluating evidence (an erased argument or a borrow
# made by (borrow x)), which never runs: its nodes and buffers are not
# program memory, and it neither consumes nor frees any.
GHOST = [0]


def ghostly(thunk):
    GHOST[0] += 1
    try:
        return thunk()
    finally:
        GHOST[0] -= 1


class Erased:
    """A (lam0 ...) function: its argument is evidence."""

    def __init__(self, function):
        self.function = function

    def __call__(self, value):
        return self.function(value)


class Node:
    def __init__(self, family, k, fields):
        self.family, self.k, self.fields = family, k, fields
        self.alive = True

    def take(self):
        if GHOST[0]:
            return ("con", self.family, self.k, self.fields)
        assert self.alive, "node used twice"
        self.alive = False
        return ("con", self.family, self.k, self.fields)


class Borrow:
    """A borrow of a buffer or node; it expires when its lend ends."""

    def __init__(self, value, parent=None):
        self.value = value
        self.live = True
        # Evidence reads the value it had, even after it was freed.
        self.ghost = GHOST[0] > 0 or (parent is not None and parent.ghost)
        # A field read through a borrow lives as long as that borrow.
        self.parent = parent

    def read(self):
        if self.ghost:
            return self.value
        assert self.live, "a borrow outlived its lend"
        if self.parent is not None:
            self.parent.read()
        assert self.value.alive, "a borrow of a freed value"
        return self.value


def definitions(text):
    """Return (kind, name, type, body) tuples, registering inductives for evaluate.

    Use this instead of read_terms when loading a program's definitions, including
    from core_chain.py. Each call resets the module-level family/constructor tables;
    evaluate the returned bodies in declaration order into the same environment.
    """
    CONSTRUCTORS.clear()
    FAMILIES.clear()
    PARAMS.clear()
    BOXED.clear()
    result = []
    for form in read_terms(text):
        if form[0] not in ("inductive", "data"):
            kind, name, ty, body = form
            assert kind in ("def", "export")
            result.append((kind, name, ty, body))
            continue
        if form[0] == "data":
            # A data type; its values are constructor tuples. With counts,
            # (data F N P ...) has N indices, the first P parameters.
            _, family, *constructors = form
            arity = params = 0
            if isinstance(constructors[0], str):
                arity, params, *constructors = constructors
            PARAMS[family] = int(params)
        else:
            _, family, arity, *constructors = form
        FAMILIES[family] = int(arity)
        for k, (name, ty) in enumerate(constructors):
            fields, recursive = 0, []
            while isinstance(ty, list) and ty[0] in ("pi", "pi0"):
                _, _, domain, ty = ty
                head = domain[0] if isinstance(domain, list) else domain
                if head == family:
                    recursive.append(fields)
                fields += 1
            CONSTRUCTORS[name] = (family, k, fields, tuple(recursive))
            if form[0] == "data" and recursive:
                BOXED.add(family)
    return result


def constructor(name, fields):
    family, k, count, _ = CONSTRUCTORS[name]
    assert len(fields) == count
    if family in BOXED:
        node = Node(family, k, tuple(fields))
        if not GHOST[0]:
            NODES.append(node)
        return node
    return ("con", family, k, tuple(fields))


def opened(value):
    """A constructor value; a heap node is consumed."""
    return value.take() if isinstance(value, Node) else value


def evaluate(term, env):
    """An independent named-variable evaluator; the compiler uses de Bruijn terms."""
    if isinstance(term, str):
        if term.isdecimal():
            return int(term)
        if term in env:
            return env[term]
        if term in CONSTRUCTORS:
            return constructor(term, [])
        if term in FAMILIES:
            return ("ind", term)
        raise AssertionError(f"unknown reference name {term}")
    head, *args = term
    if head in ("lam", "lam0"):
        name, _, body = args
        function = lambda value: evaluate(body, {**env, name: value})
        return Erased(function) if head == "lam0" else function
    if head == "app":
        value = evaluate(args[0], env)
        for argument in args[1:]:
            if isinstance(value, Erased):
                value = value(ghostly(lambda: evaluate(argument, env)))
            else:
                value = value(evaluate(argument, env))
        return value
    if head == "int":
        return int(args[0])
    if head == "array":
        return [evaluate(x, env) for x in args]
    if head in ("Lt", "Eq"):
        a, b = (evaluate(x, env) for x in args)
        return (a, b) if head == "Lt" else ("eq", a, b)
    if head == "refl":
        a = evaluate(args[0], env)
        return ("eq", a, a)
    if head == "transport":
        family, equality, proof = (evaluate(x, env) for x in args)
        tag, a, b = equality
        assert tag == "eq" and a == b and proof == family(a)
        return family(b)
    if head == "if-eq":
        a, b = evaluate(args[0], env), evaluate(args[1], env)
        return evaluate(args[3], {**env, args[2]: ("eq", a, b)}) if a == b else evaluate(args[4], env)
    if head == "induct":
        family, _, *branches, evidence = args
        cases = [evaluate(case, env) for case in branches]
        metadata = {k: (count, recursive)
                    for f, k, count, recursive in CONSTRUCTORS.values() if f == family}

        def fold(proof):
            tag, actual_family, k, fields = opened(proof)
            assert tag == "con" and actual_family == family
            count, recursive = metadata[k]
            assert len(fields) == count
            value = cases[k]
            for field in fields[PARAMS.get(family, 0):]:
                value = value(field)
            for position in recursive:
                value = value(fold(fields[position]))
            return value

        return fold(evaluate(evidence, env))
    if head in ("add", "sub", "mul"):
        a, b = (evaluate(x, env) for x in args)
        value = a + b if head == "add" else a - b if head == "sub" else a * b
        # The compiled program traps here; callers avoid overflowing inputs.
        assert -(1 << 63) <= value < (1 << 63), ("overflow", head, a, b)
        return value
    if head == "uadd":
        a, b = (evaluate(x, env) for x in args)
        # A sum of naturals; the compiled program traps beyond U64.
        assert a + b < (1 << 64), ("overflow", a, b)
        return a + b
    if head == "usub":
        a, b, proof = (evaluate(x, env) for x in args)
        assert proof == (b, a + 1) and b <= a
        return a - b
    if head == "zero-le":
        a = evaluate(args[0], env)
        return (0, a + 1)
    if head == "case":
        family, _, *branches, value = args
        cases = [evaluate(case, env) for case in branches]
        tag, actual, k, fields = opened(evaluate(value, env))
        assert tag == "con" and actual == family
        result = cases[k]
        for field in fields[PARAMS.get(family, 0):]:
            result = result(field)
        return result
    if head == "alloc":
        n, x = (evaluate(v, env) for v in args)
        assert n < (1 << 20), ("test buffers are small", n)
        buffer = Buffer([x] * n)
        if not GHOST[0]:
            BUFFERS.append(buffer)
        return buffer
    if head in ("load", "store"):
        buffer, index, *rest = (evaluate(v, env) for v in args)
        # A freed buffer is never touched again.
        assert buffer.alive and 0 <= index < len(buffer.values)
        if head == "load":
            proof, k = rest
            assert proof == (index, len(buffer.values))
            return k(buffer.values[index])(buffer)
        value, proof = rest
        assert proof == (index, len(buffer.values))
        buffer.values[index] = value
        return buffer
    if head == "free":
        buffer = evaluate(args[0], env)
        if GHOST[0]:
            return evaluate(args[1], env)
        assert buffer.alive, "double free"
        buffer.alive = False
        return evaluate(args[1], env)
    if head == "drop":
        family, value, rest = args
        released = evaluate(value, env)
        assert isinstance(released, Node) and released.family == family, ("drop", family)
        if GHOST[0]:
            return evaluate(rest, env)

        def release(node):
            # Every node the value owns is taken apart once.
            for field in node.take()[3]:
                if isinstance(field, Node):
                    release(field)

        release(released)
        return evaluate(rest, env)
    if head == "pack":
        family, a, proof = (evaluate(x, env) for x in args)
        # The evidence must be of the predicate at the witness.
        assert proof == family(a), ("pack", a, proof)
        return ("pack", a, proof)
    if head in ("witness", "proof"):
        tag, a, proof = evaluate(args[0], env)
        assert tag == "pack"
        return a if head == "witness" else proof
    if head in ("lt-add", "lt-cancel"):
        a, b, c, proof = (evaluate(x, env) for x in args)
        shifted = (a + c, b + c)
        assert proof == ((a, b) if head == "lt-add" else shifted) and a < b
        return shifted if head == "lt-add" else (a, b)
    if head == "lt-le":
        x, y, z, p, q = (evaluate(v, env) for v in args)
        assert p == (x, y) and q == (y, z + 1) and x < y <= z
        return (x, z)
    if head == "fold":
        n, acc, body = (evaluate(x, env) for x in args)
        for i in range(n):
            acc = body(i)((i, n))(acc)
        return acc
    if head == "loop":
        n = evaluate(args[0], env)
        acc, body = evaluate(args[2], env), evaluate(args[3], env)
        for i in range(n):
            acc = body(i)((i, n))(acc)
        return acc
    if head == "decide-lt":
        a, b = (evaluate(x, env) for x in args)
        assert a < b
        return (a, b)
    if head == "if-lt":
        a, b = evaluate(args[0], env), evaluate(args[1], env)
        return evaluate(args[3], {**env, args[2]: (a, b)}) if a < b else evaluate(args[4], env)
    if head == "index":
        array, index, proof = (evaluate(x, env) for x in args)
        if isinstance(array, Borrow):
            array = array.read().values
        assert proof == (index, len(array)) and 0 <= index < len(array)
        return array[index]
    if head == "borrow":
        # Evidence only: a borrow of a value built for the type, never freed.
        return ghostly(lambda: Borrow(evaluate(args[0], env)))
    if head == "absurd":
        raise AssertionError("code with evidence of Lt(i, 0) ran")
    if head == "deref":
        # Evidence only: the value a borrow reads.
        borrowed = ghostly(lambda: evaluate(args[0], env))
        return borrowed.value if isinstance(borrowed, Borrow) else borrowed
    if head == "lend":
        owner = evaluate(args[0], env)
        assert isinstance(owner, (Buffer, Node)) and owner.alive, ("lend", owner)
        borrow = Borrow(owner)
        result = evaluate(args[1], env)(borrow)
        borrow.live = False
        assert not isinstance(result, Borrow), "a borrow escaped its lend"
        assert owner.alive, "a lent value was freed"
        return evaluate(args[2], env)(result)(owner)
    if head in ("view", "view-rec"):
        family, _, *branches, value = args
        cases = [evaluate(case, env) for case in branches]
        metadata = {k: (count, recursive)
                    for f, k, count, recursive in CONSTRUCTORS.values() if f == family}

        def read(borrow):
            node = borrow.read()
            assert isinstance(node, Node) and node.family == family, ("view", family)
            count, recursive = metadata[node.k]
            # Heap fields arrive borrowed, under the same lend.
            fields = [Borrow(x, borrow) if isinstance(x, Node) else x for x in node.fields]
            result = cases[node.k]
            for field in fields[PARAMS.get(family, 0):]:
                result = result(field)
            if head == "view-rec":
                for position in recursive:
                    result = result(read(fields[position]))
            return result

        return read(evaluate(value, env))
    if head in CONSTRUCTORS:
        return constructor(head, [evaluate(x, env) for x in args])
    if head in FAMILIES:
        return ("ind", head, *(evaluate(x, env) for x in args))
    raise AssertionError(f"unsupported reference term {head}")


GET = """
(def get
 (pi n U64 (pi xs (Array n) (pi i U64 (pi0 p (Lt i n) I64))))
 (lam n U64 (lam xs (Array n) (lam i U64 (lam0 p (Lt i n) (index xs i p))))))
"""



SOURCE_GET = """
fn get(n: u64, xs: [i64; n], i: u64, p: erased(Lt(i, n))) -> i64 {
    index(xs, i, p)
}
"""


def source_frontend(compiler, root, temporary, environment):
    """Exercise ordinary parsing, direct AST elaboration and the shared kernel."""
    def command(action, path, *options, success=True, env=None):
        return run([compiler, action, str(path), *options], success=success,
                   env=environment if env is None else env)

    example = root / "examples/core_index.jh"
    # Checking needs neither a standard library nor LLVM/link/proof tools.
    unavailable = {**environment, "JIHOO_PATH": "/unavailable", "JIHOO_LLVM": "/unavailable",
                   "JIHOO_CC": "/unavailable", "JIHOO_LD": "/unavailable"}
    for target in ("x86_64", "aarch64"):
        for options in ([], ["--verify"], ["--no-verify"]):
            checked = command("check", example, "--target", target, *options, env=unavailable)
            assert not checked.stdout and not checked.stderr
    ast = command("emit-ast", example).stdout
    assert "erased" in ast and "if_lt" in ast
    mir = command("emit-mir", example, "--lib").stdout
    core_mir = run([compiler, "core", "emit-mir", "examples/core_index.jhc"], env=environment).stdout
    assert mir == core_mir, (mir, core_mir)
    assert len(re.findall(r"let mut", mir)) == 7, mir
    assert "assert" not in mir and "call" not in mir and "Lt" not in mir
    assert mir.count("switch ") == 1 and mir.count("[_") == 1
    for legacy in ("verify", "emit-obligations", "test"):
        rejected = command(legacy, example, "--error-format=json", success=False)
        assert rejected.returncode == 1 and "core:" in rejected.stderr
        assert json.loads(rejected.stderr)
    for level in ("-O0", "-O2"):
        result = command("run", example, level, success=False)
        assert result.returncode == 255 and not result.stdout and not result.stderr

    invalid = {
        "false-proof": "export fn bad() -> i64 { index([1], 0, decide_lt(1, 1)) }",
        "wrong-index": SOURCE_GET + "export fn bad() -> i64 { get(2, [1, 2], 1, decide_lt(0, 2)) }",
        "wrong-length": SOURCE_GET + "export fn bad() -> i64 { get(3, [1, 2], 1, decide_lt(1, 3)) }",
        "wrong-branch-bound": SOURCE_GET + "export fn bad(i: u64) -> i64 { if_lt(i, 4, fn(p) { get(3, [1, 2, 3], i, p) }, -1) }",
        "wrong-branch-index": SOURCE_GET + "export fn bad(i: u64, j: u64) -> i64 { if_lt(i, 3, fn(p) { get(3, [1, 2, 3], j, p) }, -1) }",
        "outside-branch": SOURCE_GET + "export fn bad(i: u64) -> i64 { if_lt(i, 3, fn(p) { 0 }, get(3, [1, 2, 3], i, p)) }",
        "sibling-branch": SOURCE_GET + "export fn bad(i: u64) -> i64 { if_lt(i, 3, fn(p) { 0 }, if_lt(i, 3, fn(q) { get(3, [1, 2, 3], i, p) }, -1)) }",
        "shadowed-proof": SOURCE_GET + "export fn bad(i: u64) -> i64 { if_lt(i, 3, fn(p) { if_lt(i, 4, fn(p) { get(3, [1, 2, 3], i, p) }, -1) }, -1) }",
        "shadowed-index": SOURCE_GET + "export fn bad(i: u64) -> i64 { if_lt(i, 3, fn(i) { get(3, [1, 2, 3], i, i) }, -1) }",
        "missing-proof": SOURCE_GET + "export fn bad() -> i64 { get(1, [1], 0) }",
        "extra-proof": SOURCE_GET + "export fn bad() -> i64 { get(1, [1], 0, decide_lt(0, 1), decide_lt(0, 1)) }",
        "erased-runtime": "fn bad(p: erased(Lt(0, 1))) -> i64 { p }",
        "erased-in-array": "fn bad(p: erased(Lt(0, 1))) -> [i64; 1] { [p] }",
        "erased-in-condition": "fn bad(p: erased(Lt(0, 1))) -> i64 { if_lt(p, 1, fn(q) { 0 }, 1) }",
        "erased-data": "fn bad(n: erased(u64)) -> u64 { n }",
        "relevant-proof": "fn bad(p: Lt(0, 1)) -> i64 { 0 }",
        "comptime-proof": "fn bad(comptime p: Lt(0, 1)) -> i64 { 0 }",
        "comptime-index": "fn bad(comptime n: u64) -> u64 { n }",
        "symbolic-decide": "fn bad(i: u64) -> Lt(i, 3) { decide_lt(i, 3) }",
        "dead-helper": "fn bad() -> Lt(2, 1) { decide_lt(2, 1) }",
        "dead-branch": "export fn bad() -> i64 { if_lt(0, 1, fn(p) { 7 }, index([1], 3, decide_lt(3, 1))) }",
        "bad-erased-arg": "fn ignore(p: erased(Lt(0, 1))) -> i64 { 7 }\nexport fn bad() -> i64 { ignore(decide_lt(2, 1)) }",
        "recursive": "fn bad(x: u64) -> u64 { bad(x) }",
        "forward": "fn bad(x: u64) -> u64 { later(x) }\nfn later(x: u64) -> u64 { x }",
        "duplicate": "fn same() -> i64 { 1 }\nfn same() -> i64 { 2 }",
        "duplicate-param": "fn bad(x: u64, x: u64) -> u64 { x }",
        "u64-overflow": "export fn bad() -> u64 { 18446744073709551616 }",
        "i64-overflow": "export fn bad() -> i64 { 9223372036854775808 }",
        "i64-underflow": "export fn bad() -> i64 { -9223372036854775809 }",
        "foreign-proof": "export fn bad(p: erased(Lt(0, 1))) -> i64 { 1 }",
        "foreign-array": "export fn bad(xs: [i64; 0]) -> i64 { 1 }",
        "foreign-result": "export fn bad() -> [i64; 1] { [1] }",
        "foreign-proposition": "export fn bad() -> Lt(0, 1) { decide_lt(0, 1) }",
        "mutation": "export fn bad() -> i64 { var x = 1; x = 2; x }",
        "unsafe": "unsafe export fn bad() -> i64 { 0 }",
        "contracts": "export fn bad(x: u64) -> u64 requires x < 3 { x }",
        "attribute": "#[test]\nexport fn bad() -> i64 { 0 }",
        "import": "import unavailable\nexport fn bad() -> i64 { 0 }",
        "extern": "extern fn bad() -> i64",
        "reserved": "fn index() -> i64 { 0 }",
        "bad-branch-binder": "export fn bad() -> i64 { if_lt(0, 1, fn(p: u64) { 0 }, 1) }",
        "ordinary-index": "export fn bad() -> i64 { [1][0] }",
        "profile": "#![freestanding]\nexport fn bad() -> i64 { 0 }",
        "main-params": "fn main(x: u64) -> i64 { 0 }",
        "main-result": "fn main() -> u64 { 0 }",
        "export-main": "export fn main() -> i64 { 0 }",
    }
    for name, source in invalid.items():
        path = temporary / f"source-{name}.jh"
        # An innocent export must never hide an unused invalid helper.
        path.write_text("#![dependent_core]\n" + source + "\nexport fn good() -> i64 { 0 }\n")
        options = [] if name.startswith("main-") else ["--lib"]
        result = command("check", path, *options, "--error-format=json", success=False)
        diagnostic = json.loads(result.stderr)
        assert result.returncode == 1 and diagnostic, result.stderr
        # A module that cannot be found is the loader's error, as anywhere.
        if name not in ("u64-overflow", "import"):
            assert "core:" in result.stderr, (name, result.stderr)
        # The diagnostic must identify the .jh source, not a temporary core input.
        assert str(path) in result.stderr, (name, result.stderr)
        obj = temporary / f"source-{name}.o"
        command("emit-obj", path, *options, "--no-verify", "-o", str(obj), success=False)
        assert not obj.exists(), name

    mixed = temporary / "mixed.jh"
    mixed.write_text("import source_module\nfn main() {}\n")
    (temporary / "source_module.jh").write_text("#![dependent_core]\nexport fn select() -> i64 { 0 }\n")
    command("check", mixed, success=False)
    unmarked = temporary / "unmarked.jh"
    unmarked.write_text(SOURCE_GET + "fn main() {}\n")
    command("check", unmarked, success=False)

    # Corresponding .jh and .jhc programs, with an independent evaluator of
    # the core text. Neither text is constructed by the compiler frontend.
    source = "#![dependent_core]\n" + SOURCE_GET + """
fn evidence(i: u64, n: u64, p: erased(Lt(i, n))) -> Lt(i, n) { p }
fn forward(n: u64, xs: [i64; n], i: u64, p: erased(Lt(i, n))) -> i64 {
    get(n, xs, i, evidence(i, n, p))
}
export fn identity(x: u64) -> u64 { x }
export fn signed(x: i64) -> i64 { x }
export fn closed() -> i64 { get(1, [-9223372036854775808], 0, decide_lt(0, 1)) }
"""
    core_source = GET + """
(def evidence (pi i U64 (pi n U64 (pi0 p (Lt i n) (Lt i n))))
 (lam i U64 (lam n U64 (lam0 p (Lt i n) p))))
(def forward (pi n U64 (pi xs (Array n) (pi i U64 (pi0 p (Lt i n) I64))))
 (lam n U64 (lam xs (Array n) (lam i U64 (lam0 p (Lt i n)
 (app get n xs i (app evidence i n p)))))))
(export identity (pi x U64 U64) (lam x U64 x))
(export signed (pi x I64 I64) (lam x I64 x))
(export closed I64 (app get 1 (array (int -9223372036854775808)) 0 (decide-lt 0 1)))
"""
    rng = random.Random(0x5A17)
    names = []
    for number in range(18):
        values = [rng.randrange(-10000, 10000) for _ in range(number % 9)]
        n = len(values)
        elements = "[" + ", ".join(map(str, values)) + "]"
        body = f"if_lt(i, {n}, fn(p) {{ forward({n}, {elements}, i, p) }}, -1)"
        core_elements = "(array " + " ".join(f"(int {x})" for x in values) + ")"
        core_body = f"(if-lt i {n} p (app forward {n} {core_elements} i p) (int -1))"
        if number % 2:
            body = f"if_lt(i, 18446744073709551615, fn(p) {{ {body} }}, -1)"
            core_body = f"(if-lt i 18446744073709551615 p {core_body} (int -1))"
        name = f"pick_{number}"
        names.append(name)
        source += f"export fn {name}(i: u64) -> i64 {{ {body} }}\n"
        core_source += f"(export {name} (pi i U64 I64) (lam i U64 {core_body}))\n"
    # A false branch keeps the outer proof, and inner proof binders shadow
    # runtime names. Both cases exercise capture-avoiding substitutions.
    source += """
export fn outer(i: u64, j: u64) -> i64 {
    if_lt(i, 3, fn(p) { if_lt(j, 3, fn(q) { get(3, [11, 22, 33], j, q) }, get(3, [11, 22, 33], i, p)) }, -1)
}
export fn shadow(i: u64) -> i64 {
    if_lt(i, 3, fn(q) { if_lt(0, 1, fn(i) { get(3, [11, 22, 33], 0, q) }, -1) }, -1)
}
"""
    # shadow's q proves the old runtime i, so using index 0 must be rejected.
    shadow = source[source.index("export fn shadow"):]
    source = source[:source.index("export fn shadow")]
    shadow_path = temporary / "shadow-runtime.jh"
    shadow_path.write_text("#![dependent_core]\n" + SOURCE_GET + shadow)
    command("check", shadow_path, "--lib", success=False)
    path = temporary / "source-program.jh"
    core_path = temporary / "source-program.jhc"
    path.write_text(source)
    core_path.write_text(core_source)
    reference = {}
    for _, name, _, body in definitions(core_source):
        reference[name] = evaluate(body, reference.copy())
    command("check", path, "--lib")
    source_mir = command("emit-mir", path, "--lib").stdout
    expected_mir = run([compiler, "core", "emit-mir", str(core_path)], env=environment).stdout
    assert source_mir[:source_mir.index("fn outer ")] == expected_mir
    assert "assert" not in source_mir and "call" not in source_mir and "Lt" not in source_mir
    # Formatting must preserve the AST, including the experimental forms.
    formatted = command("fmt", path).stdout
    formatted_path = temporary / "source-formatted.jh"
    formatted_path.write_text(formatted)
    assert command("emit-mir", path, "--lib").stdout == command("emit-mir", formatted_path, "--lib").stdout
    host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
    for target, machine in (("x86_64", 62), ("aarch64", 183)):
        for level in ("-O0", "-O2"):
            obj = temporary / f"source-{target}{level}.o"
            command("emit-obj", path, "--lib", "--target", target, level, "-o", str(obj))
            data = obj.read_bytes()
            assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
            if target != host:
                continue
            cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
            library = temporary / f"source{level}.so"
            run([*cc, "-shared", str(obj), "-o", str(library)])
            native = ctypes.CDLL(str(library))
            native.closed.restype = ctypes.c_int64
            assert native.closed() == -(1 << 63)
            native.identity.argtypes = [ctypes.c_uint64]
            native.identity.restype = ctypes.c_uint64
            native.signed.argtypes = [ctypes.c_int64]
            native.signed.restype = ctypes.c_int64
            for value in (0, 1, 1 << 63, (1 << 64) - 1):
                assert native.identity(value) == reference["identity"](value)
            for value in (-(1 << 63), -1, 0, (1 << 63) - 1):
                assert native.signed(value) == reference["signed"](value)
            for name in names:
                function = getattr(native, name)
                function.argtypes = [ctypes.c_uint64]
                function.restype = ctypes.c_int64
                for value in [*range(12), (1 << 63) - 1, 1 << 63, (1 << 64) - 1,
                              *(rng.getrandbits(64) for _ in range(30))]:
                    assert function(value) == reference[name](value), (name, value)
            native.outer.argtypes = [ctypes.c_uint64, ctypes.c_uint64]
            native.outer.restype = ctypes.c_int64
            for i in (0, 1, 2, 3, 1 << 63):
                for j in (0, 1, 2, 3, (1 << 64) - 1):
                    expected = [11, 22, 33][j if j < 3 else i] if i < 3 else -1
                    assert native.outer(i, j) == expected
    print(f"dependent source: AST elaboration, both targets, native execution, {len(invalid)} rejections and MIR erasure passed")

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--compiler", required=True)
    args = parser.parse_args()
    compiler = str(Path(args.compiler).resolve())
    root = Path(__file__).resolve().parents[1]
    os.chdir(root)
    environment = dict(os.environ)
    with tempfile.TemporaryDirectory(prefix="jihoo-core-") as directory:
        temporary = Path(directory)

        def command(action, path, *options, success=True):
            return run([compiler, "core", action, str(path), *options],
                       success=success, env=environment)

        source_frontend(compiler, root, temporary, environment)
        from core_equality import validate_equality
        validate_equality(compiler, root, temporary, environment, run, definitions, evaluate)
        from core_chain import validate_chain
        validate_chain(compiler, root, temporary, environment, run, definitions, evaluate)
        from core_inductive import validate_inductive
        validate_inductive(compiler, root, temporary, environment, run, definitions, evaluate)
        from core_loop import validate_loop
        validate_loop(compiler, root, temporary, environment, run, definitions, evaluate)
        from core_order import validate_order
        validate_order(compiler, root, temporary, environment, run, definitions, evaluate)
        from core_sub import validate_sub
        validate_sub(compiler, root, temporary, environment, run, definitions, evaluate)
        from core_refine import validate_refine
        validate_refine(compiler, root, temporary, environment, run, definitions, evaluate)
        from core_data import validate_data
        validate_data(compiler, root, temporary, environment, run, definitions, evaluate)
        from core_indexed import validate_indexed
        validate_indexed(compiler, root, temporary, environment, run, definitions, evaluate)
        from core_buffer import validate_buffer
        validate_buffer(compiler, root, temporary, environment, run, definitions, evaluate, BUFFERS)
        from core_list import validate_list
        validate_list(compiler, root, temporary, environment, run, definitions, evaluate, NODES)
        from core_scope import validate_scope
        validate_scope(compiler, root, temporary, environment, run, definitions, evaluate, BUFFERS,
                       NODES)
        from core_borrow import validate_borrow
        validate_borrow(compiler, root, temporary, environment, run, definitions, evaluate, BUFFERS,
                        NODES)
        from core_borrow_proof import validate_borrow_proof
        validate_borrow_proof(compiler, root, temporary, environment, run, definitions, evaluate,
                              BUFFERS, NODES)
        from core_lend import validate_lend
        validate_lend(compiler, root, temporary, environment, run, definitions, evaluate, BUFFERS,
                      NODES)
        from core_borrow_induct import validate_borrow_induct
        validate_borrow_induct(compiler, root, temporary, environment, run, definitions, evaluate,
                               BUFFERS, NODES)
        from core_invariant import validate_invariant
        validate_invariant(compiler, root, temporary, environment, run, definitions, evaluate,
                           BUFFERS, NODES)
        from core_nth import validate_nth
        validate_nth(compiler, root, temporary, environment, run, definitions, evaluate, BUFFERS,
                     NODES)
        from core_inout import validate_inout
        validate_inout(compiler, root, temporary, environment, run, definitions, evaluate, BUFFERS,
                       NODES)
        from core_spec import validate_preservation, validate_spec
        validate_spec(root)
        validate_preservation(compiler, root, environment, run)
        from core_vec import validate_vec
        validate_vec(compiler, root, temporary, environment, run)

        example = root / "examples/core_index.jhc"
        command("check", example)
        assert "FILE.jhc" in run([compiler, "core", "--help"]).stdout
        usage = command("check", example, "--no-verify", "--error-format=json", success=False)
        assert usage.returncode == 2 and json.loads(usage.stderr)
        missing = command("check", temporary / "missing.jhc", "--error-format=json", success=False)
        assert missing.returncode == 1 and json.loads(missing.stderr)
        mir = command("emit-mir", example).stdout
        assert mir.count("fn ") == 1 and "fn lookup [lookup]" in mir
        assert "assert" not in mir and "call" not in mir and "Lt" not in mir
        assert mir.count("switch ") == 1 and mir.count("[_") == 1
        llvm = command("emit-llvm", example).stdout
        function = re.search(r'define[^\n]*@"?lookup"?\([^\n]*\).*?\n}', llvm, re.S)
        assert function, llvm
        assert re.search(r'@"?lookup"?\(i64[^,)]*\)', function[0]), function[0]
        assert "malloc" not in function[0] and "panic" not in function[0]

        invalid = {
            "false-proof": "(def bad (Lt 3 3) (decide-lt 3 3))",
            "wrong-index": GET + "(export bad I64 (app get 3 (array (int 1) (int 2) (int 3)) 2 (decide-lt 1 3)))",
            "wrong-length": GET + "(export bad I64 (app get 3 (array (int 1) (int 2)) 1 (decide-lt 1 3)))",
            "missing-proof": GET + "(export bad I64 (app get 3 (array (int 1) (int 2) (int 3)) 1))",
            "symbolic-decide": "(def bad (pi i U64 (Lt i 3)) (lam i U64 (decide-lt i 3)))",
            "wrong-branch-bound": GET + "(export bad (pi i U64 I64) (lam i U64 (if-lt i 4 p (app get 3 (array (int 1) (int 2) (int 3)) i p) (int -1))))",
            "proof-outside-branch": GET + "(export bad (pi i U64 I64) (lam i U64 (if-lt i 3 p (int 0) (app get 3 (array (int 1) (int 2) (int 3)) i p))))",
            "erased-runtime": "(def bad (pi0 p (Lt 0 1) I64) (lam0 p (Lt 0 1) p))",
            "erased-data": "(def bad (pi0 n U64 U64) (lam0 n U64 n))",
            "relevant-proof": "(def bad (pi p (Lt 0 1) I64) (lam p (Lt 0 1) (int 0)))",
            "type-in-type": "(def bad (Type 0) (Type 0))",
            "bad-erased-argument": "(export bad I64 (app (lam0 p (Lt 0 1) (int 7)) (decide-lt 2 1)))",
            "bad-dead-branch": "(export bad I64 (if-lt 0 1 p (int 7) (index (array (int 1)) 3 (decide-lt 3 1))))",
            "forward": "(def first U64 second) (def second U64 1)",
            "recursive": "(def bad (pi x U64 U64) (lam x U64 (app bad x)))",
            "u64-overflow": "(export bad U64 18446744073709551616)",
            "i64-overflow": "(export bad I64 (int 9223372036854775808))",
            "i64-underflow": "(export bad I64 (int -9223372036854775809))",
            "duplicate": "(def same U64 1) (def same U64 2)",
            "duplicate-family": "(inductive F 0) (inductive F 0)",
            "definition-family": "(def F U64 0) (inductive F 0)",
            "family-definition": "(inductive F 0) (def F U64 0)",
            "constructor-family": "(inductive F 0 (C F)) (inductive C 0)",
            "family-constructor": "(inductive F 0 (F F))",
            "constructor-definition": "(inductive F 0 (C F)) (def C U64 0)",
            "definition-constructor": "(def C U64 0) (inductive F 0 (C F))",
            "duplicate-constructor": "(inductive F 0 (C F) (C F))",
            "cross-family-constructor": "(inductive F 0 (C F)) (inductive G 0 (C G))",
            "reserved-family": "(inductive pi 0)",
            "reserved-constructor": "(inductive F 0 (refl F))",
            "negative-arity": "(inductive F -1)",
            "overflow-arity": "(inductive F 4294967296)",
            "unknown-induct-family": "(def bad (Eq 0 0) (induct Missing (Eq 0 0) (refl 0)))",
            "removed-chain-refl": "(def bad (Eq 0 0) (chain-refl 0))",
            "trailing": "(export good I64 (int 1)) )",
            "nesting": "(export bad U64 " + "(app (lam x U64 x) " * 140 + "0" + ")" * 140 + ")",
        }
        for name, source in invalid.items():
            path = temporary / f"{name}.jhc"
            path.write_text(source)
            result = command("check", path, "--error-format=json", success=False)
            assert result.returncode == 1, result.stderr
            diagnostic = json.loads(result.stderr)
            assert "core:" in result.stderr and diagnostic, result.stderr
            # Code generation must fail too, before producing an object.
            obj = temporary / f"{name}.o"
            command("emit-obj", path, "-o", str(obj), success=False)
            assert not obj.exists()

        for name, source in {
            "foreign-proof": "(export bad (pi0 p (Lt 0 1) I64) (lam0 p (Lt 0 1) (int 1)))",
            "foreign-array": "(export bad (pi xs (Array 0) I64) (lam xs (Array 0) (int 1)))",
        }.items():
            path = temporary / f"{name}.jhc"
            path.write_text(source)
            command("check", path)
            command("emit-mir", path, success=False)
        command("check", example, "--no-verify", success=False)

        # Closed proof computation, higher-order beta reduction, universe
        # separation, arbitrary runtime indices and nested binder capture.
        source = GET + """
(def id (pi T (Type 0) (pi x T T)) (lam T (Type 0) (lam x T x)))
(def evidence (pi i U64 (pi n U64 (pi0 p (Lt i n) (Lt i n))))
  (lam i U64 (lam n U64 (lam0 p (Lt i n) p))))
(export closed I64 (app get 1 (array (int -9223372036854775808)) 0 (app evidence 0 1 (decide-lt 0 1))))
(export identity (pi x U64 U64) (lam x U64 (app id U64 x)))
"""
        rng = random.Random(0xC0DE)
        names = []
        for number in range(24):
            values = [rng.randrange(-10000, 10000) for _ in range(number % 9)]
            elements = "(array " + " ".join(f"(int {x})" for x in values) + ")"
            body = f"(if-lt i {len(values)} p (app get {len(values)} {elements} i (app evidence i {len(values)} p)) (int -1))"
            # The inner proof binder shadows the outer proof binder. Its
            # index still refers to the correct runtime argument after beta.
            if number % 2:
                body = f"(if-lt i 18446744073709551615 p {body} (int -1))"
            name = f"select_{number}"
            names.append(name)
            source += f"\n(export {name} (pi i U64 I64) (lam i U64 {body}))\n"
        path = temporary / "program.jhc"
        path.write_text(source)
        reference = {}
        for _, name, _, body in definitions(source):
            reference[name] = evaluate(body, reference.copy())
        command("check", path)
        host = "aarch64" if platform.machine() in ("aarch64", "arm64") else "x86_64"
        for target, machine in (("x86_64", 62), ("aarch64", 183)):
            for level in ("-O0", "-O2"):
                obj = temporary / f"{target}{level}.o"
                command("emit-obj", path, "--target", target, level, "-o", str(obj))
                data = obj.read_bytes()
                assert data[:4] == b"\x7fELF" and struct.unpack_from("<H", data, 18)[0] == machine
                if target != host:
                    continue
                library = temporary / f"test{level}.so"
                cc = shlex.split(os.environ.get("JIHOO_CC", "clang"))
                run([*cc, "-shared", str(obj), "-o", str(library)])
                native = ctypes.CDLL(str(library))
                native.closed.restype = ctypes.c_int64
                assert native.closed() == -(1 << 63)
                native.identity.argtypes = [ctypes.c_uint64]
                native.identity.restype = ctypes.c_uint64
                for value in (0, 1, (1 << 63), (1 << 64) - 1):
                    assert native.identity(value) == value
                for name in names:
                    function = getattr(native, name)
                    function.argtypes = [ctypes.c_uint64]
                    function.restype = ctypes.c_int64
                    for value in [*range(12), (1 << 63) - 1, 1 << 63, (1 << 64) - 1,
                                  *(rng.getrandbits(64) for _ in range(30))]:
                        assert function(value) == reference[name](value), (name, value)
    print(f"dependent core: both targets/profiles, native differential execution, {len(invalid)} rejections and proof erasure passed")


if __name__ == "__main__":
    main()
