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


def evaluate(term, env):
    """An independent named-variable evaluator; the compiler uses de Bruijn terms."""
    if isinstance(term, str):
        return int(term) if term.isdecimal() else env[term]
    head, *args = term
    if head in ("lam", "lam0"):
        name, _, body = args
        return lambda value: evaluate(body, {**env, name: value})
    if head == "app":
        value = evaluate(args[0], env)
        for argument in args[1:]:
            value = value(evaluate(argument, env))
        return value
    if head == "int":
        return int(args[0])
    if head == "array":
        return [evaluate(x, env) for x in args]
    if head == "decide-lt":
        a, b = (evaluate(x, env) for x in args)
        assert a < b
        return (a, b)
    if head == "if-lt":
        a, b = evaluate(args[0], env), evaluate(args[1], env)
        return evaluate(args[3], {**env, args[2]: (a, b)}) if a < b else evaluate(args[4], env)
    if head == "index":
        array, index, proof = (evaluate(x, env) for x in args)
        assert proof == (index, len(array)) and 0 <= index < len(array)
        return array[index]
    raise AssertionError(f"unsupported reference term {head}")


GET = """
(def get
 (pi n U64 (pi xs (Array n) (pi i U64 (pi0 p (Lt i n) I64))))
 (lam n U64 (lam xs (Array n) (lam i U64 (lam0 p (Lt i n) (index xs i p))))))
"""


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--compiler", required=True)
    args = parser.parse_args()
    compiler = str(Path(args.compiler).resolve())
    root = Path(__file__).resolve().parents[1]
    os.chdir(root)
    environment = {**os.environ, "HORN": "/unavailable", "AGDA": "/unavailable",
                   "SCHEMATIC_KERNEL": "/unavailable"}
    with tempfile.TemporaryDirectory(prefix="jihoo-core-") as directory:
        temporary = Path(directory)

        def command(action, path, *options, success=True):
            return run([compiler, "core", action, str(path), *options],
                       success=success, env=environment)

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
        for _, name, _, body in read_terms(source):
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
