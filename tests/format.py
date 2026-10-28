#!/usr/bin/env python3
"""Check formatting, syntax preservation, comments, idempotence and emitted IR."""

import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def run(compiler, *args, env=None):
    return subprocess.run([str(compiler), *map(str, args)], cwd=ROOT,
                          capture_output=True, env=env, timeout=120)


def comments(source):
    """Extract exact comment bytes independently of the compiler lexer."""
    result = []
    i = 0
    while i < len(source):
        if source[i] in (ord('"'), ord("'")):
            quote = source[i]
            i += 1
            while i < len(source) and source[i] != quote:
                i += 2 if source[i] == ord("\\") else 1
            i += 1
        elif source[i:i + 2] == b"//":
            end = source.find(b"\n", i)
            if end < 0:
                end = len(source)
            result.append(source[i:end])
            i = end
        elif source[i:i + 2] == b"/*":
            start = i
            i += 2
            depth = 1
            while depth:
                if source[i:i + 2] == b"/*":
                    depth += 1
                    i += 2
                elif source[i:i + 2] == b"*/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            result.append(source[start:i])
        else:
            i += 1
    return result


def syntax(dump):
    # The AST dump encodes strings as hex. Only source spans use N:N.
    return re.sub(rb" \d+:\d+", b"", dump)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "out/jihoo")
    parser.add_argument("--external", type=Path, help="optionally include an external jihoo project")
    args = parser.parse_args()
    compiler = args.compiler.resolve()
    files = []
    for directory in ["compiler", "lib", "examples", "tests", "experimental", "experiments", "benchmarks"]:
        files.extend((path, path.relative_to(ROOT)) for path in sorted((ROOT / directory).rglob("*.jh")))
    if args.external:
        project = args.external.resolve()
        files.extend((path, Path("external") / path.relative_to(project))
                     for path in sorted(project.rglob("*.jh")))

    valid = invalid = compared = 0
    with tempfile.TemporaryDirectory(prefix="jihoo-format-") as directory:
        mirror = Path(directory)
        for original, relative in files:
            ast = run(compiler, "emit-ast", original)
            formatted = run(compiler, "fmt", original)
            if ast.returncode:
                assert formatted.returncode == ast.returncode and not formatted.stdout, original
                assert formatted.stderr == ast.stderr, original
                invalid += 1
                continue
            assert formatted.returncode == 0 and not formatted.stderr, (original, formatted.stderr)
            assert comments(original.read_bytes()) == comments(formatted.stdout), original
            target = mirror / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(formatted.stdout)
            second = run(compiler, "fmt", target)
            assert second.returncode == 0 and second.stdout == formatted.stdout and not second.stderr, original
            after = run(compiler, "emit-ast", target)
            assert after.returncode == 0 and syntax(ast.stdout) == syntax(after.stdout), original
            check = run(compiler, "fmt", target, "--check")
            assert check.returncode == 0 and not check.stdout and not check.stderr, original
            valid += 1

        golden = run(compiler, "fmt", "tests/format/input.jh")
        assert golden.stdout == (ROOT / "tests/format/expected.txt").read_bytes(), golden.stdout
        needs_formatting = run(compiler, "fmt", "tests/format/input.jh", "--check")
        assert needs_formatting.returncode == 1 and not needs_formatting.stdout
        assert b"needs formatting" in needs_formatting.stderr

        environment = os.environ.copy()
        environment["JIHOO_PATH"] = str(mirror / "lib")
        # Same executable representation after formatting every imported module,
        # including the compiler and its standard library, on both targets.
        programs = [ROOT / "compiler/main.jh", ROOT / "tests/format/input.jh"]
        programs += sorted((ROOT / "tests/run").glob("*.jh"))
        programs += sorted((ROOT / "examples").glob("*.jh"))
        if args.external:
            programs += [project / "src/main.jh"]
        for original in programs:
            relative = (Path("external") / original.relative_to(project)
                        if args.external and original.is_relative_to(project) else original.relative_to(ROOT))
            for target in ["x86_64", "aarch64"]:
                before = run(compiler, "emit-llvm", original, "--target", target)
                after = run(compiler, "emit-llvm", mirror / relative, "--target", target, env=environment)
                assert before.returncode == after.returncode == 0, (original, target, before.stderr, after.stderr)
                assert before.stdout == after.stdout and not before.stderr and not after.stderr, (original, target)
                compared += 1

        # Formatting needs neither imports nor backend tools, even for modules.
        environment.update(JIHOO_LLVM="/no-library.so", JIHOO_CC="/no-compiler", JIHOO_LD="/no-linker")
        source = mirror / "standalone.jh"
        source.write_bytes(b'import missing\nconst BAD = comptime trap()\nfn main(){return\n(1)}\n')
        result = run(compiler, "fmt", source, env=environment)
        assert result.returncode == 0 and not result.stderr, result.stderr
        assert b"return\n" in result.stdout
        source.write_bytes(result.stdout)
        assert run(compiler, "fmt", source, "--check", env=environment).returncode == 0

        # Significant line starts, nested prefix operators, CRLF, comments,
        # tuple fields, attributes, empty input and final-newline handling.
        for text in [b"", b" \t\n\n", b"// comment", b"/* a /* b */ c */",
                     b"fn f(){\r\n\tlet x=1\r\n}\r\n",
                     b"fn f(){let x=1+\n2\nx\n.foo()\n}\n",
                     b"fn f(){var n=1;let p=& &n;let q=**p}\n",
                     b"fn f(x:i64){match x{0..=9=>{},_=>{}}}\n",
                     b"fn f(){let pair=(1,(2,3));println(pair.1.0)}\n",
                     b"#[derive(Eq)]\nstruct S{x:i64}\n",
                     b"// heading\r\nfn f(){/*x\r\ny*/}\r\n"]:
            source.write_bytes(text)
            first = run(compiler, "fmt", source)
            assert first.returncode == 0 and not first.stderr, (text, first.stderr)
            assert comments(first.stdout) == comments(text), text
            source.write_bytes(first.stdout)
            second = run(compiler, "fmt", source)
            assert second.returncode == 0 and second.stdout == first.stdout, text

        for options in [["-o", str(mirror / "no-output")], ["--keep-ll"], ["-lmissing"], ["--", "arg"]]:
            result = run(compiler, "fmt", source, *options)
            assert result.returncode == 2 and not result.stdout and b"fmt does not accept" in result.stderr
        assert not (mirror / "no-output").exists()
        result = run(compiler, "fmt", source, "-o")
        assert result.returncode == 2 and not result.stdout and b"fmt does not accept" in result.stderr

        # Profile selection must follow attribute syntax, not its whitespace.
        # Compare with the canonical freestanding example on both targets.
        canonical = (ROOT / "examples/freestanding.jh").read_bytes()
        for attribute in [b"#! [ freestanding ]", b"#![\nfreestanding\n]",
                          b"/* leading /* nested */ comment */\n#! [ freestanding ]"]:
            source.write_bytes(canonical.replace(b"#![freestanding]", attribute, 1))
            formatted = run(compiler, "fmt", source)
            assert formatted.returncode == 0 and not formatted.stderr, formatted.stderr
            target_file = mirror / "profile.jh"
            target_file.write_bytes(formatted.stdout)
            for target in ["x86_64", "aarch64"]:
                expected = run(compiler, "emit-llvm", "examples/freestanding.jh", "--target", target)
                original = run(compiler, "emit-llvm", source, "--target", target)
                actual = run(compiler, "emit-llvm", target_file, "--target", target)
                assert expected.returncode == original.returncode == actual.returncode == 0
                assert expected.stdout == original.stdout == actual.stdout, (attribute, target)

    print(f"Formatter: {valid} files preserve syntax/comments and are idempotent; "
          f"{invalid} invalid files rejected; {compared} LLVM comparisons passed")


if __name__ == "__main__":
    main()
