#!/usr/bin/env python3
"""Check formatting, syntax preservation, comments, idempotence and emitted IR."""

import argparse
import json
import os
from pathlib import Path
import re
import random
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
    for directory in ["compiler", "lib", "examples", "tests", "benchmarks"]:
        # A directory named like a source, as the loader tests have, is traversed.
        files.extend((path, path.relative_to(ROOT)) for path in sorted((ROOT / directory).rglob("*.jh"))
                     if not path.is_dir())
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
        programs = [ROOT / "compiler/main.jh", ROOT / "tests/format/input.jh", ROOT / "tests/format/wrap.jh"]
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

        # Layout choices use parser list boundaries, then reparse identically.
        wrapping = ROOT / "tests/format/wrap.jh"
        golden = run(compiler, "fmt", wrapping, "--width", "40")
        assert golden.returncode == 0 and not golden.stderr, golden.stderr
        assert golden.stdout == (ROOT / "tests/format/wrap-40.txt").read_bytes(), golden.stdout
        source.write_bytes(golden.stdout)
        checked = run(compiler, "fmt", source, "--check", "--width", "40")
        assert checked.returncode == 0 and not checked.stdout and not checked.stderr
        changed = run(compiler, "fmt", wrapping, "--check", "--width", "40")
        assert changed.returncode == 1 and not changed.stdout and b"needs formatting" in changed.stderr
        comparison = run(compiler, "run", "tests/format/syntax.jh", "-I", "compiler")
        assert comparison.returncode == 0 and not comparison.stderr, comparison.stderr
        assert comparison.stdout == b"syntax comparison checks passed\n"
        for target in ["x86_64", "aarch64"]:
            original = run(compiler, "emit-llvm", wrapping, "--target", target)
            actual = run(compiler, "emit-llvm", source, "--target", target)
            assert original.returncode == actual.returncode == 0 and original.stdout == actual.stdout

        cases = [
            b"fn f(){let result=outer(inner(first_long_argument,second_long_argument),third_long_argument)}\n",
            b"fn f(){let a=[first_long_name, /* inline */ second_long_name, third_long_name,]}\n",
            b"fn f(){call(first_long_argument, // stays with the first argument\nsecond_long_argument,third_long_argument)}\n",
            b"fn f(){call(/* before first */ first_long_argument, /* before last */ second_long_argument /* after last */)}\n",
            b"fn f(){let r=S{field:for index, item in long_collection_name{use_pair(index,item)},other:long_value_name}}\n",
            b"fn f(){call(fn(){return\n(1)},first_long_argument)}\n",
            b"fn f(){call(fn(){let x=1\n(2)},first_long_argument)}\n",
            b"fn f(){call(fn(){let x=1\n[2]},first_long_argument)}\n",
            b"fn f(){call(fn(){let x=1\n?},first_long_argument)}\n",
            b"fn f(x:fnptr(i64,i64,...)->i64){let a=[1;very_long_repeat_count]}\n",
            b"fn f(){let r=(very_long_first, very_long_second,);let s=S{a:r.0,b:r.1}}\n",
            b"enum E{First(i64,i64),Second(i64,i64)}\nfn f(){let E.First(a,b)=value}\n",
            b"fn f(){let r=S{very_long_first:i64;very_long_second:i64}}\n",
            "fn f(){call(가)}\n".encode(),  # invalid syntax remains an error
        ]
        rng = random.Random(73)
        for _ in range(40):
            values = [f"argument_{i}_with_a_long_name" for i in range(rng.randint(1, 7))]
            nested = ",".join(values)
            for _ in range(rng.randint(0, 4)):
                nested = "combine(" + nested + ",last_argument)"
            cases.append(("fn generated(){let result=[" + nested + ",final_argument]}\n").encode())
        wrapped = 0
        for text in cases:
            source.write_bytes(text)
            before = run(compiler, "emit-ast", source)
            for width in [20, 40, 80, 1000]:
                first = run(compiler, "fmt", source, "--width", str(width))
                if before.returncode:
                    assert first.returncode == before.returncode and first.stderr == before.stderr
                    continue
                assert first.returncode == 0 and not first.stderr, (text, width, first.stderr)
                assert comments(first.stdout) == comments(text), (text, width)
                target_file = mirror / "wrapped.jh"
                target_file.write_bytes(first.stdout)
                second = run(compiler, "fmt", target_file, "--width", str(width))
                after = run(compiler, "emit-ast", target_file)
                assert second.returncode == 0 and second.stdout == first.stdout, (text, width)
                assert after.returncode == 0 and syntax(before.stdout) == syntax(after.stdout), (text, width)
                wrapped += 1
        for options in [["--width"], ["--width", "19"], ["--width", "1001"],
                        ["--width", "-1"], ["--width", "abc"], ["--width", "20.5"],
                        ["--width", "18446744073709551716"]]:
            bad = run(compiler, "fmt", source, *options)
            assert bad.returncode == 2 and not bad.stdout and b"--width" in bad.stderr, options

        # Several files and directories are checked or rewritten together.
        project = mirror / "project"
        (project / "sub").mkdir(parents=True)
        (project / ".hidden").mkdir()
        unformatted = b"fn main() {\n  let x=1\n}\n"
        formatted_text = b"fn main() {\n    let x = 1\n}\n"
        (project / "a.jh").write_bytes(unformatted)
        (project / "sub/b.jh").write_bytes(formatted_text)
        (project / "sub/c.jh").write_bytes(b"fn main( {\n")
        (project / ".hidden/d.jh").write_bytes(unformatted)
        (project / "notes.txt").write_bytes(b"not jihoo")
        (project / "sub/loop").symlink_to("..")
        printed = run(compiler, "fmt", project)
        assert printed.returncode == 2 and not printed.stdout and b"--check or --write" in printed.stderr
        both = run(compiler, "fmt", project, "--check", "--write")
        assert both.returncode == 2 and b"not both" in both.stderr
        check = run(compiler, "fmt", project, "--check")
        lines = check.stderr.decode().splitlines()
        assert check.returncode == 1 and not check.stdout, check
        assert lines[0] == f"{project / 'a.jh'}: needs formatting", lines
        assert lines[1].startswith(f"error: {project / 'sub/c.jh'}:1:10: "), lines
        assert b"hidden" not in check.stderr and b"loop" not in check.stderr
        structured = run(compiler, "fmt", project, "--check", "--error-format=json")
        value = json.loads(structured.stderr)
        assert structured.returncode == 1 and value["error_count"] == 2, value
        assert [d["kind"] for d in value["diagnostics"]] == ["format", "source"], value
        explicit = run(compiler, "fmt", project / "sub/b.jh", project / "a.jh", "--check")
        assert explicit.returncode == 1 and explicit.stderr.decode().count("needs formatting") == 1
        written = run(compiler, "fmt", project, "--write")
        assert written.returncode == 1 and not written.stdout and b"sub/c.jh:1:10" in written.stderr
        assert (project / "a.jh").read_bytes() == formatted_text
        assert (project / "sub/b.jh").read_bytes() == formatted_text
        assert (project / ".hidden/d.jh").read_bytes() == unformatted
        assert (project / "notes.txt").read_bytes() == b"not jihoo"
        (project / "sub/c.jh").unlink()
        again = run(compiler, "fmt", project, "--check")
        assert again.returncode == 0 and not again.stdout and not again.stderr, again
        missing = run(compiler, "fmt", project / "missing.jh", project, "--check")
        assert missing.returncode == 1 and b"error: cannot read" in missing.stderr

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
          f"{invalid} invalid files rejected; {compared} LLVM comparisons; {wrapped} wrapping cases passed")


if __name__ == "__main__":
    main()
