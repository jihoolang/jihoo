#!/usr/bin/env python3
"""Validate compiler JSON diagnostics with an independent JSON parser."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


KINDS = {"source", "usage", "io", "backend", "format"}


def run(compiler, *args, env=None):
    return subprocess.run(
        [str(compiler), *map(str, args)], cwd=ROOT, capture_output=True,
        env=env, timeout=90,
    )


def document(data):
    # A single complete JSON document, not a mix of JSON and text messages.
    value = json.loads(data)
    assert value["version"] == 1, value
    diagnostics = value["diagnostics"]
    assert len(diagnostics) == min(value["error_count"], 20), value
    assert value["truncated"] == (value["error_count"] > 20), value
    for diagnostic in diagnostics:
        assert diagnostic["severity"] == "error", diagnostic
        assert diagnostic["kind"] in KINDS, diagnostic
        assert isinstance(diagnostic["message"], str), diagnostic
        for note in diagnostic["notes"]:
            assert isinstance(note["message"], str), note
    return value


def position(source, offset):
    return {
        "byte": offset,
        "line": source[:offset].count(b"\n") + 1,
        "column": offset - source[:offset].rfind(b"\n"),
    }


def validate_span(span):
    if span is None:
        return
    source = (ROOT / span["file"]).read_bytes()
    start, end = span["start"]["byte"], span["end"]["byte"]
    assert 0 <= start <= end <= len(source), span
    assert span["start"] == position(source, start), span
    assert span["end"] == position(source, end), span


def compare(text, structured):
    cursor = 0
    for diagnostic in structured["diagnostics"]:
        validate_span(diagnostic["span"])
        items = [("error", diagnostic)]
        items += [("note", note) for note in diagnostic["notes"]]
        for severity, item in items:
            span = item["span"]
            validate_span(span)
            location = ""
            if span is not None:
                start = span["start"]
                location = f'{span["file"]}:{start["line"]}:{start["column"]}: '
            expected = f'{severity}: {location}{item["message"]}'
            found = text.find(expected, cursor)
            assert found >= 0, item
            cursor = found + len(expected)
    assert sum(len(d["notes"]) for d in structured["diagnostics"]) == len(
        re.findall(r"^note: ", text, re.MULTILINE))
    summary = re.search(r"\n\n(\d+) errors(?: \(the first \d+ shown\))?$", text)
    assert structured["error_count"] == (int(summary[1]) if summary else 1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "out/jihoo")
    args = parser.parse_args()
    compiler = args.compiler.resolve()

    negative_cases = 0
    for source in sorted((ROOT / "tests/fail").glob("*.jh")):
        path = source.relative_to(ROOT)
        text = run(compiler, "check", path)
        structured = run(compiler, "check", path, "--error-format=json")
        assert text.returncode == structured.returncode == 1, path
        assert not text.stdout and not structured.stdout, path
        compare(text.stderr.decode("utf-8", errors="replace"), document(structured.stderr))
        negative_cases += 1

    # Exercise lexical, parse and import errors, and all frontend entry points.
    for command, path in [
        ("emit-tokens", "tests/selfhost/lex/at.jh"),
        ("emit-ast", "tests/selfhost/parse/expect_name.jh"),
        ("emit-program", "tests/selfhost/load/bad_import.jh"),
        ("fmt", "tests/selfhost/lex/at.jh"),
        ("fmt", "tests/selfhost/parse/expect_name.jh"),
        ("build", "tests/fail/use_after_move.jh"),
        ("run", "tests/fail/use_after_move.jh"),
        ("emit-mir", "tests/fail/use_after_move.jh"),
        ("emit-llvm", "tests/fail/use_after_move.jh"),
        ("emit-obj", "tests/fail/use_after_move.jh"),
    ]:
        text = run(compiler, command, path)
        structured = run(compiler, command, path, "--error-format=json")
        assert text.returncode == structured.returncode == 1, (command, path)
        assert not structured.stdout, (command, path)
        compare(text.stderr.decode("utf-8", errors="replace"), document(structured.stderr))

    default = run(compiler, "check", "tests/fail/use_after_move.jh")
    explicit = run(compiler, "check", "--error-format=text", "tests/fail/use_after_move.jh")
    assert (default.returncode, default.stdout, default.stderr) == (
        explicit.returncode, explicit.stdout, explicit.stderr)
    repeated = run(compiler, "check", "tests/fail/use_after_move.jh",
                   "--error-format=json", "--error-format=text")
    assert (default.returncode, default.stdout, default.stderr) == (
        repeated.returncode, repeated.stdout, repeated.stderr)
    invalid = run(compiler, "check", "examples/hello.jh", "--error-format=invalid")
    assert invalid.returncode == 2 and b"unknown option" in invalid.stderr

    # Both renderers may be asked to report a file that could not be read.
    with tempfile.TemporaryDirectory(prefix="jihoo-diagnostics-") as directory:
        missing = Path(directory) / "missing.jh"
        for command in ["check", "fmt", "emit-tokens", "emit-ast"]:
            result = run(compiler, command, missing, "--error-format=json")
            assert result.returncode == 1 and not result.stdout
            value = document(result.stderr)
            assert value["diagnostics"][0]["span"] is None, value
            assert value["diagnostics"][0]["kind"] == "io", value
            assert "cannot read" in value["diagnostics"][0]["message"], value

        # Every unsuccessful invocation has one document: usage errors,
        # backend and linker errors, and files that need formatting.
        failures = [
            (["check"], 2, "usage", "no source file"),
            (["check", "examples/hello.jh", "--bogus"], 2, "usage", "unknown option `--bogus`"),
            (["check", "examples/hello.jh", "-o", "x"], 2, "usage", "check does not accept"),
            (["frobnicate", "examples/hello.jh"], 2, "usage", "unknown command `frobnicate`"),
            (["build", "examples/hello.jh", "--target", "sparc"], 2, "usage", "unknown target"),
            (["build", "examples/hello.jh", "no-such-input.o", "-o", Path(directory) / "x"],
             1, "backend", "no-such-input.o"),
            (["emit-llvm", "examples/hello.jh", "-o", Path(directory) / "none" / "x.ll"],
             1, "io", "cannot write"),
        ]
        for arguments, code, kind, message in failures:
            text = run(compiler, *arguments)
            # The format option may come after the failing option.
            result = run(compiler, *arguments, "--error-format=json")
            assert text.returncode == result.returncode == code, (arguments, result)
            assert not text.stderr.startswith(b"{"), arguments
            value = document(result.stderr)
            assert len(value["diagnostics"]) == 1, value
            diagnostic = value["diagnostics"][0]
            assert diagnostic["kind"] == kind, (arguments, value)
            assert message in diagnostic["message"], (arguments, value)
            assert diagnostic["span"] is None and "usage:" not in diagnostic["message"], value
        # After `--`, the option belongs to the program.
        result = run(compiler, "check", "--", "--error-format=json")
        assert result.returncode == 2 and not result.stderr.startswith(b"{"), result

        unformatted = Path(directory) / "unformatted.jh"
        unformatted.write_bytes(b"fn main() {\n  let x = 1\n}\n")
        text = run(compiler, "fmt", unformatted, "--check")
        result = run(compiler, "fmt", unformatted, "--check", "--error-format=json")
        assert text.returncode == result.returncode == 1 and b"needs formatting" in text.stderr
        value = document(result.stderr)
        diagnostic = value["diagnostics"][0]
        assert diagnostic["kind"] == "format", value
        span = diagnostic["span"]
        assert span["file"] == str(unformatted) and span["start"] == position(
            unformatted.read_bytes(), 14), span

        # UTF-8 before an error must not be mistaken for UTF-16 columns.
        source = Path(directory) / '가"\\name.jh'
        source.write_text('fn main() { let text = "가"; println(missing) }\n', encoding="utf-8")
        result = run(compiler, "check", source, "--error-format=json")
        assert result.returncode == 1 and not result.stdout
        value = document(result.stderr)
        span = value["diagnostics"][0]["span"]
        assert span["file"] == str(source), span
        assert span["start"]["byte"] == source.read_bytes().index(b"missing"), span
        validate_span(span)

    environment = os.environ.copy()
    environment.update(JIHOO_LLVM="/no-library.so", JIHOO_CC="/no-compiler", JIHOO_LD="/no-linker")
    for options in [["--error-format=json"], ["--error-format=text"],
                    ["--error-format=json", "--error-format=text"]]:
        result = run(compiler, "check", "examples/hello.jh", *options, env=environment)
        assert result.returncode == 0 and not result.stdout and not result.stderr

    rendered = run(compiler, "run", "tests/diagnostics/render.jh", "-I", "compiler")
    assert rendered.returncode == 0 and not rendered.stderr, rendered.stderr
    values = [document(line) for line in rendered.stdout.splitlines()]
    assert len(values) == 4
    assert all(d["kind"] == "source" for v in values for d in v["diagnostics"])
    diagnostic = values[0]["diagnostics"][0]
    assert diagnostic["message"] == 'quote=" slash=\\ controls=\0\t\n\r\x1f 가 \ufffd\ufffd'
    span = diagnostic["span"]
    source = "\t가x\r\nsecond\n".encode("utf-8")
    assert span["file"] == 'path"\\\n가\ufffd.jh', span
    assert span["start"] == position(source, 1), span
    assert span["end"] == position(source, 10), span
    assert diagnostic["notes"][0]["span"]["start"] == position(source, 0)
    assert diagnostic["notes"][1] == {"message": "instance context", "span": None}
    assert values[1]["error_count"] == 23 and values[1]["truncated"] is True
    assert [d["message"] for d in values[1]["diagnostics"]] == [str(i) for i in range(20)]
    last_span = values[1]["diagnostics"][-1]["span"]
    assert last_span["start"] == last_span["end"] == position(source, len(source))
    assert values[2]["diagnostics"][0]["span"] is None
    reversed_span = values[3]["diagnostics"][0]["span"]
    assert reversed_span["start"] == reversed_span["end"] == position(source, 10)
    print(f"JSON diagnostics: {negative_cases} negative programs, frontend commands and renderer edge cases passed")


if __name__ == "__main__":
    main()
