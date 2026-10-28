#!/usr/bin/env python3
"""Validate evaluator measurements independently of diagnostic rendering."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def run(compiler, *args):
    return subprocess.run([str(compiler), *map(str, args)], cwd=ROOT, capture_output=True, timeout=90)


def validate(path):
    report = json.loads(path.read_bytes())
    assert report["version"] == 1
    assert report["limits"] == {"steps": 1000000, "allocation_bytes": 67108864, "allocations": 1000000, "active_calls": 128}
    for e in report["evaluations"]:
        assert 0 < e["steps"] <= report["limits"]["steps"]
        assert 0 <= e["allocation_bytes"] <= report["limits"]["allocation_bytes"]
        assert e["allocations"] <= report["limits"]["allocations"]
        assert 0 < e["max_active_calls"] <= report["limits"]["active_calls"]
        for key in ["steps", "allocation_bytes", "allocations"]:
            assert sum(f[key] for f in e["functions"]) == e[key], (key, e)
        for span in [e["span"], *(f["span"] for f in e["functions"])]:
            if span is not None:
                source = (ROOT / span["file"]).read_bytes()
                assert 0 <= span["start"]["byte"] <= span["end"]["byte"] <= len(source)
    return report


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "out/jihoo")
    args = parser.parse_args()
    compiler = args.compiler.resolve()
    with tempfile.TemporaryDirectory(prefix="jihoo-comptime-") as directory:
        tmp = Path(directory)
        source = tmp / 'report "한글".jh'
        source.write_text('''fn sum(n: i64) -> i64 {
    var values = Vec(i64).new()
    for i in 0..n { values.push(i) }
    var total = 0
    for x in values { total += x }
    total
}
const TOTAL = sum(12)
fn main() { println(TOTAL) }
''')
        plain = run(compiler, "check", source)
        assert plain.returncode == 0 and not plain.stdout and not plain.stderr, plain.stderr
        assert list(tmp.iterdir()) == [source]
        output = tmp / "resources.json"
        for target in ["x86_64", "aarch64"]:
            result = run(compiler, "check", source, "--target", target, "--comptime-report", output)
            assert result.returncode == 0 and not result.stdout and not result.stderr, result.stderr
            report = validate(output)
            assert report["target"] == target and report["checked_arithmetic"] is True
            assert report["evaluations"] and all(e["success"] for e in report["evaluations"])
            assert any("std.sys.alloc_bytes" in f["name"] for e in report["evaluations"] for f in e["functions"])
        result = run(compiler, "check", source, "--release", "--comptime-report", output)
        assert result.returncode == 0
        assert validate(output)["checked_arithmetic"] is False
        plain = run(compiler, "emit-llvm", source)
        profiled = run(compiler, "emit-llvm", source, "--comptime-report", output)
        assert plain.returncode == profiled.returncode == 0 and plain.stdout == profiled.stdout
        empty = tmp / "empty.jh"
        empty.write_text("fn main() {}\n")
        result = run(compiler, "check", empty, "--comptime-report", output)
        assert result.returncode == 0 and validate(output)["evaluations"] == []

        for name in ["steps", "depth", "memory", "invalid_pointer", "lifetime"]:
            path = Path(f"tests/fail/comptime_eval_{name}.jh")
            result = run(compiler, "check", path, "--error-format=json", "--comptime-report", output)
            assert result.returncode == 1 and not result.stdout, result.stderr
            diagnostics = json.loads(result.stderr)["diagnostics"]
            notes = [n for d in diagnostics for n in d["notes"]]
            assert any(n["message"] == "while evaluating this compile-time obligation" and n["span"] for n in notes)
            assert any(n["message"].startswith("compile-time resources: ") for n in notes)
            report = validate(output)
            failures = [e for e in report["evaluations"] if not e["success"]]
            assert failures, report
            if name == "steps":
                assert all(e["steps"] == report["limits"]["steps"] for e in failures)
            if name == "depth":
                assert any(e["max_active_calls"] == report["limits"]["active_calls"] for e in failures)
        missing = run(compiler, "check", source, "--comptime-report")
        assert missing.returncode == 2 and b"requires a path" in missing.stderr
        original = source.read_bytes()
        overwrite = run(compiler, "check", source, "--comptime-report", source)
        assert overwrite.returncode == 2 and b"overwrite a source file" in overwrite.stderr
        assert source.read_bytes() == original
        for command in ["fmt", "emit-tokens", "emit-ast", "emit-program"]:
            rejected = run(compiler, command, source, "--comptime-report", output)
            assert rejected.returncode == 2 and b"requires checking or code generation" in rejected.stderr
        nested = tmp / "nested.jh"
        nested.write_text("fn forever() -> i64 { loop {} }\nfn staged(comptime n: i64) -> i64 { comptime forever() }\nconst VALUE = staged(4)\nfn main() { println(VALUE) }\n")
        failed = run(compiler, "check", nested, "--error-format=json", "--comptime-report", output)
        assert failed.returncode == 1
        notes = [n for d in json.loads(failed.stderr)["diagnostics"] for n in d["notes"]]
        assert any(n["message"] == "required by this compile-time expression" and n["span"]["start"]["line"] == 3 for n in notes), notes
    print("Compile-time resources, call context, JSON diagnostics and unchanged IR passed")


if __name__ == "__main__":
    main()
