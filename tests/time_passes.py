#!/usr/bin/env python3
"""Validate `--time-passes`: phases on standard error, every other output unchanged."""
import argparse
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ROW = re.compile(r"^(\S+(?: \S+)?) +(\d+\.\d{3})s +(\d+\.\d{3})s +(\d+\.\d) MiB$")
FRONT = ["load", "sema", "elaboration", "effects", "borrows"]
BACK = ["IR generation", "LLVM parse", "LLVM optimize", "LLVM emit"]


def run(compiler, *args):
    return subprocess.run([str(compiler), *map(str, args)], cwd=ROOT, capture_output=True, timeout=120)


def phases(text):
    """The table at the start of `text` as {name: (elapsed, cpu, peak)}, and what follows it."""
    lines = text.split("\n")
    assert lines[0].split() == ["phase", "elapsed", "cpu", "peak"], text
    table = {}
    for i, line in enumerate(lines[1:], 1):
        m = ROW.match(line)
        assert m, (line, text)
        assert m[1] not in table, text
        table[m[1]] = (float(m[2]), float(m[3]), float(m[4]))
        if m[1] == "total":
            break
    total = table.pop("total")
    # Rounding: each phase is truncated to milliseconds.
    assert total[0] + 0.0005 >= sum(p[0] for p in table.values()) >= total[0] - 0.001 * (len(table) + 1), text
    assert total[2] == max(p[2] for p in table.values()), text
    return list(table), "\n".join(lines[i + 1:])


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "out/jihoo")
    args = parser.parse_args()
    compiler = args.compiler.resolve()
    with tempfile.TemporaryDirectory(prefix="jihoo-time-passes-") as directory:
        tmp = Path(directory)
        source = tmp / "hello.jh"
        source.write_text('fn main() {\n    println("hello")\n}\n')

        result = run(compiler, "check", source, "--time-passes")
        assert result.returncode == 0 and not result.stdout, result.stderr
        names, rest = phases(result.stderr.decode())
        assert names == FRONT and rest == "", result.stderr

        for command in ["emit-llvm", "emit-mir"]:
            plain = run(compiler, command, source)
            timed = run(compiler, command, source, "--time-passes")
            assert plain.returncode == timed.returncode == 0 and plain.stdout == timed.stdout
            names, rest = phases(timed.stderr.decode())
            assert names == FRONT + [{"emit-llvm": "IR generation", "emit-mir": "MIR text"}[command]]
            assert rest == "" and plain.stderr == b"", timed.stderr

        for target in ["x86_64", "aarch64"]:
            plain, timed = tmp / f"plain-{target}.o", tmp / f"timed-{target}.o"
            assert run(compiler, "emit-obj", source, "--target", target, "-o", plain).returncode == 0
            result = run(compiler, "emit-obj", source, "--target", target, "-o", timed, "--time-passes")
            assert result.returncode == 0 and not result.stdout, result.stderr
            assert plain.read_bytes() == timed.read_bytes()
            assert phases(result.stderr.decode()) == (FRONT + BACK, "")

        exe = tmp / "hello"
        result = run(compiler, "build", source, "-o", exe, "--time-passes")
        assert result.returncode == 0 and not result.stdout, result.stderr
        assert phases(result.stderr.decode()) == (FRONT + BACK + ["link"], "")

        # The program's output and status are its own; the phases end before it runs.
        program = tmp / "exit.jh"
        program.write_text('import std.sys\nfn main() {\n    println("out")\n    eprintln("err")\n    sys.exit(3)\n}\n')
        result = run(compiler, "run", program, "--time-passes")
        assert result.returncode == 3 and result.stdout == b"out\n", result
        assert phases(result.stderr.decode()) == (FRONT + BACK + ["link"], "err\n")

        # Diagnostics follow the phases that ran, unchanged, in both formats.
        cases = [
            ("syntax", "fn main() {\n    let = 1\n}\n", ["load"]),
            ("types", "fn main() {\n    let x: i64 = true\n}\n", ["load", "sema"]),
            ("moves", "fn take(sink s: String) {}\n\nfn main() {\n    let s = String.from(\"a\")\n"
             "    take(s)\n    println(s)\n}\n", FRONT),
        ]
        for name, text, ran in cases:
            path = tmp / f"{name}.jh"
            path.write_text(text)
            for fmt in ["--error-format=text", "--error-format=json"]:
                plain = run(compiler, "build", path, fmt, "-o", exe)
                timed = run(compiler, "build", path, fmt, "-o", exe, "--time-passes")
                assert plain.returncode == timed.returncode == 1, (name, plain.stderr)
                assert plain.stdout == timed.stdout == b""
                assert phases(timed.stderr.decode()) == (ran, plain.stderr.decode()), (name, timed.stderr)

        for command in ["fmt", "emit-tokens", "emit-ast", "emit-program"]:
            result = run(compiler, command, source, "--time-passes")
            assert result.returncode == 2 and b"--time-passes requires" in result.stderr, result.stderr
        assert b"--time-passes" in run(compiler, "--help").stdout


if __name__ == "__main__":
    main()
