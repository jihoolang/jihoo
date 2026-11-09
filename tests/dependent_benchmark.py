#!/usr/bin/env python3
"""Structural and executable checks; intentionally no performance thresholds."""
import argparse
import importlib.util
import os
import json
import sys
from unittest.mock import patch
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("benchmark", ROOT / "scripts/benchmark_compile.py")
benchmark = importlib.util.module_from_spec(spec)
spec.loader.exec_module(benchmark)


def require(value, message):
    if not value:
        raise AssertionError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", required=True)
    args = parser.parse_args()
    compiler = str(Path(args.compiler).resolve())
    env = {**os.environ, "JIHOO_PATH": str(ROOT / "lib")}
    with patch.dict(os.environ, {"PATH": ""}):
        require(benchmark.git_revision(ROOT) is None, "missing Git must yield unknown revision")
    with tempfile.TemporaryDirectory(prefix="dependent-bench-test-") as directory:
        temp = Path(directory)
        for kind in benchmark.DEPENDENT:
            for n, entry in ((1, "exports"), (4, "exports"), (4, "fanout"), (16, "exports")):
                source = benchmark.dependent_source(kind, n, entry)
                require(source == benchmark.dependent_source(kind, n, entry), "nondeterministic source")
                require(source.count("export fn consumer_") == n, "wrong consumer count")
                main_source = source.split("fn main()", 1)[1]
                require(main_source.count("consumer_") == (n if entry == "fanout" else 1), "wrong entry fanout")
                require("auto(" not in source, "workload depends on proof automation")
                path = temp / f"{kind}-{entry}-{n}.jh"
                path.write_text(source)
                before = set(temp.iterdir())
                checked = subprocess.run([compiler, "check", str(path)], env=env, capture_output=True, timeout=120)
                require(checked.returncode == 0 and not checked.stdout and not checked.stderr,
                        f"check failed: {checked.stderr!r}")
                require(set(temp.iterdir()) == before, "check wrote output")
                if n == 16:
                    emitted = subprocess.run([compiler, "emit-llvm", str(path)], env=env,
                                             check=True, capture_output=True, text=True, timeout=120)
                    for i in range(n):
                        require(f'define i64 @"consumer_{i}"(' in emitted.stdout,
                                f"export consumer_{i} was not emitted")
                for opt in ("-O0", "-O2"):
                    output = temp / "program"
                    subprocess.run([compiler, "build", opt, str(path), "-o", str(output)], env=env,
                                   check=True, capture_output=True, timeout=120)
                    result = subprocess.run([str(output)], capture_output=True, timeout=30)
                    require(result.returncode == (17 * n if entry == "fanout" else 17), f"wrong runtime result: {result.returncode}")
            for n in (0, -1, 257):
                try:
                    benchmark.dependent_source(kind, n, entry)
                except ValueError:
                    pass
                else:
                    raise AssertionError("invalid size accepted")
        report_path = temp / "report.json"
        command = [sys.executable, str(ROOT / "scripts/benchmark_compile.py"), "--compiler", compiler,
                   "--workload", "dependent-buffer", "--dependent-size", "1", "--dependent-size", "4",
                   "--check-only", "--json", str(report_path)]
        measured = subprocess.run(command, env=env, capture_output=True, timeout=120)
        require(measured.returncode == 0,
                f"benchmark failed: {measured.stdout!r}\n{measured.stderr!r}")
        report = json.loads(report_path.read_text())
        require(len(report["cases"]) == 4, "missing check/full or scaling case")
        require(len(report["compiler_invocation_sha256"]) == 64, "missing compiler identity")
        require(set(report["generated"]) == {"dependent-buffer-exports-1", "dependent-buffer-exports-4"}, "wrong generation metadata")
        require(all(g["entry"] == "exports" for g in report["generated"].values()), "missing entry metadata")
        for case in report["cases"]:
            require("error" not in case and len(case["samples"]) == 1, "failed structural sample")
            require(case["summary"]["peak_kib"] > 0, "missing peak memory")
        fanout = subprocess.run(command + ["--dependent-entry", "fanout"], env=env,
                                capture_output=True, timeout=120)
        require(fanout.returncode == 0, f"fanout benchmark failed: {fanout.stderr!r}")
        fanout_report = json.loads(report_path.read_text())
        require(set(fanout_report["generated"]) == {"dependent-buffer-fanout-1", "dependent-buffer-fanout-4"},
                "fanout keys collide with export scaling")
        require(all(g["entry"] == "fanout" for g in fanout_report["generated"].values()),
                "wrong fanout metadata")
        for size in ("0", "257"):
            invalid = subprocess.run(command + ["--dependent-size", size], env=env, capture_output=True)
            require(invalid.returncode == 2, "CLI accepted invalid size")
        require(benchmark.key({"workload": "dependent-list-exports-4", "mode": "check", "target": "x86_64"})
                != benchmark.key({"workload": "dependent-list-fanout-4", "mode": "check", "target": "x86_64"}),
                "entry modes collide in baseline keys")
    print("dependent benchmark: deterministic generation, size validation, silent checks, O0/O2 execution passed")


if __name__ == "__main__":
    main()
