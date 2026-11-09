#!/usr/bin/env python3
"""Structural and executable checks; intentionally no performance thresholds."""
import argparse
import importlib.util
import os
import json
import sys
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
    with tempfile.TemporaryDirectory(prefix="dependent-bench-test-") as directory:
        temp = Path(directory)
        for kind in benchmark.DEPENDENT:
            for n in (1, 4):
                source = benchmark.dependent_source(kind, n)
                require(source == benchmark.dependent_source(kind, n), "nondeterministic source")
                require(source.count("export fn consumer_") == n, "wrong consumer count")
                require("auto(" not in source, "workload depends on proof automation")
                path = temp / f"{kind}-{n}.jh"
                path.write_text(source)
                before = set(temp.iterdir())
                checked = subprocess.run([compiler, "check", str(path)], env=env, capture_output=True, timeout=120)
                require(checked.returncode == 0 and not checked.stdout and not checked.stderr,
                        f"check failed: {checked.stderr!r}")
                require(set(temp.iterdir()) == before, "check wrote output")
                for opt in ("-O0", "-O2"):
                    output = temp / "program"
                    subprocess.run([compiler, "build", opt, str(path), "-o", str(output)], env=env,
                                   check=True, capture_output=True, timeout=120)
                    result = subprocess.run([str(output)], capture_output=True, timeout=30)
                    require(result.returncode == 17 * n, f"wrong runtime result: {result.returncode}")
            for n in (0, -1, 257):
                try:
                    benchmark.dependent_source(kind, n)
                except ValueError:
                    pass
                else:
                    raise AssertionError("invalid size accepted")
        report_path = temp / "report.json"
        command = [sys.executable, str(ROOT / "scripts/benchmark_compile.py"), "--compiler", compiler,
                   "--workload", "dependent-buffer", "--dependent-size", "1", "--dependent-size", "4",
                   "--check-only", "--json", str(report_path)]
        subprocess.run(command, env=env, check=True, capture_output=True, timeout=120)
        report = json.loads(report_path.read_text())
        require(len(report["cases"]) == 4, "missing check/full or scaling case")
        require(len(report["compiler_invocation_sha256"]) == 64, "missing compiler identity")
        require(set(report["generated"]) == {"dependent-buffer-1", "dependent-buffer-4"}, "wrong generation metadata")
        for case in report["cases"]:
            require("error" not in case and len(case["samples"]) == 1, "failed structural sample")
            require(case["summary"]["peak_kib"] > 0, "missing peak memory")
        for size in ("0", "257"):
            invalid = subprocess.run(command + ["--dependent-size", size], env=env, capture_output=True)
            require(invalid.returncode == 2, "CLI accepted invalid size")
        require(benchmark.key({"workload": "dependent-list-4", "mode": "check", "target": "x86_64"})
                != benchmark.key({"workload": "dependent-list-16", "mode": "check", "target": "x86_64"}),
                "sizes collide in baseline keys")
    print("dependent benchmark: deterministic generation, size validation, silent checks, O0/O2 execution passed")


if __name__ == "__main__":
    main()
