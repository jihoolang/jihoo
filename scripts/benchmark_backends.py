#!/usr/bin/env python3
"""Compare the same compiler's LLVM C API and clang backends, interleaved.

Uses medians, checks every output, and fails if runtime regresses beyond
--max-regression (default 10%). Run on an otherwise idle machine. Results
describe these workloads on this host, not a universal performance guarantee.
"""
import argparse
import json
import os
import platform
from pathlib import Path
import statistics
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
CASES = [("fib", "34", "12"), ("sieve", "4000000", "16"),
         ("matrix", "240", "48"), ("float", "160000", "2")]


def run(args, env):
    start = time.perf_counter()
    p = subprocess.run(args, cwd=ROOT, env=env, capture_output=True, check=True)
    return time.perf_counter() - start, p.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", default="out/jihoo")
    parser.add_argument("--repeats", type=int, default=7)
    parser.add_argument("--compile-repeats", type=int, default=3)
    parser.add_argument("--max-regression", type=float, default=0.10)
    parser.add_argument("--selfhost", action="store_true", help="also build and time the compiler itself")
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()
    if min(args.repeats, args.compile_repeats) < 1:
        parser.error("repeat counts must be positive")
    compiler = str(Path(args.compiler).resolve())
    env = {**os.environ, "JIHOO_PATH": str(ROOT / "lib")}
    env.setdefault("JIHOO_CC", "clang")  # use the same linker for both paths
    envs = {b: {**env, "JIHOO_BACKEND": b} for b in ("clang", "llvm")}
    report = {"compiler": compiler, "host": platform.platform(), "llvm_major": 21,
              "cc": run([env["JIHOO_CC"], "--version"], env)[1].decode().splitlines()[0],
              "repeats": args.repeats, "results": {}}
    failed = False
    with tempfile.TemporaryDirectory(prefix="jihoo-backends-") as temp:
        exes = {b: str(Path(temp) / b) for b in envs}
        timings = {b: [] for b in envs}
        for i in range(args.compile_repeats):
            for b in (list(envs) if i % 2 == 0 else list(reversed(envs))):
                t, _ = run([compiler, "build", "-O2", "--release", "benchmarks/backends.jh", "-o", exes[b]], envs[b])
                timings[b].append(t)
        report["compile_seconds"] = {b: statistics.median(t) for b, t in timings.items()}
        print("compile seconds:", report["compile_seconds"], flush=True)
        for case in CASES:
            samples = {b: [] for b in envs}
            outputs = [run([exes[b], *case], env)[1] for b in envs]  # warm up
            assert outputs[0] == outputs[1], (case, outputs)
            for i in range(args.repeats):
                for b in (list(envs) if i % 2 == 0 else list(reversed(envs))):
                    t, output = run([exes[b], *case], env)
                    assert output == outputs[0], (case, b, output)
                    samples[b].append(t)
            medians = {b: statistics.median(ts) for b, ts in samples.items()}
            ratio = medians["llvm"] / medians["clang"]
            report["results"][case[0]] = {"seconds": medians, "llvm_over_clang": ratio, "samples": samples}
            failed |= ratio > 1 + args.max_regression
            print(f"{case[0]:8} clang={medians['clang']:.4f}s llvm={medians['llvm']:.4f}s ratio={ratio:.3f}", flush=True)
        if args.selfhost:
            samples = {b: [] for b in envs}
            build_times = {}
            compilers = {b: str(Path(temp) / (b + "-compiler")) for b in envs}
            for b in envs:
                t, _ = run([compiler, "build", "-O2", "compiler/main.jh", "-o", compilers[b]], envs[b])
                build_times[b] = t
            expected = None
            for i in range(args.repeats):
                for b in (list(envs) if i % 2 == 0 else list(reversed(envs))):
                    t, output = run([compilers[b], "emit-llvm", "compiler/main.jh"], env)
                    if expected is None:
                        expected = output
                    assert output == expected, "self-hosted compilers emit different IR"
                    samples[b].append(t)
            medians = {b: statistics.median(ts) for b, ts in samples.items()}
            ratio = medians["llvm"] / medians["clang"]
            report["selfhost"] = {"build_seconds": build_times, "emit_seconds": medians, "llvm_over_clang": ratio}
            failed |= ratio > 1 + args.max_regression
            print("selfhost:", report["selfhost"], flush=True)
    if args.json:
        args.json.write_text(json.dumps(report, indent=2) + "\n")
    raise SystemExit(1 if failed else 0)


if __name__ == "__main__":
    main()
