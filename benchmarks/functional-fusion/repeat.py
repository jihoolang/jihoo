#!/usr/bin/env python3
"""Repeat the original C comparison, then use longer CPU-pinned paired runs.

Run inside nix develop. All measurements are sequential. The control pair
functional/handwritten has identical function bytes in this experiment.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import random
import statistics
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def run(command):
    result = subprocess.run([str(x) for x in command], cwd=ROOT, text=True,
                            capture_output=True)
    if result.returncode:
        raise RuntimeError(f"Command failed: {command}\n{result.stdout}{result.stderr}")
    return result.stdout


def percentile(values, fraction):
    values = sorted(values)
    position = (len(values) - 1) * fraction
    low = math.floor(position)
    high = math.ceil(position)
    return values[low] + (values[high] - values[low]) * (position - low)


def summarize(ratios):
    # Resample whole session summaries, not individual correlated samples.
    rng = random.Random(20261026)
    boot = [statistics.median(rng.choices(ratios, k=len(ratios)))
            for _ in range(25000)]
    return {"sessions": len(ratios), "jihoo_faster_sessions": sum(r < 1 for r in ratios),
            "c_faster_sessions": sum(r > 1 for r in ratios),
            "median_ratio": statistics.median(ratios), "min_ratio": min(ratios),
            "max_ratio": max(ratios),
            "session_bootstrap_95_percent": [percentile(boot, .025), percentile(boot, .975)],
            "session_ratios": ratios}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "out/jihoo")
    parser.add_argument("--output", type=Path, default=ROOT / "out/functional-fusion/repeated")
    parser.add_argument("--sessions", type=int, default=10)
    parser.add_argument("--repeats", type=int, default=7)
    parser.add_argument("--size", type=int, default=1_000_000)
    parser.add_argument("--iterations", type=int, default=128)
    parser.add_argument("--pinned-iterations", type=int, default=512)
    parser.add_argument("--pairs", type=int, default=15)
    parser.add_argument("--cpu", type=int, default=2)
    args = parser.parse_args()
    if min(args.sessions, args.repeats, args.size, args.iterations,
           args.pinned_iterations, args.pairs) < 1:
        parser.error("session, repeat, size, iteration and pair counts must be positive")
    initial_affinity = sorted(os.sched_getaffinity(0))
    if args.cpu not in initial_affinity:
        parser.error(f"CPU {args.cpu} is not in the allowed affinity: {initial_affinity}")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    report = {"commit": run(["git", "rev-parse", "HEAD"]).strip(),
              "compiler_sha256": hashlib.sha256(args.compiler.resolve().read_bytes()).hexdigest(),
              "host": platform.platform(), "initial_affinity": initial_affinity,
              "size": args.size, "sessions": args.sessions,
              "baseline_iterations": args.iterations, "baseline_repeats": args.repeats,
              "pinned_cpu": args.cpu, "pinned_iterations": args.pinned_iterations,
              "pinned_pairs_per_session": args.pairs,
              "baseline": [], "pinned": []}
    for session in range(args.sessions):
        directory = output / f"baseline-{session + 1:02d}"
        log = run([sys.executable, HERE / "run.py", "--compiler", args.compiler.resolve(),
                   "--output", directory, "--size", args.size,
                   "--iterations", args.iterations, "--repeats", args.repeats])
        (directory / "run.log").write_text(log)
        measured = json.loads((directory / "report.json").read_text())
        ratio = measured["results"]["iterator"]["over_c"]
        control = measured["results"]["functional"]["seconds"] / measured["results"]["handwritten"]["seconds"]
        binary = directory / "wrapping-O2"
        report["baseline"].append({"ratio": ratio, "identical_code_control_ratio": control,
                                   "results": {name: measured["results"][name]
                                               for name in ("iterator", "c", "functional", "handwritten")},
                                   "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest()})
        print(f"baseline {session+1:02d}: iterator/C={ratio:.5f} "
              f"identical-code control={control:.5f}", flush=True)
        (output / "progress.json").write_text(json.dumps(report, indent=2) + "\n")
    if not measured["machine_code"]["functional_equals_handwritten"]:
        raise RuntimeError("the control functions do not have identical machine code")
    report["toolchain"] = {k: measured[k] for k in ("compiler", "clang", "opt")}
    report["machine_code"] = measured["machine_code"]
    os.sched_setaffinity(0, {args.cpu})  # Child processes inherit this affinity.
    report["observed_pinned_affinity"] = sorted(os.sched_getaffinity(0))
    for session in range(args.sessions):
        samples = []
        expected = None

        def measure(name):
            nonlocal expected
            value = json.loads(run([binary, name, args.size, args.pinned_iterations]))
            actual = value["sample"], value["checksum"]
            if expected is None:
                expected = actual
            if actual != expected or value["allocations"] != 0:
                raise RuntimeError(f"incorrect benchmark result: {name}: {value}")
            return value["seconds"]

        for name in ("iterator", "c", "functional", "handwritten"):
            measure(name)  # Warm-up is excluded.
        for pair in range(args.pairs):
            # Alternate AB/BA and which pair goes first; flip between sessions.
            target = ["iterator", "c"]
            control = ["functional", "handwritten"]
            if (session + pair) % 2:
                target.reverse()
            if (session + pair // 2) % 2:
                control.reverse()
            order = target + control if (session + pair) % 2 else control + target
            sample = {"order": order, "seconds": {name: measure(name) for name in order}}
            sample["ratio"] = sample["seconds"]["iterator"] / sample["seconds"]["c"]
            sample["control_ratio"] = sample["seconds"]["functional"] / sample["seconds"]["handwritten"]
            samples.append(sample)
        median = {name: statistics.median(s["seconds"][name] for s in samples)
                  for name in ("iterator", "c", "functional", "handwritten")}
        result = {"median_seconds": median, "ratio": median["iterator"] / median["c"],
                  "identical_code_control_ratio": median["functional"] / median["handwritten"],
                  "jihoo_faster_pairs": sum(s["ratio"] < 1 for s in samples), "samples": samples}
        report["pinned"].append(result)
        print(f"pinned   {session+1:02d}: iterator/C={result['ratio']:.5f} "
              f"jihoo-faster pairs={result['jihoo_faster_pairs']}/{args.pairs} "
              f"identical-code control={result['identical_code_control_ratio']:.5f}", flush=True)
        (output / "progress.json").write_text(json.dumps(report, indent=2) + "\n")
    report["summary"] = {}
    for phase in ("baseline", "pinned"):
        report["summary"][phase] = summarize([s["ratio"] for s in report[phase]])
        report["summary"][phase]["identical_code_control"] = summarize(
            [s["identical_code_control_ratio"] for s in report[phase]])
        control = report["summary"][phase]["identical_code_control"]
        control["functional_faster_sessions"] = control.pop("jihoo_faster_sessions")
        control["handwritten_faster_sessions"] = control.pop("c_faster_sessions")
    report["summary"]["pinned"]["jihoo_faster_pairs"] = sum(
        s["jihoo_faster_pairs"] for s in report["pinned"])
    report["summary"]["pinned"]["total_pairs"] = args.sessions * args.pairs
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report["summary"], indent=2), flush=True)
    print(f"Artifacts: {output}")


if __name__ == "__main__":
    main()
