#!/usr/bin/env python3
"""Measure frontend checking and full compilation, and compare with a baseline.

Each workload is compiled with `jihoo check` (loading, types, compile-time
evaluation, moves, drops and borrows) and with full compilation (`build` for
the host target, `emit-obj` for another one). Every sample is a fresh compiler
process; its elapsed time, user+system CPU time and peak resident memory
(GNU `time`) are recorded with the compiler revision, target, options and host.
Samples of all cases are interleaved, so drift affects them alike.

--baseline compares medians with a recorded report and fails when time or
memory grows beyond the thresholds. Compare only reports from the same
controlled host. --check-only runs every case once, checks that it succeeds
and that `check` is silent and writes nothing, and applies no thresholds: CI
runs it, timing comparisons do not belong there.

--time-passes also records the compiler's own phase timings (`jihoo
--time-passes`) in every sample and their medians per case, and prints them;
against a baseline that has them, each phase's ratio is printed, without
thresholds.
"""
import argparse
import datetime
import json
import os
import re
import platform
from pathlib import Path
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
HOST = {"x86_64": "x86_64", "aarch64": "aarch64", "arm64": "aarch64"}.get(platform.machine())
VERSION = 1

# name -> (directory, entry relative to it, other flags). A `--lib` workload
# has no entry point, so its full compilation is `emit-obj`.
WORKLOADS = {
    "compiler": (ROOT, "compiler/main.jh", []),
    "comptime": (ROOT, "benchmarks/compile/comptime.jh", []),
    "fusion": (ROOT, "benchmarks/functional-fusion/kernels.jh", ["--lib"]),
}


def git_revision(directory, paths=()):
    """The commit of `directory`, with `-dirty` if tracked files (in paths) changed."""
    def git(*args):
        p = subprocess.run(["git", "-C", str(directory), *args], capture_output=True, text=True)
        return p.stdout.strip() if p.returncode == 0 else None
    revision = git("rev-parse", "HEAD")
    if revision and git("status", "--porcelain", "--untracked-files=no", "--", *paths):
        revision += "-dirty"
    return revision


def gnu_time():
    """GNU time, which reports the peak memory of the compiler alone.

    A process's peak includes the memory it had before `exec`, so a child
    forked from Python would start at Python's size; GNU time forks from a
    small process instead.
    """
    path = shutil.which("time")
    if path:
        p = subprocess.run([path, "--version"], capture_output=True, text=True)
        if "GNU" in p.stdout + p.stderr:
            return path
    return None


def measure(time_cmd, argv, cwd, env):
    """Run argv once: (status, stdout, stderr, elapsed, cpu seconds, peak KiB)."""
    with tempfile.TemporaryDirectory(prefix="jihoo-sample-") as temp:
        stats = Path(temp) / "stats"
        start = time.perf_counter()
        p = subprocess.run([time_cmd, "-f", "%M %U %S", "-o", str(stats), *argv],
                           cwd=cwd, env=env, stdin=subprocess.DEVNULL, capture_output=True)
        elapsed = time.perf_counter() - start
        # GNU time writes "Command exited with non-zero status N" first then.
        peak, user, system = stats.read_text().split("\n")[-2].split()
        return p.returncode, p.stdout, p.stderr, elapsed, float(user) + float(system), int(peak)


def parse_external(text):
    """NAME=ENTRY[:INCLUDE...], paths relative to the current directory."""
    name, sep, rest = text.partition("=")
    if not sep or not name or not rest:
        raise argparse.ArgumentTypeError("expected NAME=ENTRY[:INCLUDE...]")
    entry, *includes = rest.split(":")
    entry = Path(entry).resolve()
    if not entry.is_file():
        raise argparse.ArgumentTypeError(f"{entry} is not a file")
    return name, (entry.parent, entry.name, [x for i in includes for x in ("-I", str(Path(i).resolve()))])


PHASE_ROW = re.compile(r"^(\S+(?: \S+)?) +(\d+\.\d+)s +(\d+\.\d+)s +(\d+\.\d+) MiB$")


def parse_phases(stderr):
    """The table `--time-passes` writes: ({phase: {elapsed, cpu, peak_kib}}, rest of stderr)."""
    lines = stderr.decode(errors="replace").split("\n")
    if lines[0].split() != ["phase", "elapsed", "cpu", "peak"]:
        return None, stderr
    phases = {}
    for i, line in enumerate(lines[1:], 1):
        m = PHASE_ROW.match(line)
        if not m:
            return None, stderr
        phases[m[1]] = {"elapsed": float(m[2]), "cpu": float(m[3]), "peak_kib": round(float(m[4]) * 1024)}
        if m[1] == "total":
            return phases, "\n".join(lines[i + 1:]).encode()
    return None, stderr


def key(case):
    return f"{case['workload']}/{case['mode']}/{case['target']}"


def summarize(samples):
    summary = {
        "elapsed_seconds": statistics.median(s["elapsed"] for s in samples),
        "cpu_seconds": statistics.median(s["cpu"] for s in samples),
        "peak_kib": statistics.median(s["peak_kib"] for s in samples),
        "min_elapsed_seconds": min(s["elapsed"] for s in samples),
        "max_peak_kib": max(s["peak_kib"] for s in samples),
    }
    if all("phases" in s for s in samples):
        summary["phases"] = {
            name: {field: statistics.median(s["phases"][name][field] for s in samples)
                   for field in ["elapsed", "cpu", "peak_kib"]}
            for name in samples[0]["phases"]
        }
    return summary


def print_phases(phases, before=None):
    """One line per phase, with its elapsed ratio to `before` where that has it."""
    for name, p in phases.items():
        ratio = ""
        if before and name in before and before[name]["elapsed"] > 0:
            ratio = f" x{p['elapsed'] / before[name]['elapsed']:.3f}"
        print(f"    {name:16} {p['elapsed']:8.3f}s elapsed {p['cpu']:8.3f}s cpu"
              f" {p['peak_kib'] / 1024:8.1f} MiB peak{ratio}")


def compare(report, baseline, max_time, max_memory, min_time):
    """Print each case's ratio to the baseline; return whether any regressed."""
    for field in ["host", "compiler_version", "options"]:
        if report[field] != baseline.get(field):
            print(f"note: {field} differs from the baseline: {baseline.get(field)!r} -> {report[field]!r}")
    old = {key(c): c for c in baseline["cases"]}
    regressed = False
    for case in report["cases"]:
        before = old.get(key(case))
        if before is None:
            print(f"{key(case):40} not in the baseline")
            continue
        now, then = case["summary"]["elapsed_seconds"], before["summary"]["elapsed_seconds"]
        time_ratio = now / then
        memory_ratio = case["summary"]["peak_kib"] / before["summary"]["peak_kib"]
        bad = []
        if time_ratio > 1 + max_time and now - then > min_time:
            bad.append("time")
        if memory_ratio > 1 + max_memory:
            bad.append("memory")
        regressed |= bool(bad)
        print(f"{key(case):40} elapsed x{time_ratio:.3f} peak x{memory_ratio:.3f}"
              + (" REGRESSED: " + ", ".join(bad) if bad else ""))
        if "phases" in case["summary"] and "phases" in before["summary"]:
            print_phases(case["summary"]["phases"], before["summary"]["phases"])
    missing = set(old) - {key(c) for c in report["cases"]}
    for k in sorted(missing):
        print(f"{k:40} only in the baseline")
    return regressed


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--compiler", default="out/jihoo")
    parser.add_argument("--repeats", type=int, default=5)
    parser.add_argument("--target", action="append", choices=["x86_64", "aarch64"],
                        help="target to compile for (repeatable; default the host)")
    parser.add_argument("--opt", default="-O2", choices=["-O0", "-O1", "-O2", "-O3"],
                        help="optimization for full compilation")
    parser.add_argument("--workload", action="append", choices=sorted(WORKLOADS),
                        help="built-in workload (repeatable; default all)")
    parser.add_argument("--external", action="append", type=parse_external, default=[],
                        metavar="NAME=ENTRY[:INCLUDE...]",
                        help="also measure a program outside the checkout, e.g. a Banana entry point")
    parser.add_argument("--proofs", type=Path, metavar="DIR",
                        help="also measure the compile-time generation examples of a jihoo-proofs checkout")
    parser.add_argument("--baseline", type=Path, help="report to compare with")
    parser.add_argument("--max-time-regression", type=float, default=0.10)
    parser.add_argument("--max-memory-regression", type=float, default=0.10)
    parser.add_argument("--min-time-difference", type=float, default=0.02,
                        help="seconds a median must grow by before it counts as a regression")
    parser.add_argument("--check-only", action="store_true",
                        help="one sample per case, structural checks only, no thresholds")
    parser.add_argument("--json", type=Path, help="write the report here")
    parser.add_argument("--time-passes", action="store_true",
                        help="also record the compiler's phase timings (jihoo --time-passes)")
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    if args.check_only:
        args.repeats = 1

    compiler = shutil.which(args.compiler) if os.sep not in args.compiler else str(Path(args.compiler).resolve())
    if not compiler or not Path(compiler).is_file():
        parser.error(f"no compiler at {args.compiler}")
    time_cmd = gnu_time()
    if not time_cmd:
        parser.error("GNU time is needed to measure peak memory (it is in the dev shell)")
    env = {**os.environ, "JIHOO_PATH": str(ROOT / "lib")}
    targets = args.target or [HOST]
    workloads = {name: WORKLOADS[name] for name in (args.workload or WORKLOADS)}
    sources = {}
    if args.proofs:
        proofs = args.proofs.resolve()
        workloads["proofs"] = (proofs, "proofs/example.jh", ["-I", "kernel"])
        workloads["verified-codec"] = (proofs, "verified-codec/example.jh", ["-I", "proofs", "-I", "kernel"])
        sources["jihoo-proofs"] = {"path": str(proofs), "revision": git_revision(proofs)}
    for name, workload in args.external:
        if name in workloads:
            parser.error(f"workload {name} is defined twice")
        workloads[name] = workload
        sources[name] = {"path": str(workload[0] / workload[1]), "revision": git_revision(workload[0])}

    version = subprocess.run([compiler, "--version"], capture_output=True, text=True).stdout.strip()
    report = {
        "version": VERSION,
        "date": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
        "compiler": compiler,
        "compiler_version": version,
        "revision": git_revision(ROOT, ["compiler", "lib", "benchmarks"]),
        "external": sources,
        "host": {"platform": platform.platform(), "machine": platform.machine(),
                 "cpus": os.cpu_count(), "python": platform.python_version()},
        "options": {"opt": args.opt},
        "time_passes": args.time_passes,
        "repeats": args.repeats,
        "cases": [],
    }

    failed = False
    with tempfile.TemporaryDirectory(prefix="jihoo-compile-") as temp:
        temp = Path(temp)
        cases = []
        for name, (directory, entry, flags) in workloads.items():
            for target in targets:
                full = "build" if target == HOST and "--lib" not in flags else "emit-obj"
                output = temp / f"{name}-{target}{'' if full == 'build' else '.o'}"
                timing = ["--time-passes"] if args.time_passes else []
                for mode, argv in [
                    ("check", ["check", entry, "--target", target, *flags, *timing]),
                    ("full", [full, entry, "--target", target, args.opt, *flags, "-o", str(output), *timing]),
                ]:
                    cases.append({"workload": name, "mode": mode, "target": target,
                                  "command": ["jihoo", *argv], "directory": str(directory),
                                  "samples": [], "_argv": [compiler, *argv], "_output": output})
        for i in range(args.repeats):
            for case in (cases if i % 2 == 0 else reversed(cases)):
                if case.get("error"):
                    continue
                case["_output"].unlink(missing_ok=True)
                before = set(Path(case["directory"]).iterdir())
                status, out, err, elapsed, cpu, peak = measure(time_cmd, case["_argv"], case["directory"], env)
                phases = None
                if args.time_passes:
                    phases, err = parse_phases(err)
                problem = None
                if args.time_passes and phases is None and status == 0:
                    problem = "no phase timings on standard error:\n" + err.decode(errors="replace")
                elif status != 0:
                    problem = f"exit status {status}:\n{err.decode(errors='replace')}"
                elif case["mode"] == "check" and (out or err):
                    problem = "check was not silent:\n" + (out + err).decode(errors="replace")
                elif case["mode"] == "check" and set(Path(case["directory"]).iterdir()) != before:
                    problem = "check created files"
                elif case["mode"] == "full" and not case["_output"].is_file():
                    problem = "full compilation wrote no output"
                if problem:
                    case["error"] = problem
                    failed = True
                    print(f"{key(case)}: {problem}", file=sys.stderr, flush=True)
                    continue
                sample = {"elapsed": elapsed, "cpu": cpu, "peak_kib": peak}
                if phases is not None:
                    sample["phases"] = phases
                case["samples"].append(sample)
        for case in cases:
            del case["_argv"], case["_output"]
            if case["samples"]:
                case["summary"] = summarize(case["samples"])
                s = case["summary"]
                print(f"{key(case):40} {s['elapsed_seconds']:8.3f}s elapsed {s['cpu_seconds']:8.3f}s cpu"
                      f" {s['peak_kib'] / 1024:8.1f} MiB peak", flush=True)
                if "phases" in s and not args.baseline:
                    print_phases(s["phases"])
            report["cases"].append(case)

    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(report, indent=2) + "\n")
    if args.baseline and not args.check_only:
        measured = dict(report, cases=[c for c in report["cases"] if "summary" in c])
        failed |= compare(measured, json.loads(args.baseline.read_text()),
                          args.max_time_regression, args.max_memory_regression, args.min_time_difference)
    raise SystemExit(1 if failed else 0)


if __name__ == "__main__":
    main()
