#!/usr/bin/env python3
"""Check and measure function composition with the existing jihoo compiler.

Run inside nix develop. LLVM tools must use the same major version as jihoo.
Artifacts include raw/optimized IR, assembly, correctness output, and JSON.
"""
import argparse
import json
import platform
from pathlib import Path
import re
import statistics
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
NAMES = ["functional", "staged", "iterator", "eager", "handwritten", "c"]
EXTRA = ("iterator_take", "iterator_zip", "iterator_returned")
COMPOSED = ("functional", "staged", "iterator", *EXTRA)


def run(command):
    result = subprocess.run([str(x) for x in command], cwd=ROOT,
                            capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(f"Command failed: {command}\n{result.stdout}{result.stderr}")
    return result.stdout


def inspect_ir(path):
    source = path.read_text()
    definitions = dict(re.findall(
        r"^define [^\n]*@([\w.$]+)\([^\n]*\)[^\n]*\{\n(.*?)^\}",
        source, re.M | re.S))
    results = {}
    for entry in [*NAMES[:-1], *EXTRA]:
        visited, pending, external, indirect = set(), [entry], set(), []
        while pending:
            name = pending.pop()
            if name in visited:
                continue
            if name not in definitions:
                raise RuntimeError(f"missing IR definition: {name}")
            visited.add(name)
            for line in definitions[name].splitlines():
                if not re.search(r"\b(?:call|invoke)\b", line):
                    continue
                target = re.search(r"@([\w.$]+)\(", line)
                if not target:
                    indirect.append(line.strip())
                elif target[1] in definitions:
                    pending.append(target[1])
                elif not target[1].startswith("llvm."):
                    external.add(target[1])
        results[entry] = {"reachable_functions": sorted(visited),
                          "external_calls": sorted(external),
                          "indirect_calls": indirect}
    # The experiment succeeds structurally only if the compositions have
    # no runtime callback calls and no external calls (including allocation).
    for name in COMPOSED:
        if results[name]["external_calls"] or results[name]["indirect_calls"]:
            raise RuntimeError(f"composition did not fuse completely: {results[name]}")
    return results


def inspect_machine_code(obj, output):
    section = output / "text.bin"
    run(["llvm-objcopy", "--dump-section", f".text={section}", obj])
    text = section.read_bytes()
    bodies = {}
    for line in run(["llvm-nm", "--print-size", "--format=posix", obj]).splitlines():
        name, kind, address, size = line.split()
        if name in ("functional", "staged", "iterator", "handwritten") and kind == "T":
            start, length = int(address, 16), int(size, 16)
            bodies[name] = text[start:start + length]
    return {"bytes": {name: len(body) for name, body in bodies.items()},
            "functional_equals_staged": bodies["functional"] == bodies["staged"],
            "iterator_equals_handwritten": bodies["iterator"] == bodies["handwritten"],
            "functional_equals_handwritten": bodies["functional"] == bodies["handwritten"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "out/jihoo")
    parser.add_argument("--output", type=Path, default=ROOT / "out/functional-fusion/results")
    parser.add_argument("--size", type=int, default=1_000_000)
    parser.add_argument("--iterations", type=int, default=64)
    parser.add_argument("--repeats", type=int, default=7)
    parser.add_argument("--check-only", action="store_true",
                        help="check correctness, allocations and IR without timing samples")
    parser.add_argument("--max-iterator-over-c", type=float,
                        help="optionally fail when the iterator/C median ratio exceeds this value")
    args = parser.parse_args()
    if min(args.size, args.iterations, args.repeats) < 1:
        parser.error("size, iterations and repeats must be positive")
    if args.max_iterator_over_c is not None and args.max_iterator_over_c <= 0:
        parser.error("max-iterator-over-c must be positive")
    if args.check_only and args.max_iterator_over_c is not None:
        parser.error("--max-iterator-over-c requires timing; omit --check-only")
    compiler, output = args.compiler.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    report = {"host": platform.platform(), "compiler": str(compiler),
              "clang": run(["clang", "--version"]).splitlines()[0],
              "opt": run(["opt", "--version"]).strip(),
              "size": args.size, "iterations": args.iterations,
              "repeats": args.repeats, "timing_measured": not args.check_only,
              "validation": {}, "allocations": {}}
    reference = output / "reference.o"
    run(["clang", "-O2", "-fwrapv", "-S", "-emit-llvm", HERE / "reference.c",
         "-o", output / "reference.raw.ll"])
    run(["opt", "-passes=default<O2>", "-S", output / "reference.raw.ll",
         "-o", output / "reference.ll"])
    run(["clang", "-O2", "-c", output / "reference.ll", "-o", reference])
    for wrapping in (False, True):
        for level in (0, 2):
            label = f"{'wrapping' if wrapping else 'checked'}-O{level}"
            raw, optimized = output / f"{label}.raw.ll", output / f"{label}.ll"
            obj, exe = output / f"{label}.o", output / label
            start = time.perf_counter()
            run([compiler, "emit-llvm", "--lib", *(["--release"] if wrapping else []),
                 HERE / "kernels.jh", "-o", raw])
            run(["opt", f"-passes=default<O{level}>", "-S", raw, "-o", optimized])
            run(["clang", f"-O{level}", "-c", optimized, "-o", obj])
            # fwrapv matches jihoo release arithmetic; checked validation uses
            # bounded values. No LTO: the harness cannot hoist kernel calls.
            run(["clang", "-O2", "-fwrapv", "-Wall", "-Wextra", "-Werror",
                 HERE / "harness.c", reference, obj,
                 "-Wl,--wrap=malloc,--wrap=realloc,--wrap=free", "-o", exe])
            validation = run([exe, "check", int(wrapping)]).strip()
            report["validation"][label] = validation
            report["allocations"][label] = json.loads(run([exe, "check-allocations"]))
            print(f"{label}: {validation}", flush=True)
            if wrapping and level == 2:
                report["build_seconds"] = time.perf_counter() - start
                report["ir"] = inspect_ir(optimized)
                report["machine_code"] = inspect_machine_code(obj, output)
                print(f"Machine code: {report['machine_code']}", flush=True)
                (output / "kernels.asm").write_text(run(["llvm-objdump", "-d", obj]))
                benchmark = exe
    if args.check_only:
        (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(f"Correctness, allocations and IR passed without timing; artifacts: {output}", flush=True)
        return
    samples = {name: [] for name in NAMES}
    metadata = {}
    expected = None
    for repetition in range(args.repeats + 1):
        # Rotate order; the first round warms every implementation.
        order = NAMES[repetition % len(NAMES):] + NAMES[:repetition % len(NAMES)]
        for name in order:
            sample = json.loads(run([benchmark, name, args.size, args.iterations]))
            observed = sample["sample"], sample["checksum"]
            if expected is None:
                expected = observed
            if observed != expected:
                raise RuntimeError(f"benchmark result mismatch: {name}: {observed} != {expected}")
            metadata[name] = {k: v for k, v in sample.items() if k != "seconds"}
            if repetition:
                samples[name].append(sample["seconds"])
    reference = statistics.median(samples["c"])
    report["results"] = {}
    for name in NAMES:
        median = statistics.median(samples[name])
        report["results"][name] = {**metadata[name], "seconds": median,
                                    "over_c": median / reference, "samples": samples[name]}
        print(f"{name:12} {median:.6f}s  C ratio={median/reference:.3f}  "
              f"allocations/call={metadata[name]['allocations']}", flush=True)
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Artifacts: {output}")
    if (args.max_iterator_over_c is not None and
            report["results"]["iterator"]["over_c"] > args.max_iterator_over_c):
        raise SystemExit("iterator runtime exceeded the requested C ratio; see report.json")


if __name__ == "__main__":
    main()
