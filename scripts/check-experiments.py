#!/usr/bin/env python3
"""Run deterministic experiment regressions, without sibling repositories by default."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
HORN_REVISION = "18caf6d39088e1569beff678bc4461a28b8d2827"


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "out/jihoo")
    parser.add_argument("--horn", type=Path, help="also compare against this pinned Horn checkout (requires Rust)")
    parser.add_argument("--horn-revision", default=HORN_REVISION)
    args = parser.parse_args()
    compiler = args.compiler.resolve(strict=True)
    out = ROOT / "out/experiments"
    out.mkdir(parents=True, exist_ok=True)
    report = {"status": "running", "host": platform.platform(),
              "compiler": str(compiler),
              "compiler_sha256": hashlib.sha256(compiler.read_bytes()).hexdigest(),
              "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
              "source_tree_dirty": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT)),
              "mode": "differential" if args.horn else "local", "suites": {}}

    def save():
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(*command, env=None):
        subprocess.run(list(map(str, command)), cwd=ROOT, env=env, check=True)

    save()
    try:
        reference = (["--horn", args.horn.resolve(), "--horn-revision", args.horn_revision]
                     if args.horn else ["--local"])
        suites = [
            ("kernel", "experimental/kernel/check.py", reference, ROOT / "out/kernel/report.json"),
            ("proofs", "experimental/proofs/check.py", reference, ROOT / "out/proofs/report.json"),
            ("codec", "experimental/verified-codec/check.py", [], ROOT / "out/verified-codec/report.json"),
            ("fusion", "experiments/functional-fusion/run.py", ["--check-only"], ROOT / "out/functional-fusion/results/report.json"),
        ]
        for name, script, options, result in suites:
            print(f"Checking {name}", flush=True)
            run(sys.executable, ROOT / script, "--compiler", compiler, *options)
            report["suites"][name] = json.loads(result.read_text())
            save()

        print("Checking iterator semantics and compile-time closure captures", flush=True)
        runner = out / "test-runner"
        run(compiler, "build", "tests/runner.jh", "-o", runner)
        for name in ("functional", "comptime_closure"):
            run(runner, "run", env={**os.environ, "JIHOO_COMPILER": str(compiler), "JIHOO_TEST": name})
        report["iterator_and_closure_regressions"] = "passed"
        report["status"] = "passed"
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report["status"] = "failed"
        report["error"] = str(error)
        raise
    finally:
        save()
    print(f"Experiment regressions passed; report: {out / 'report.json'}", flush=True)


if __name__ == "__main__":
    main()
