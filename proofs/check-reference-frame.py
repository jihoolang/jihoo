#!/usr/bin/env python3
"""Standalone frame proof check; does not modify shared imports or audit."""
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
os.chdir(ROOT)
env = dict(os.environ, LEAN_NUM_THREADS="2")
modules = ("ReferenceHeapFrame", "ReferenceHeapFrameChecks")
expected = set()
for module in modules:
    source = (ROOT / "Jihoo" / f"{module}.lean").read_text()
    namespace = "Jihoo.ReferenceHeap.Frame" + (".Checks" if module.endswith("Checks") else "")
    expected.update(namespace + "." + name for name in re.findall(r"^theorem (\w+)", source, re.M))
expected.update("Jihoo.ReferenceHeap." + name for name in (
    "scalar_load_compatible", "scalar_write_compatible", "allocate_compatible", "release_compatible"))
audit = ROOT / "AuditReferenceHeapFrame.lean"
registered = re.findall(r"^#print axioms (\S+)$", audit.read_text(), re.M)
if set(registered) != expected or len(registered) != len(expected):
    raise SystemExit(f"Audit coverage mismatch: missing={expected - set(registered)}, extra={set(registered) - expected}")
subprocess.run(["lake", "build", "Jihoo.ReferenceHeapFrameChecks"], env=env, check=True)
for module in modules:
    subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", f"Jihoo/{module}.lean"], env=env, check=True)
result = subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", audit.name],
                        env=env, check=True, text=True, stdout=subprocess.PIPE)
allowed = {"propext", "Classical.choice", "Quot.sound"}
seen = set()
used = set()
for line in result.stdout.splitlines():
    match = re.fullmatch(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", line)
    if not match:
        raise SystemExit(f"Unexpected audit output: {line}")
    seen.add(match[1])
    axioms = set(match[2].split(", ")) if match[2] else set()
    if axioms - allowed:
        raise SystemExit(f"Forbidden axioms for {match[1]}: {axioms - allowed}")
    used.update(axioms)
if seen != expected:
    raise SystemExit(f"Incomplete audit output: {expected - seen}")
print(result.stdout, end="")
print(f"PASS: {len(expected)} declarations; axiom union: {', '.join(sorted(used))}")
