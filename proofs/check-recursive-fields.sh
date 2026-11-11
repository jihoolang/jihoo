#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
expected=$(sed 's|leanprover/lean4:v||' lean-toolchain)
actual=$(lean --version)
case "$actual" in
  "Lean (version $expected,"*) ;;
  *) printf 'Expected Lean %s; got %s\n' "$expected" "$actual" >&2; exit 1 ;;
esac
lake build Jihoo.RecursiveCaseBodyExamples --wfail
report=$(mktemp)
trap 'rm -f "$report"' EXIT
lake env lean -DwarningAsError=true CheckRecursiveFieldOwnership.lean > "$report"
cat "$report"
python3 - "$report" <<'PY'
import re
import sys
with open(sys.argv[1], encoding="utf-8") as audit:
    report = audit.read()
entries = re.findall(r"depends on axioms: \[([^\]]*)\]", report)
closed = re.findall(r"does not depend on any axioms", report)
if len(entries) + len(closed) != 101:
    raise SystemExit("Expected 101 elaborated theorem audits")
for entry in entries:
    unexpected = set(filter(None, re.split(r"[,\s]+", entry))) - {
        "propext", "Quot.sound", "Classical.choice"
    }
    if unexpected:
        raise SystemExit(f"Unexpected proof dependencies: {unexpected}")
PY
