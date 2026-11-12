#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
expected=$(sed 's|leanprover/lean4:v||' lean-toolchain)
actual=$(lean --version)
case "$actual" in
  "Lean (version $expected,"*) ;;
  *) printf 'Expected Lean %s; got %s\n' "$expected" "$actual" >&2; exit 1 ;;
esac
lake build Jihoo.TreeCreateChecks Jihoo.TreeCreateRelocationChecks --wfail
report=$(mktemp)
trap 'rm -f "$report"' EXIT
lake env lean -DwarningAsError=true AuditTreeCreate.lean > "$report"
lake env lean -DwarningAsError=true AuditTreeCreateRelocation.lean >> "$report"
cat "$report"
python3 - "$report" <<'PY'
import re
import sys
with open(sys.argv[1], encoding="utf-8") as audit:
    report = audit.read()
allowed = {"propext", "Quot.sound", "Classical.choice"}
entries = re.findall(r"depends on axioms: \[([^\]]*)\]", report)
closed = re.findall(r"does not depend on any axioms", report)
assert len(entries) + len(closed) == 51, report
for entry in entries:
    unexpected = set(filter(None, re.split(r"[,\s]+", entry))) - allowed
    assert not unexpected, f"Unexpected proof dependencies: {unexpected}"
PY
