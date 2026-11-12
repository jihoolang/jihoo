#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
expected=$(sed 's|leanprover/lean4:v||' lean-toolchain)
case "$(lean --version)" in
  "Lean (version $expected,"*) ;;
  *) printf 'Expected Lean %s\n' "$expected" >&2; exit 1 ;;
esac
lake build --wfail Jihoo.CommonDataCoreBackwardChecks
report=$(mktemp)
trap 'rm -f "$report"' EXIT
lake env lean -DwarningAsError=true CheckCommonCoreBackward.lean > "$report"
cat "$report"
python3 - "$report" <<'PY'
import re
import sys
with open(sys.argv[1], encoding="utf-8") as f:
    report = f.read()
entries = re.findall(r"depends on axioms: \[([^\]]*)\]", report)
closed = re.findall(r"does not depend on any axioms", report)
assert len(entries) + len(closed) == 16, report
for entry in entries:
    unexpected = set(filter(None, re.split(r"[,\s]+", entry))) - {"propext", "Quot.sound", "Classical.choice"}
    assert not unexpected, f"Unexpected proof dependencies: {unexpected}"
PY
