#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
expected=$(sed 's|leanprover/lean4:v||' lean-toolchain)
case "$(lean --version)" in
  "Lean (version $expected,"*) ;;
  *) echo "Expected Lean $expected" >&2; exit 1 ;;
esac
lake build Jihoo.TreeDropCallChecks --wfail
report=$(mktemp)
trap 'rm -f "$report"' EXIT
lake env lean -DwarningAsError=true AuditTreeDropCall.lean > "$report"
cat "$report"
python3 - "$report" <<'PY'
import re, sys
text = open(sys.argv[1], encoding='utf-8').read()
entries = re.findall(r'depends on axioms: \[([^\]]*)\]', text)
closed = re.findall(r'does not depend on any axioms', text)
assert len(entries) + len(closed) == 32, 'Expected 32 audits'
for entry in entries:
    assert set(filter(None, re.split(r'[,\s]+', entry))) <= {'propext', 'Quot.sound', 'Classical.choice'}, entry
PY
