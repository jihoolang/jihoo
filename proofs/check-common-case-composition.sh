#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
for check in common-composition-contract common-data-case-relocated-context common-data-branch-finish common-data-restricted-composition common-data-case-register-safety literal-finish; do
  bash "check-${check}.sh"
done
lake build Jihoo --wfail
report=$(mktemp)
trap 'rm -f "$report"' EXIT
lake env lean -DwarningAsError=true AuditCommonCaseComposition.lean > "$report"
cat "$report"
python3 - "$report" <<'PYTHON'
import re, sys
text = open(sys.argv[1]).read()
entries = re.findall(r'depends on axioms: \[([^\]]*)\]', text)
closed = re.findall(r'does not depend on any axioms', text)
assert len(entries) + len(closed) == 60, text
for entry in entries:
    assert set(filter(None, re.split(r'[,\s]+', entry))) <= {'propext', 'Quot.sound', 'Classical.choice'}, entry
PYTHON
