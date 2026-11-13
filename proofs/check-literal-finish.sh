#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lake build Jihoo.CommonLiteralBodyChecks Jihoo.CommonDataInstalledFinishChecks Jihoo.CommonLiteralFinishChecks --wfail
report=$(mktemp)
trap 'rm -f "$report"' EXIT
lake env lean -DwarningAsError=true AuditLiteralFinish.lean > "$report"
cat "$report"
python3 - "$report" <<'PY'
import re, sys
text = open(sys.argv[1]).read()
entries = re.findall(r'depends on axioms: \[([^\]]*)\]', text)
closed = re.findall(r'does not depend on any axioms', text)
assert len(entries) + len(closed) == 36, text
for entry in entries:
    assert set(filter(None, re.split(r'[,\s]+', entry))) <= {'propext', 'Quot.sound', 'Classical.choice'}, entry
PY
