#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
expected=$(sed 's|leanprover/lean4:v||' lean-toolchain)
actual=$(lean --version)
case "$actual" in
  "Lean (version $expected,"*) ;;
  *) printf 'Expected Lean %s; got %s\n' "$expected" "$actual" >&2; exit 1 ;;
esac
# Warnings (including admitted proofs) are errors, also on cached builds.
lake build --wfail
report=$(lake env lean -DwarningAsError=true Audit.lean)
printf '%s\n' "$report"
# Audit actual elaborated dependencies, not merely source text. Only Lean's
# standard logical axioms may occur; in particular sorryAx is never accepted.
python3 - "$report" <<'PY'
import re
import sys
report = sys.argv[1]
allowed = {"propext", "Quot.sound", "Classical.choice"}
entries = re.findall(r"depends on axioms: \[([^\]]*)\]", report)
closed = re.findall(r"does not depend on any axioms", report)
assert len(entries) + len(closed) == 1388, report
for entry in entries:
    unexpected = set(filter(None, re.split(r"[,\s]+", entry))) - allowed
    assert not unexpected, f"Unexpected proof dependencies: {unexpected}"
PY
# The exact Lean-generated program is a normal core preservation fixture.
# Its acceptance by the executable checker is separately tested by core.py.
generated=$(mktemp)
trap 'rm -f "$generated"' EXIT
lake env lean -DwarningAsError=true --run EmitCore.lean > "$generated"
diff -u ../tests/core_preserves/lean-core-translation.jhc "$generated"
lake env lean -DwarningAsError=true --run EmitPrimitiveSafety.lean > "$generated"
diff -u ../tests/core_preserves/lean-primitive-safety.jhc "$generated"
lake env lean -DwarningAsError=true --run EmitBinderClassification.lean > "$generated"
diff -u ../tests/core_binder_modes.txt "$generated"
lake env lean -DwarningAsError=true --run EmitMixedTelescope.lean > "$generated"
diff -u ../tests/core_preserves/lean-mixed-telescope.jhc "$generated"
lake env lean -DwarningAsError=true --run EmitMixedInference.lean > "$generated"
diff -u ../tests/core_mixed_inference.tsv "$generated"
lake env lean -DwarningAsError=true --run EmitMixedProofTranslation.lean > "$generated"
diff -u ../tests/core_preserves/lean-mixed-proof-translation.jhc "$generated"
# Every local, operand, statement and CFG edge matches the native-export fixture.
lake env lean -DwarningAsError=true --run EmitMirFixture.lean > "$generated"
diff -u ../tests/core_mir_single.json "$generated"
