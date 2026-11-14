#!/usr/bin/env bash
set -euo pipefail
# Local checks share the capped process group used by all proof agents. Nix/CI
# sandboxes without a user systemd manager still get Lean's per-process cap.
resource_guard="$(dirname "$0")/../scripts/proof-limits.sh"
if [[ -x "$resource_guard" && -r /proc/self/cgroup ]] &&
    [[ $(< /proc/self/cgroup) != *'/jihoo-proof-jobs.slice/'* ]] &&
    command -v systemctl >/dev/null && systemctl --user show-environment >/dev/null 2>&1; then
  exec "$resource_guard" bash "$0" "$@"
fi
cd "$(dirname "$0")"
expected=$(sed 's|leanprover/lean4:v||' lean-toolchain)
actual=$(lean --version)
case "$actual" in
  "Lean (version $expected,"*) ;;
  *) printf 'Expected Lean %s; got %s\n' "$expected" "$actual" >&2; exit 1 ;;
esac
# Warnings (including admitted proofs) are errors, also on cached builds.
lake build --wfail
report=$(mktemp)
generated=$(mktemp)
trap 'rm -f "$report" "$generated"' EXIT
lake env lean -M 4096 -j 1 -DwarningAsError=true Audit.lean > "$report"
cat "$report"
# Audit actual elaborated dependencies, not merely source text. Only Lean's
# standard logical axioms may occur; in particular sorryAx is never accepted.
python3 - "$report" <<'PY'
import re
import sys
with open(sys.argv[1], encoding="utf-8") as audit:
    report = audit.read()
allowed = {"propext", "Quot.sound", "Classical.choice"}
entries = re.findall(r"depends on axioms: \[([^\]]*)\]", report)
closed = re.findall(r"does not depend on any axioms", report)
assert len(entries) + len(closed) == 4646, report
for entry in entries:
    unexpected = set(filter(None, re.split(r"[,\s]+", entry))) - allowed
    assert not unexpected, f"Unexpected proof dependencies: {unexpected}"
PY
# The exact Lean-generated program is a normal core preservation fixture.
# Its acceptance by the executable checker is separately tested by core.py.
lake env lean -M 4096 -j 1 -DwarningAsError=true --run EmitCore.lean > "$generated"
diff -u ../tests/core_preserves/lean-core-translation.jhc "$generated"
lake env lean -M 4096 -j 1 -DwarningAsError=true --run EmitPrimitiveSafety.lean > "$generated"
diff -u ../tests/core_preserves/lean-primitive-safety.jhc "$generated"
lake env lean -M 4096 -j 1 -DwarningAsError=true --run EmitBinderClassification.lean > "$generated"
diff -u ../tests/core_binder_modes.txt "$generated"
lake env lean -M 4096 -j 1 -DwarningAsError=true --run EmitMixedTelescope.lean > "$generated"
diff -u ../tests/core_preserves/lean-mixed-telescope.jhc "$generated"
lake env lean -M 4096 -j 1 -DwarningAsError=true --run EmitMixedInference.lean > "$generated"
diff -u ../tests/core_mixed_inference.tsv "$generated"
lake env lean -M 4096 -j 1 -DwarningAsError=true --run EmitMixedProofTranslation.lean > "$generated"
diff -u ../tests/core_preserves/lean-mixed-proof-translation.jhc "$generated"
# Every local, operand, statement and CFG edge matches the native-export fixture.
lake env lean -M 4096 -j 1 -DwarningAsError=true --run EmitMirFixture.lean > "$generated"
diff -u ../tests/core_mir_single.json "$generated"
# Full original-Core constructor view of the closed composed-program proof.
lake env lean -M 4096 -j 1 -DwarningAsError=true --run EmitComposedGraph.lean > "$generated"
diff -u ../tests/core_composed_graph.json "$generated"
# Full source graph of runtime-dependent Buffer length/index interpretation.
lake env lean -M 4096 -j 1 -DwarningAsError=true --run EmitDependentBufferGraph.lean > "$generated"
diff -u ../tests/core_dependent_index.json "$generated"
# Complete original graph for framed sized calls and owned-result Lend.
lake env lean -M 4096 -j 1 -DwarningAsError=true --run EmitSizedCompositionGraph.lean > "$generated"
diff -u ../tests/core_sized_composition.json "$generated"
# The single runtime-parameterized MIR fixture includes explicit argument slots.
lake env lean -M 4096 -j 1 -DwarningAsError=true --run EmitDynamicMir.lean > "$generated"
diff -u ../tests/core_dynamic_mir.json "$generated"

# Full native four-argument composition fixture, separate from generated MIR.
lake env lean -M 4096 -j 1 -DwarningAsError=true --run EmitNativeCompositionMir.lean > "$generated"
diff -u ../tests/core_native_composition_mir.json "$generated"
