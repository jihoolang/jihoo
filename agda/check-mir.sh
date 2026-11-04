#!/usr/bin/env bash
# Regenerate MIR and Horn data from the current compiler sources, prove
# their correspondence for scalar helpers, direct callers and a loop,
# and reject bad graphs/rules and unsupported MIR operations.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
horn=${HORN:-$root/../horn}
jihoo=${JIHOO:-jihoo}
agda=${AGDA:-agda}
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
cd "$root"
mkdir "$out/horn"
cp "$horn/agda/Schematic.agda" "$out/horn/"
cat compiler/linear.jh agda/mir-callers.jh > "$out/program.jh"
"$jihoo" build -O1 -I compiler agda/export-mir.jh -o "$out/export-mir"

base() {
  mkdir -p "$1"
  cp agda/Adequacy.agda agda/Integers.agda agda/ListExecution.agda \
    agda/ScalarExecution.agda agda/MirExecution.agda "$1/"
}

proof() {
  mkdir -p "$1"
  cp agda/MirCorrespondence.agda agda/MirExecutionExamples.agda \
    agda/MirLoopCorrespondence.agda agda/MirLoopExamples.agda "$1/"
}

for target in x86_64 aarch64; do
  base "$out/$target/base"
  proof "$out/$target/good"
  "$out/export-mir" "$out/program.jh" "$target" > "$out/$target/good/GeneratedMir.agda"
  "$jihoo" emit-horn -I compiler --target "$target" --lib "$out/program.jh" \
    --fn check --fn mir_add --fn mir_mul --fn mir_loop > "$out/$target/program.horn"
  "$jihoo" run agda/theory.jh -- "$out/$target/program.horn" > "$out/$target/base/Theory.agda"
  "$agda" --safe --no-libraries -i "$out/$target/good" -i "$out/$target/base" -i "$out/horn" \
    "$out/$target/good/MirLoopExamples.agda"
  echo "checked scalar MIR execution, direct calls and an inductive loop: $target"
  if [[ -n ${MIR_PROOF_OUT:-} ]]; then
    mkdir -p "$MIR_PROOF_OUT/$target"
    cp "$out/$target/good/GeneratedMir.agda" "$out/$target/base/Theory.agda" \
      "$out/$target/program.horn" "$MIR_PROOF_OUT/$target/"
  fi
done

# Keep the correct Horn theory fixed when changing MIR. This exercises
# execution correspondence rather than only the scalar schema lookup.
python3 - "$out" <<'PY'
import sys
from pathlib import Path

root = Path(sys.argv[1])
source = (root / "program.jh").read_text()
mutations = {
    "operation": ("let (s, over) = overflowing_add(a, b)", "let (s, over) = overflowing_mul(a, b)", 1),
    "return": ("if over { return None }", "if over { return Some(a) }", 2),
    "callee": ("{ add(a, b) }", "{ mul(a, b) }", 1),
    "unsupported": ("{ add(a, b) }", "{ Some(a +% b) }", 1),
    "loop-operation": ("let (next, over) = overflowing_add(value, b)", "let (next, over) = overflowing_mul(value, b)", 1),
    "loop-return": ("if over { return Some(value) }", "if over { return Some(next) }", 1),
    "loop-update": ("value = next", "value = a", 1),
}
for name, (old, new, count) in mutations.items():
    assert source.count(old) == count, f"source mutation no longer applies: {name}"
    (root / (name + ".jh")).write_text(source.replace(old, new, 1))

generated = (root / "x86_64/good/GeneratedMir.agda").read_text()
old = "(live 4) ∷ (assign 4 (use (local 3 (0 ∷ []))))"
assert generated.count(old) == 2, "lifetime mutation no longer applies"
(root / "lifetime.agda").write_text(generated.replace(old, "(dead 3) ∷ " + old, 1))
old = "(switch (local 6 ([])) 7 6)"
assert generated.count(old) == 1, "loop-branch mutation no longer applies"
(root / "loop-branch.agda").write_text(generated.replace(old, "(switch (local 6 ([])) 6 7)", 1))

rules = (root / "x86_64/program.horn").read_text().splitlines()
changed = 0
for i, line in enumerate(rules):
    if line.startswith("(rule ") and "(fn.mir_add " in line and "(fn.add " in line:
        rules[i] = line.replace("(fn.add ", "(fn.mul ", 1)
        changed += 1
assert changed == 1, "caller-rule mutation no longer applies"
(root / "caller-rule.horn").write_text("\n".join(rules) + "\n")

original_rules = (root / "x86_64/program.horn").read_text().splitlines()
for name in ("loop-step", "loop-exit"):
    rules = []
    changed = 0
    for line in original_rules:
        if line.startswith("(rule ") and "(fn.mir_loop@1 " in line:
            if name == "loop-step" and "(add " in line:
                line = line.replace("(add ", "(mul ", 1)
                changed += 1
            elif name == "loop-exit" and " () " in line:
                changed += 1
                continue
        rules.append(line)
    assert changed == 1, f"loop-rule mutation no longer applies: {name}"
    (root / (name + ".horn")).write_text("\n".join(rules) + "\n")
PY

for bad in operation return callee lifetime caller-rule \
    loop-operation loop-return loop-update loop-branch loop-step loop-exit; do
  proof "$out/$bad"
  shared="$out/x86_64/base"
  module=MirCorrespondence
  case $bad in loop-*) module=MirLoopCorrespondence ;; esac
  case $bad in
    lifetime|loop-branch) cp "$out/$bad.agda" "$out/$bad/GeneratedMir.agda" ;;
    caller-rule|loop-step|loop-exit)
      cp "$out/x86_64/good/GeneratedMir.agda" "$out/$bad/GeneratedMir.agda"
      shared="$out/$bad-base"
      base "$shared"
      "$jihoo" run agda/theory.jh -- "$out/$bad.horn" > "$shared/Theory.agda" ;;
    *) "$out/export-mir" "$out/$bad.jh" x86_64 > "$out/$bad/GeneratedMir.agda" ;;
  esac
  if "$agda" --safe --no-libraries -i "$out/$bad" -i "$shared" -i "$out/horn" \
      "$out/$bad/$module.agda" > "$out/$bad.log" 2>&1; then
    echo "accepted incorrect MIR correspondence: $bad" >&2
    exit 1
  fi
  # Require an actual proof/type mismatch in the correspondence module.
  # Syntax errors, unresolved names and tool failures are not rejections.
  if ! grep -Fq "$module.agda:" "$out/$bad.log" ||
      ! grep -Fq 'error: [UnequalTerms]' "$out/$bad.log"; then
    cat "$out/$bad.log" >&2
    exit 1
  fi
  echo "rejected incorrect MIR correspondence: $bad"
done

if "$out/export-mir" "$out/unsupported.jh" x86_64 > "$out/unsupported.agda" 2> "$out/unsupported.log"; then
  echo "exported an unsupported MIR operation" >&2
  exit 1
fi
if ! grep -Fq 'MIR export: unsupported rvalue' "$out/unsupported.log"; then
  cat "$out/unsupported.log" >&2
  exit 1
fi
echo "rejected unsupported wrapping arithmetic in the MIR export"
echo "exported scalar MIR executions and loop returns imply their generated Horn relations"
