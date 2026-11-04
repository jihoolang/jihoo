#!/usr/bin/env bash
# The scalar helper execution bridge, checked against current emit-horn
# output. Also reject incorrect operations and a missing overflow result.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
horn=${HORN:-$root/../horn}
jihoo=${JIHOO:-jihoo}
agda=${AGDA:-agda}
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
mkdir -p "$out/horn" "$out/good"
cp "$horn/agda/Schematic.agda" "$out/horn/"
"$jihoo" emit-horn --lib "$root/compiler/linear.jh" --fn check > "$out/check.horn"

prepare() {
  local dir=$1 rules=$2
  cp "$root/agda/Adequacy.agda" "$root/agda/Integers.agda" "$root/agda/ListExecution.agda" \
    "$root/agda/ScalarExecution.agda" "$root/agda/ScalarExecutionExamples.agda" "$dir/"
  "$jihoo" run "$root/agda/theory.jh" -- "$rules" > "$dir/Theory.agda"
}

prepare "$out/good" "$out/check.horn"
"$agda" --safe --no-libraries -i "$out/horn" -i "$out/good" "$out/good/ScalarExecutionExamples.agda"
for bad in add mul overflow; do
  mkdir "$out/$bad"
  case $bad in
    add)
      sed '/^(rule [^ ]* () (fn\.add /s/(add /(mul /' "$out/check.horn" > "$out/$bad.horn" ;;
    mul)
      sed '/^(rule [^ ]* () (fn\.mul /s/(mul /(add /' "$out/check.horn" > "$out/$bad.horn" ;;
    overflow)
      sed '/^(rule [^ ]* () (fn\.add .* Option<i128>\.None))$/d' "$out/check.horn" > "$out/$bad.horn" ;;
  esac
  if cmp -s "$out/check.horn" "$out/$bad.horn"; then
    echo "scalar-rule mutation did not change the generated rules: $bad" >&2
    exit 1
  fi
  prepare "$out/$bad" "$out/$bad.horn"
  if "$agda" --safe --no-libraries -i "$out/horn" -i "$out/$bad" \
      "$out/$bad/ScalarExecution.agda" > "$out/$bad.log" 2>&1; then
    echo "accepted incorrect scalar rules: $bad" >&2
    exit 1
  fi
  # The schema's witness must fail. Missing imports, parse errors and
  # tool failures do not count as proof rejection.
  if ! grep -Fq 'when checking that the expression tt has type' "$out/$bad.log" ||
      ! grep -Fq 'T?' "$out/$bad.log"; then
    cat "$out/$bad.log" >&2
    exit 1
  fi
  echo "rejected incorrect scalar rules: $bad"
done
cd "$root"
python3 -I tests/horn/scalars.py "$jihoo"
echo "bounded scalar helper executions imply the generated Horn relations"
