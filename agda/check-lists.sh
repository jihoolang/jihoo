#!/usr/bin/env bash
# Prove the executable list primitives imply the generated Horn relations,
# then require rejection of off-by-one lengths/indices and a lost push.
# JIHOO: current compiler; HORN: pinned Horn checkout for Schematic.agda.
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
  cp "$root/agda/Adequacy.agda" "$root/agda/Integers.agda" \
    "$root/agda/ListExecution.agda" "$root/agda/ListExecutionExamples.agda" "$dir/"
  "$jihoo" run "$root/agda/theory.jh" -- "$rules" > "$dir/Theory.agda"
}

prepare "$out/good" "$out/check.horn"
"$agda" --safe --no-libraries -i "$out/horn" -i "$out/good" "$out/good/ListExecutionExamples.agda"
for bad in length index push; do
  mkdir "$out/$bad"
  case $bad in
    length)
      sed '/^(rule Vec<<i64,i128>>\.len\.cons /s/(add ?n z1)/(add ?n z0)/' \
        "$out/check.horn" > "$out/$bad.horn" ;;
    index)
      sed '/^(rule Vec<Lin>\.nth\.zero /s/(eq ?i z0)/(eq ?i z1)/' \
        "$out/check.horn" > "$out/$bad.horn" ;;
    push)
      sed '/^(rule Vec<i128>\.snoc\.nil /s/(Vec<i128>\.cons ?e Vec<i128>\.nil)/Vec<i128>.nil/' \
        "$out/check.horn" > "$out/$bad.horn" ;;
  esac
  if cmp -s "$out/check.horn" "$out/$bad.horn"; then
    echo "list-rule mutation did not change the generated rules: $bad" >&2
    exit 1
  fi
  prepare "$out/$bad" "$out/$bad.horn"
  # Every mutant has a fresh module directory and no inherited interfaces.
  # A parser error or missing symbol does not count as proof rejection.
  if "$agda" --safe --no-libraries -i "$out/horn" -i "$out/$bad" \
      "$out/$bad/ListExecution.agda" > "$out/$bad.log" 2>&1; then
    echo "accepted incorrect list rules: $bad" >&2
    exit 1
  fi
  if ! grep -Fq 'error: [UnequalTerms]' "$out/$bad.log"; then
    cat "$out/$bad.log" >&2
    exit 1
  fi
  echo "rejected incorrect list rules: $bad"
done
echo "list execution implies the generated Horn relations"
