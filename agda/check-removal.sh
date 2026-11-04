#!/usr/bin/env bash
# The semantic VC/check-removal theorem and its positive and negative
# instantiations. No compiler, LLVM or certificate generation is needed.
# Copy inputs so Agda can write interfaces even from a read-only checkout.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
horn=${HORN:-$root/../horn}
agda=${AGDA:-agda}
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
mkdir -p "$out/horn" "$out/reject"
cp "$horn/agda/Schematic.agda" "$out/horn/"
cp "$root/agda/CheckRemoval.agda" "$root/agda/CheckRemovalExamples.agda" "$out/"
cp "$root/agda/reject/"*.agda "$out/reject/"
"$agda" --safe --no-libraries -i "$out/horn" -i "$out" "$out/CheckRemovalExamples.agda"
for bad in RemovedFalseGuard OpaqueWrite MissingBranch WrongPostcondition; do
  if "$agda" --safe --no-libraries -i "$out/horn" -i "$out" -i "$out/reject" \
      "$out/reject/$bad.agda" > "$out/$bad.log" 2>&1; then
    echo "accepted invalid verification conditions: $bad" >&2
    exit 1
  fi
  # A missing import, syntax error or tool failure must not pass as a
  # successful rejection. Each example must fail to prove an equality.
  if ! grep -Fq 'error: [UnequalTerms]' "$out/$bad.log"; then
    cat "$out/$bad.log" >&2
    exit 1
  fi
  echo "rejected invalid verification conditions: $bad"
done
echo "semantic VC generation and local check removal: sound"
