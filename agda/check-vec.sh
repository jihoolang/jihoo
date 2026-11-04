#!/usr/bin/env bash
# Compose typed Vec backing-store operations with both targets' generated
# Horn list rules. Wrong reads, writes and relocation must break the proof.
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

base() {
  mkdir -p "$1"
  cp agda/Adequacy.agda agda/Integers.agda agda/ListExecution.agda "$1/"
}

proof() {
  mkdir -p "$1"
  cp agda/VecMemory.agda agda/VecMemoryExamples.agda \
    agda/VecHornExecution.agda agda/VecHornExamples.agda "$1/"
}

for target in x86_64 aarch64; do
  base "$out/$target/base"
  proof "$out/$target/good"
  "$jihoo" emit-horn --target "$target" --lib compiler/linear.jh --fn check > "$out/$target/check.horn"
  "$jihoo" run agda/theory.jh -- "$out/$target/check.horn" > "$out/$target/base/Theory.agda"
  "$agda" --safe --no-libraries -i "$out/$target/good" -i "$out/horn" \
    "$out/$target/good/VecMemoryExamples.agda"
  "$agda" --safe --no-libraries -i "$out/$target/good" -i "$out/$target/base" -i "$out/horn" \
    "$out/$target/good/VecHornExamples.agda"
  echo "checked Vec backing-store/Horn correspondence: $target"
done

python3 - "$out" <<'PY'
import sys
from pathlib import Path

root = Path(sys.argv[1])
source = (root / "x86_64/good/VecMemory.agda").read_text()
mutations = {
    "read-length": (
        "index v i = bounded-read (length v) (cells v) i",
        "index v i = bounded-read (suc (length v)) (cells v) i",
    ),
    "write-position": (
        "push-in-place v x = write-next (length v) (capacity v) (cells v) x",
        "push-in-place v x = write-next zero (capacity v) (cells v) x",
    ),
    "write-capacity": (
        "push-in-place v x = write-next (length v) (capacity v) (cells v) x",
        "push-in-place v x = write-next (length v) (suc (capacity v)) (cells v) x",
    ),
    "write-length": (
        "just (vector ds (suc (length v)) (capacity v))",
        "just (vector ds (length v) (capacity v))",
    ),
    "copy-prefix": (
        "resize (suc cap) (suc n) (c ∷ cs) = resize cap n cs >>= λ ds → just (c ∷ ds)",
        "resize (suc cap) (suc n) (c ∷ cs) = resize cap n cs >>= λ ds → just (nothing ∷ ds)",
    ),
    "copy-capacity": (
        "reserve-to v cap = resize cap (length v) (cells v) >>= λ ds → just (vector ds (length v) cap)",
        "reserve-to v cap = resize cap (length v) (cells v) >>= λ ds → just (vector ds (length v) (suc cap))",
    ),
}
for name, (old, new) in mutations.items():
    assert source.count(old) == 1, f"memory mutation no longer applies: {name}"
    destination = root / name
    destination.mkdir()
    (destination / "VecMemory.agda").write_text(source.replace(old, new))
PY

for bad in read-length write-position write-capacity write-length copy-prefix copy-capacity; do
  if "$agda" --safe --no-libraries -i "$out/$bad" -i "$out/horn" \
      "$out/$bad/VecMemory.agda" > "$out/$bad.log" 2>&1; then
    echo "accepted incorrect Vec memory operation: $bad" >&2
    exit 1
  fi
  # Missing imports, syntax errors and tool failures are not rejections.
  if ! grep -Fq 'VecMemory.agda:' "$out/$bad.log" ||
      ! grep -Fq 'error: [UnequalTerms]' "$out/$bad.log"; then
    cat "$out/$bad.log" >&2
    exit 1
  fi
  echo "rejected incorrect Vec memory operation: $bad"
done
echo "Vec backing-store operations imply the generated Horn list relations"
