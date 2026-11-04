#!/usr/bin/env bash
# Checks the soundness of the linear checker in Agda, from the current
# source: writes the theory in which lib/proof/refine.jh proves it sound
# (`emit-horn` of compiler/linear.jh, then agda/theory.jh), the certificate
# refine.jh produces (agda/certificate.jh), exports that certificate for
# Agda with Horn's `schematic-kernel --agda`, and checks agda/Certified.agda,
# where Agda runs Horn's proved checker on it and reads the theorem in the
# integers. CertifiedRemoval.agda then connects it to the semantic guard
# conditions of CheckRemoval.agda. HORN: a checkout of Horn, by default
# ../horn beside this repository, for its agda/; SCHEMATIC_KERNEL: Horn's `schematic-kernel`
# (default: on PATH); JIHOO: the compiler (default `jihoo`), whose standard
# library must have lib/proof (JIHOO_PATH=$PWD/lib in the dev shell).
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
horn=${HORN:-$root/../horn}
jihoo=${JIHOO:-jihoo}
kernel=${SCHEMATIC_KERNEL:-schematic-kernel}
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
"$jihoo" emit-horn --lib "$root/compiler/linear.jh" --fn check > "$out/check.horn"
"$jihoo" run "$root/agda/theory.jh" -- "$out/check.horn" > "$out/Theory.agda"
"$jihoo" run "$root/agda/certificate.jh" -- "$out/check.horn" "$out"
# The export is untrusted: Agda checks the certificate itself.
"$kernel" --agda CheckCertificate "$out/check.theory" "$out/check.goals" "$out/check.proof" \
  "$out/CheckCertificate.agda"
mkdir "$out/horn"
cp "$horn"/agda/*.agda "$out/horn"/
cp "$root"/agda/*.agda "$out"/
# A larger allocation area spares the collector most of the work.
agda --safe --no-libraries -i "$out/horn" -i "$out" "$out/CertifiedRemoval.agda" +RTS -A256m -RTS
echo "linear checker: sound, certificate checked by Agda"
echo "certified linear guards discharge semantic check-removal conditions"
