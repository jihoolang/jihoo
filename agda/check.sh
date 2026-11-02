#!/usr/bin/env bash
# Checks the adequacy proof: writes the theory in which lib/proof/refine.jh
# proves the linear checker sound (`emit-horn` of compiler/linear.jh, then
# agda/theory.jh), and checks agda/Integers.agda against it with Agda and
# Horn's agda/ (HORN: a checkout of Horn, by default ../horn beside this
# repository). JIHOO is the compiler (default `jihoo`); its standard
# library must have lib/proof (JIHOO_PATH=$PWD/lib in the dev shell).
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
horn=${HORN:-$root/../horn}
jihoo=${JIHOO:-jihoo}
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
"$jihoo" emit-horn --lib "$root/compiler/linear.jh" --fn check > "$out/check.horn"
"$jihoo" run "$root/agda/theory.jh" -- "$out/check.horn" > "$out/Theory.agda"
mkdir "$out/horn"
cp "$horn"/agda/*.agda "$out/horn"/
cp "$root"/agda/*.agda "$out"/
agda --safe --no-libraries -i "$out/horn" -i "$out" "$out/Integers.agda"
echo "adequacy: checked"
