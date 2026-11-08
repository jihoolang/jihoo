#!/usr/bin/env bash
# Releases a new version of jihoo, then makes it the seed.
#
#   scripts/bump-version.sh release 0.1.2   # on main: bump, commit, tag, push, wait for binaries
#   scripts/bump-version.sh seed 0.1.2      # vendor and pin the released seed archives
#
# `release` sets `version` in flake.nix and the download link in the getting
# started page, commits "Release <version>", tags v<version>, pushes both and
# waits for .github/workflows/release.yml to attach the x86_64 and aarch64
# archives. `seed` verifies both released archives against their published
# checksums, replaces bootstrap/'s copies, and updates flake.nix's seed version
# and hashes. It commits on the current branch (not pushed); check it
# with `nix build` before opening a pull request. See
# docs/internals/self-hosting.md.
set -euo pipefail

repo=jihoolang/jihoo
root=$(git rev-parse --show-toplevel)
cd "$root"

usage() {
  echo "usage: $0 release|seed <version>" >&2
  exit 2
}

[ $# -eq 2 ] || usage
cmd=$1
version=${2#v}
tag=v$version
[[ $version =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]] || { echo "bad version: $version" >&2; exit 2; }

clean() {
  git diff --quiet && git diff --cached --quiet ||
    { echo "the working tree has changes" >&2; exit 1; }
}

release() {
  clean
  [ "$(git branch --show-current)" = main ] || { echo "release from main" >&2; exit 1; }
  git fetch -q origin main --tags
  [ "$(git rev-parse HEAD)" = "$(git rev-parse origin/main)" ] ||
    { echo "main is not origin/main" >&2; exit 1; }
  if git rev-parse -q --verify "refs/tags/$tag" >/dev/null; then
    echo "$tag already exists; a released archive is never replaced" >&2
    exit 1
  fi

  old=$(sed -n 's/^      version = "\(.*\)";$/\1/p' flake.nix)
  [ -n "$old" ] || { echo "no version in flake.nix" >&2; exit 1; }
  sed -i "s/^      version = \"$old\";$/      version = \"$version\";/" flake.nix
  sed -i "s|releases/download/v[0-9.]*/jihoo-v[0-9.]*-|releases/download/$tag/jihoo-$tag-|g; \
          s|jihoo-v[0-9.]*-x86_64-linux/bin|jihoo-$tag-x86_64-linux/bin|g" \
    site/src/content/docs/start/getting-started.md
  git add flake.nix site/src/content/docs/start/getting-started.md
  git commit -q -m "Release $version" -m "Version $old becomes $version in flake.nix, and the getting started page downloads $tag."
  git tag -a "$tag" -m "jihoo $tag"
  git push origin main "$tag"

  echo "waiting for the release workflow of $tag"
  sleep 10
  run=$(gh run list -R "$repo" --workflow release.yml --branch "$tag" --limit 1 --json databaseId -q '.[0].databaseId')
  gh run watch -R "$repo" "$run" --exit-status
  gh release view -R "$repo" "$tag" --json assets -q '.assets[].name'
}

seed() {
  clean
  gh release view -R "$repo" "$tag" >/dev/null
  seed_tmp=$(mktemp -d)
  trap 'rm -rf -- "$seed_tmp"' EXIT
  declare -A hashes
  # Finish both downloads and checksum checks before changing the checkout.
  for arch in x86_64 aarch64; do
    archive=jihoo-$tag-$arch-linux.tar.gz
    gh release download -R "$repo" "$tag" --dir "$seed_tmp" \
      --pattern "$archive" --pattern "$archive.sha256"
    mapfile -t checksum_lines < "$seed_tmp/$archive.sha256"
    [ "${#checksum_lines[@]}" -eq 1 ] || { echo "invalid checksum file: $archive" >&2; exit 1; }
    read -r digest filename extra <<< "${checksum_lines[0]}"
    [[ $digest =~ ^[0-9a-fA-F]{64}$ && $filename == "$archive" && -z $extra ]] || \
      { echo "invalid checksum record: $archive" >&2; exit 1; }
    (cd "$seed_tmp" && printf '%s  %s\n' "$digest" "$archive" | sha256sum --check --strict)
    hashes[$arch]=$(nix hash file --type sha256 --sri "$seed_tmp/$archive")
    [[ ${hashes[$arch]} == sha256-* ]] || { echo "no hash for $archive" >&2; exit 1; }
  done
  for arch in x86_64 aarch64; do
    install -m644 "$seed_tmp/jihoo-$tag-$arch-linux.tar.gz" "bootstrap/jihoo-$arch-linux.tar.gz"
    sed -i "s|^\(          $arch-linux = \"\).*\(\";\)$|\1${hashes[$arch]}\2|" flake.nix
  done
  # The seed's version is the one followed by its hashes.
  sed -i "/^      seed = {$/,/^      };$/s/^        version = \".*\";$/        version = \"$version\";/" flake.nix
  git diff --stat
  python3 tests/bootstrap_seed.py
  git add flake.nix bootstrap/jihoo-*-linux.tar.gz
  git commit -q -m "Bootstrap from $version" -m "Vendor the exact released $tag archives and pin their hashes, so compiler/ and the lib/ it imports may use what that compiler knows."
  echo "committed; check it with: nix build"
}

case $cmd in
  release) release ;;
  seed) seed ;;
  *) usage ;;
esac
