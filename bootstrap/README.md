# Bootstrap seed

These files are byte-for-byte copies of the selected jihoo release archives.
Their version and SHA-256 hashes are pinned in `flake.nix`; their fixed local
names keep only the current pair in the checkout. Nix verifies the raw archive
hash and patches the released compiler for its environment as before.

For the initial v0.5.0 seed:

| Local file | Original release asset | Bytes | SHA-256 |
| --- | --- | ---: | --- |
| `jihoo-x86_64-linux.tar.gz` | [x86_64 archive](https://github.com/jihoolang/jihoo/releases/download/v0.5.0/jihoo-v0.5.0-x86_64-linux.tar.gz) | 1,200,682 | `a9fedcae6cdc51142f1d26fc694baa48c68636fa9b39eab777b45dd3134ecadc` |
| `jihoo-aarch64-linux.tar.gz` | [aarch64 archive](https://github.com/jihoolang/jihoo/releases/download/v0.5.0/jihoo-v0.5.0-aarch64-linux.tar.gz) | 1,132,711 | `3bb15b1e8e1f6ae88d54c6e36fb2cce9e1b5acb3f0b371a2d2bf1a856d33a211` |

Each archive contains the compiler, its standard library and Apache-2.0 license.
No binaries were rebuilt or recompressed for vendoring. The hashes above are
the release asset digests and the existing pre-vendoring `flake.nix` pins.
The x86_64 copy was recovered from the existing Nix fixed-output cache; the
aarch64 copy was downloaded from GitHub's release asset API. Both match those
independently recorded pins.

Run `python3 tests/bootstrap_seed.py` to check the current pair. To select a
new release, use `scripts/bump-version.sh seed X.Y.Z`, then review and test its
commit before pushing. The table above records initial provenance, not the
current version after a later update; `flake.nix` is authoritative.

See [self-hosting](../docs/internals/self-hosting.md) for the release process,
offline limits and bootstrap trust assumptions. Do not use Git LFS here or
replace an archive with an unverified rebuild.
