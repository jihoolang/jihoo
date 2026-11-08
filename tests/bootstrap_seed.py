#!/usr/bin/env python3
"""Check both vendored release archives without Nix, network access or execution."""
from pathlib import Path
import base64
import hashlib
import re
import tarfile

ROOT = Path(__file__).resolve().parents[1]


def check(root=ROOT):
    flake = (root / 'flake.nix').read_text()
    seed = re.search(r'^      seed = \{\n(.*?)^      \};', flake, re.M | re.S)
    if seed is None:
        raise ValueError('missing seed declaration in flake.nix')
    version = re.search(r'version = "([0-9]+\.[0-9]+\.[0-9]+)";', seed[1])
    if version is None:
        raise ValueError('missing seed version')
    for system, machine in [('x86_64-linux', 62), ('aarch64-linux', 183)]:
        pin = re.search(rf'^          {system} = "(sha256-[^"]+)";', seed[1], re.M)
        if pin is None:
            raise ValueError(f'missing seed hash for {system}')
        archive = root / 'bootstrap' / f'jihoo-{system}.tar.gz'
        contents = archive.read_bytes()
        digest = 'sha256-' + base64.b64encode(hashlib.sha256(contents).digest()).decode()
        if digest != pin[1]:
            raise ValueError(f'{archive.name}: SHA-256 differs from flake.nix')
        prefix = f'jihoo-v{version[1]}-{system}'
        with tarfile.open(archive, 'r:gz') as tar:
            for member in tar.getmembers():
                parts = Path(member.name).parts
                if not parts or parts[0] != prefix or '..' in parts or not (member.isfile() or member.isdir()):
                    raise ValueError(f'{archive.name}: unexpected member {member.name!r}')
            for name in ['LICENSE', 'share/jihoo/lib/std/prelude.jh', 'bin/jihoo']:
                if not tar.getmember(f'{prefix}/{name}').isfile():
                    raise ValueError(f'{archive.name}: missing regular file {name}')
            compiler = tar.extractfile(f'{prefix}/bin/jihoo')
            if compiler is None:
                raise ValueError(f'{archive.name}: missing compiler')
            header = compiler.read(20)
            if (header[:6] != b'\x7fELF\x02\x01' or len(header) != 20 or
                    int.from_bytes(header[18:20], 'little') != machine):
                raise ValueError(f'{archive.name}: compiler architecture differs from {system}')
        print(f'{archive.name}: {len(contents):,} bytes, release v{version[1]}, SHA-256 and ELF architecture verified')


if __name__ == '__main__':
    check()
