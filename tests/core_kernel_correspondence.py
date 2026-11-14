#!/usr/bin/env python3
"""Native/raw-checker regression correspondence, not a translation theorem.

Builds the existing snapshot exporter against this checkout's compiler/core.jh.
Every accepted case feeds its exact retained native snapshot to the Lean raw
checker. No derivation certificate or Python inference implementation is used.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shlex
import shutil
import tempfile

from core_certificate_process import ROOT, command, success
from core_typing_producer import Snapshot, encode_numbers, graph_tokens, require

# Expected outcomes differ deliberately at the documented subset boundary.
CASES = {
    'literal': ('(def value U64 7)', True, True),
    'unsigned-max': ('(def value U64 18446744073709551615)', True, True),
    'signed-min': ('(def value I64 (int -9223372036854775808))', True, True),
    'erased-index-gap': ('(def value (pi0 n U64 (Eq n n)) (lam0 n U64 (refl n)))', True, False),
    'signed': ('(def value I64 (int -7))', True, True),
    'dependent': ('(def value (Eq 7 7) (app (lam n U64 (refl n)) 7))', True, True),
    'nested-capture': (
        '(def value (pi x U64 (pi y U64 (Eq x x))) '
        '(lam x U64 (app (lam n U64 (lam y U64 (refl n))) x)))', True, True),
    'addition': ('(def value U64 (uadd 1 2))', True, True),
    'wrong-argument': ('(def value U64 (app (lam x U64 x) (int -7)))', False, False),
    'false-evidence': ('(def value (Eq 0 1) (refl 0))', False, False),
    'conversion-gap': ('(def value (Eq (uadd 0 1) 1) (refl 1))', True, False),
    'unsupported-array': ('(def value (Array 1) (array (int -7)))', True, False),
}


def run(compiler, checker, output):
    output.mkdir(parents=True, exist_ok=True)
    exporter = output / 'core-typing-snapshots'
    success(command([*compiler, 'build', '-O2', '-I', 'compiler',
                     'tests/core_typing_snapshots.jh', '-o', exporter]))
    observations = []
    retained = {}
    for name, (source, native_ok, raw_ok) in CASES.items():
        (output / f'{name}.core').write_text(source + '\n')
        result = command([exporter, 'require'], source.encode())
        require((result.returncode == 0) == native_ok, f'{name}: native outcome changed: {result.stderr!r}')
        require(result.returncode in (0, 1), f'{name}: native process crashed')
        if not native_ok:
            require(b'type mismatch' in result.stderr, f'{name}: unexpected rejection: {result.stderr!r}')
            observations.append({'case': name, 'native': 'reject', 'raw': 'not run'})
            continue
        payload = result.stdout
        retained[name] = payload
        Snapshot.read(payload)  # Existing canonical bounded decoder, no typing search.
        (output / f'{name}.snapshot').write_bytes(payload)
        checked = command([*checker, '64'], payload, cwd=ROOT / 'proofs')
        require(checked.returncode == (0 if raw_ok else 1),
                f'{name}: raw outcome changed: {checked.stderr!r}')
        if not raw_ok:
            require(b'raw inference differs or rejects' in checked.stderr,
                    f'{name}: rejection did not reach raw checker: {checked.stderr!r}')
        observations.append({'case': name, 'native': 'accept',
                             'raw': 'accept' if raw_ok else 'reject',
                             'snapshot_sha256': hashlib.sha256(payload).hexdigest()})

    # Test raw inference against the actual inferred result, not only the declared
    # type accepted by native conversion. Each call retains its own complete arena.
    for name in ('dependent', 'nested-capture'):
        source = CASES[name][0]
        payload = success(command([exporter, 'infer'], source.encode()))
        (output / f'{name}.inferred.snapshot').write_bytes(payload)
        success(command([*checker, '64'], payload, cwd=ROOT / 'proofs'))

    for fuel in ('0', '1'):
        result = command([*checker, fuel], retained['dependent'], cwd=ROOT / 'proofs')
        require(result.returncode == 1 and b'raw inference differs or rejects' in result.stderr,
                f'fuel {fuel}: expected bounded inference rejection')
    # Corrupt the selected type while preserving canonical bytes and valid graph.
    original = Snapshot.read(retained['dependent'])
    wrong_type = next(i for i, n in enumerate(original.graph) if n == (3,))
    mutation = encode_numbers([3, original.term, wrong_type, *graph_tokens(original.graph)])
    result = command([*checker, '64'], mutation, cwd=ROOT / 'proofs')
    require(result.returncode == 1 and b'raw inference differs or rejects' in result.stderr,
            'wrong selected type root was not rejected by inference')
    for payload in (retained['literal'] + b'\n', b''):
        result = command([*checker, '64'], payload, cwd=ROOT / 'proofs')
        require(result.returncode == 1, 'malformed snapshot accepted')
    # Nix source-only builds have neither .git metadata nor necessarily git.
    revision = None
    if (ROOT / ".git").exists() and shutil.which("git") is not None:
        result = command(["git", "rev-parse", "HEAD"], cwd=ROOT)
        if result.returncode == 0:
            revision = result.stdout.decode().strip()
    manifest = {
        'claim': 'regression evidence only; native parser/exporter/build/IO remain trusted',
        'core_sha256': hashlib.sha256((ROOT / 'compiler/core.jh').read_bytes()).hexdigest(),
        'exporter_sha256': hashlib.sha256((ROOT / 'compiler/core_snapshot.jh').read_bytes()).hexdigest(),
        'commit': revision,
        'cases': observations,
        'additional_checks': ['2 inferred-root snapshots', 'fuel 0 and 1',
                              'wrong type root', 'trailing newline', 'empty snapshot'],
    }
    (output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(f'kernel correspondence: {len(CASES)} native fixtures and 7 additional checks passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean -DwarningAsError=true --run CheckKernelInference.lean')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        run(shlex.split(args.compiler), shlex.split(args.checker), args.output.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='kernel-correspondence-') as output:
            run(shlex.split(args.compiler), shlex.split(args.checker), Path(output))


if __name__ == '__main__':
    main()
