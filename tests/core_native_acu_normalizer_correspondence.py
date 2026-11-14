#!/usr/bin/env python3
"""Compare the proved bounded full-Term converter with actual Core.normal.

All 204 actual outputs must pass the proved comparator. Of those, 202 match
exactly. Two explicit boundaries retain the conservative untyped proof-slot
order and the kernel's stronger selected-read equation. This is regression
association evidence, not a universal Lean source-execution refinement.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import sys
import tempfile

REPOSITORY = Path(os.environ.get('JIHOO_REPOSITORY', Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(REPOSITORY / 'tests'))
from core_certificate_process import ROOT, command, success
from core_native_kernel_correspondence import Snapshot
from core_typing_producer import require

ACKNOWLEDGEMENT = (b'native full ACU: 204 actual outputs convert; 202 exact forms match; '
                   b'read and proof-slot boundaries checked\n')


def run(compiler, checker, output, *, driver_source=None, driver_binary=None, proofs_root=None):
    output.mkdir(parents=True, exist_ok=True)
    driver_source = driver_source or ROOT / 'tests/core_native_acu_normalizer.jh'
    proofs_root = proofs_root or ROOT / 'proofs'
    driver = driver_binary or output / 'core-native-acu-normalizer'
    if driver_binary is None:
        success(command([*compiler, 'build', '-O2', '-I', ROOT / 'compiler', '-I', ROOT / 'tests',
                         driver_source, '-o', driver]))
    observations = success(command([driver]))
    lines = observations.decode().splitlines()
    require(len(lines) == 204, 'native full ACU coverage count')
    require({int(line.split('\t')[0]) for line in lines} == set(range(204)),
            'native full ACU coverage keys')

    def check(name, payload, accepted):
        (output / f'{name}.tsv').write_bytes(payload)
        result = command(checker, payload, cwd=proofs_root)
        (output / f'{name}.checker.stdout').write_bytes(result.stdout)
        (output / f'{name}.checker.stderr').write_bytes(result.stderr)
        require((result.returncode == 0) == accepted,
                f'{name}: unexpected full ACU comparison: {result.stderr.decode(errors="replace")}')
        if accepted:
            require(result.stdout == ACKNOWLEDGEMENT, f'{name}: missing comparison acknowledgement')
        return {'case': name, 'origin': 'actual Core.normal' if accepted else 'synthetic mutation',
                'admission': 'accept' if accepted else 'reject',
                'sha256': hashlib.sha256(payload).hexdigest()}

    results = [check('observations', observations, True)]

    def replaced(index, fields):
        mutated = list(lines)
        mutated[index] = '\t'.join(fields)
        return ('\n'.join(mutated) + '\n').encode()

    repeated = list(lines)
    repeated[-1] = repeated[0]
    results.append(check('duplicate-key', ('\n'.join(repeated) + '\n').encode(), False))
    results.append(check('missing-case', ('\n'.join(lines[:-1]) + '\n').encode(), False))

    fields = lines[199].split('\t')
    after = Snapshot.read(fields[2].encode())
    after.type = after.term
    fields[2] = after.encode().decode()
    results.append(check('wrong-normal-layout', replaced(199, fields), False))

    fields = lines[199].split('\t')
    after = Snapshot.read(fields[2].encode())
    after.nodes[0] = (5, (), ())
    fields[2] = after.encode().decode()
    results.append(check('modified-existing-node', replaced(199, fields), False))

    fields = lines[202].split('\t')
    after = Snapshot.read(fields[2].encode())
    _, _, index_refs = after.nodes[after.type]
    _, _, element_refs = after.nodes[index_refs[0]]
    after.type = element_refs[1]
    fields[2] = after.encode().decode()
    results.append(check('removed-read-boundary', replaced(202, fields), False))

    fields = lines[203].split('\t')
    before, after = Snapshot.read(fields[1].encode()), Snapshot.read(fields[2].encode())
    _, _, refs = before.nodes[before.term]
    after.nodes.append((17, (), (refs[1], refs[0])))
    after.type = len(after.nodes) - 1
    fields[2] = after.encode().decode()
    results.append(check('removed-proof-order-boundary', replaced(203, fields), False))

    fields = lines[0].split('\t')
    after = Snapshot.read(fields[2].encode())
    after.type = 0
    fields[2] = after.encode().decode()
    results.append(check('unrelated-result', replaced(0, fields), False))

    fields = lines[0].split('\t')
    fields[0] = '204'
    results.append(check('outside-grid', replaced(0, fields), False))

    (output / 'manifest.json').write_text(json.dumps({
        'claim': 'regression evidence; source/IO/allocation association is not a Lean refinement theorem',
        'core_sha256': hashlib.sha256((ROOT / 'compiler/core.jh').read_bytes()).hexdigest(),
        'driver_sha256': hashlib.sha256(driver_source.read_bytes()).hexdigest(),
        'native_operations': 204,
        'exact_matches': 202,
        'explicit_boundaries': ['selected read contracts more than Core.normal',
                                'untyped proof fields stay in structural atom ordering'],
        'checks': results,
    }, indent=2) + '\n')
    print('native full ACU correspondence: 204 actual normalizations and 8 mutations passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='out/jihoo')
    parser.add_argument('--checker', default='lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeACUNormalizer.lean')
    parser.add_argument('--driver-source', type=Path)
    parser.add_argument('--driver-binary', type=Path)
    parser.add_argument('--proofs-root', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    options = dict(driver_source=args.driver_source, driver_binary=args.driver_binary, proofs_root=args.proofs_root)
    if args.output:
        run(shlex.split(args.compiler), shlex.split(args.checker), args.output.resolve(), **options)
    else:
        with tempfile.TemporaryDirectory(prefix='native-full-acu-correspondence-') as directory:
            run(shlex.split(args.compiler), shlex.split(args.checker), Path(directory), **options)


if __name__ == '__main__':
    main()
