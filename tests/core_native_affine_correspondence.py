#!/usr/bin/env python3
"""Compare actual native affine normalization with proved canonical forms.

No Python arithmetic oracle, derivation certificate, or source-refinement
assumption is supplied to the Lean validator.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shlex
import tempfile

from core_certificate_process import ROOT, command, success
from core_native_kernel_correspondence import Snapshot
from core_typing_producer import require


def run(compiler, checker, output):
    output.mkdir(parents=True, exist_ok=True)
    driver = output / 'core-native-affine'
    success(command([*compiler, 'build', '-O2', '-I', 'compiler',
                     'tests/core_native_affine.jh', '-o', driver]))
    observations = success(command([driver]))
    lines = observations.decode().splitlines()
    require(len(lines) == 90, 'native affine coverage count')
    keys = [tuple(map(int, line.split('\t')[:3])) for line in lines]
    require(set(keys) == {(v, n, g) for v in range(5) for n in range(6) for g in range(3)},
            'native affine coverage grid')

    def check(name, payload, accepted):
        (output / f'{name}.tsv').write_bytes(payload)
        result = command(checker, payload, cwd=ROOT / 'proofs')
        (output / f'{name}.checker.stdout').write_bytes(result.stdout)
        (output / f'{name}.checker.stderr').write_bytes(result.stderr)
        require((result.returncode == 0) == accepted,
                f'{name}: unexpected affine comparison: {result.stderr.decode(errors="replace")}')
        if accepted:
            require(result.stdout == b'native affine sums: 90 actual Core.normal results match proved canonical forms\n',
                    f'{name}: missing canonical comparison acknowledgement')
        return {'case': name, 'origin': 'actual Core.normal' if accepted else 'synthetic',
                'admission': 'accept' if accepted else 'reject',
                'sha256': hashlib.sha256(payload).hexdigest()}

    results = [check('observations', observations, True)]

    def replaced(index, fields):
        mutated = list(lines)
        mutated[index] = '\t'.join(fields)
        return ('\n'.join(mutated) + '\n').encode()

    repeated = list(lines)
    repeated[-1] = repeated[0]
    results.append(check('duplicate-grid-entry', ('\n'.join(repeated) + '\n').encode(), False))
    fields = lines[-1].split('\t')
    after = Snapshot.read(fields[4].encode())
    after.type = after.term
    fields[4] = after.encode().decode()
    results.append(check('wrong-normal-result', replaced(len(lines) - 1, fields), False))
    fields = lines[-1].split('\t')
    after = Snapshot.read(fields[4].encode())
    after.nodes[0] = (5, (), ())
    fields[4] = after.encode().decode()
    results.append(check('modified-existing-node', replaced(len(lines) - 1, fields), False))
    fields = lines[0].split('\t')
    before, after = Snapshot.read(fields[3].encode()), Snapshot.read(fields[4].encode())
    before.nodes[0] = after.nodes[0] = (5, (), ())
    after.type = 0
    fields[3], fields[4] = before.encode().decode(), after.encode().decode()
    results.append(check('unsupported-affine-atom', replaced(0, fields), False))
    fields = lines[0].split('\t')
    fields[2] = '9'
    results.append(check('outside-grid', replaced(0, fields), False))
    (output / 'manifest.json').write_text(json.dumps({
        'claim': 'regression evidence; native source/IO/allocation fidelity is not a Lean refinement theorem',
        'core_sha256': hashlib.sha256((ROOT / 'compiler/core.jh').read_bytes()).hexdigest(),
        'driver_sha256': hashlib.sha256((ROOT / 'tests/core_native_affine.jh').read_bytes()).hexdigest(),
        'native_operations': 90,
        'checks': results,
    }, indent=2) + '\n')
    print('native affine correspondence: 90 actual normalizations and 5 mutations passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeAffine.lean')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        run(shlex.split(args.compiler), shlex.split(args.checker), args.output.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='native-affine-correspondence-') as directory:
            run(shlex.split(args.compiler), shlex.split(args.checker), Path(directory))


if __name__ == '__main__':
    main()
