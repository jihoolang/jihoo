#!/usr/bin/env python3
"""Retain actual runtime-use queries and compare their resource projections.

Invalid local-scope checks and unknown calls have explicit comparison policies;
the runner does not claim full inference, source execution, or heap refinement.
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
    driver = output / 'core-native-quantity'
    success(command([*compiler, 'build', '-O2', '-I', 'compiler',
                     'tests/core_native_quantity.jh', '-o', driver]))
    observations = success(command([driver]))
    lines = observations.decode().splitlines()
    require(len(lines) == 40, 'native quantity coverage count')
    cases = []
    for line in lines:
        name, policy, query, context, native, snapshot = line.split('\t')
        Snapshot.read(snapshot.encode())
        cases.append({'name': name, 'policy': policy, 'query': int(query),
                      'context': context, 'native': native,
                      'snapshot_sha256': hashlib.sha256(snapshot.encode()).hexdigest()})

    def check(name, payload, accepted):
        (output / f'{name}.tsv').write_bytes(payload)
        result = command(checker, payload, cwd=ROOT / 'proofs')
        (output / f'{name}.checker.stdout').write_bytes(result.stdout)
        (output / f'{name}.checker.stderr').write_bytes(result.stderr)
        require((result.returncode == 0) == accepted,
                f'{name}: unexpected quantity comparison: {result.stderr.decode(errors="replace")}')
        if accepted:
            require(result.stdout == b'native quantity: 32 count/rejection agreements, 7 stricter local scope checks, 1 explicit call gap\n',
                    'missing quantity comparison acknowledgement')
        return {'case': name, 'origin': 'actual Core.runtime_uses' if accepted else 'synthetic',
                'admission': 'accept' if accepted else 'reject',
                'sha256': hashlib.sha256(payload).hexdigest()}

    checks = [check('observations', observations, True)]

    def replaced(fields):
        return ('\n'.join(['\t'.join(fields), *lines[1:]]) + '\n').encode()

    fields = lines[0].split('\t')
    fields[4] = 'ok:999'
    checks.append(check('wrong-native-count', replaced(fields), False))
    fields = lines[0].split('\t')
    fields[2] = '99'
    checks.append(check('invalid-context-query', replaced(fields), False))
    fields = lines[0].split('\t')
    fields[3] = '999:0'
    checks.append(check('invalid-context-root', replaced(fields), False))
    fields = lines[0].split('\t')
    fields[1] = 'local-gap'
    checks.append(check('forged-gap-policy', replaced(fields), False))
    fields = lines[0].split('\t')
    graph = Snapshot.read(fields[5].encode())
    graph.nodes.append((17, (), (len(graph.nodes), len(graph.nodes))))
    fields[5] = graph.encode().decode()
    checks.append(check('unreachable-cycle', replaced(fields), False))
    duplicate = [*lines[:-1], lines[0]]
    checks.append(check('duplicate-observation', ('\n'.join(duplicate) + '\n').encode(), False))
    (output / 'manifest.json').write_text(json.dumps({
        'claim': 'resource projection regression evidence; source/inference/heap refinement remains open',
        'core_sha256': hashlib.sha256((ROOT / 'compiler/core.jh').read_bytes()).hexdigest(),
        'driver_sha256': hashlib.sha256((ROOT / 'tests/core_native_quantity.jh').read_bytes()).hexdigest(),
        'cases': cases, 'checks': checks,
    }, indent=2) + '\n')
    print('native quantity correspondence: 40 actual queries and 6 mutations passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeQuantity.lean')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        run(shlex.split(args.compiler), shlex.split(args.checker), args.output.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='native-quantity-correspondence-') as directory:
            run(shlex.split(args.compiler), shlex.split(args.checker), Path(directory))


if __name__ == '__main__':
    main()
