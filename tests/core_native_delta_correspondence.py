#!/usr/bin/env python3
"""Checked mixed environments and actual Core.normal versus proved delta/ACU.

The source/export/IO association remains regression evidence. This does not
replace native operational refinement. The adapter uses the installed delta/ACU
typing checker for original bodies and observed normal results.
Run local compiler/checker jobs through scripts/proof-limits.sh.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shlex
import tempfile

from core_certificate_process import ROOT, command, success
from core_native_family_correspondence import Program
from core_native_kernel_correspondence import Snapshot
from core_typing_producer import require

CASES = {
    'literal': ('(def value U64 7)', True, True),
    'constant-chain': ('(def first U64 7) (def second U64 first) (def value U64 second)', True, True),
    'under-lambda': ('(def fixed U64 7) (def value (pi x U64 U64) (lam x U64 fixed))', True, True),
    'under-two-binders': ('(def fixed U64 7) (def value (pi x U64 (pi y U64 U64)) '
                          '(lam x U64 (lam y U64 fixed)))', True, True),
    'scalar-type-alias': ('(def Scalar (Type 0) I64) '
                          '(def identity (pi x Scalar Scalar) (lam x Scalar x)) '
                          '(def value Scalar (app identity (int -7)))', True, True),
    'function-type-alias': ('(def Function (Type 0) (pi x U64 U64)) '
                            '(def identity Function (lam x U64 x)) '
                            '(def value U64 (app identity 7))', True, True),
    'global-beta': ('(def fixed U64 7) (def identity (pi x U64 U64) (lam x U64 x)) '
                    '(def value U64 (app identity fixed))', True, True),
    'buffer-type-alias': ('(def Heap (Type 0) (Buffer 2)) (def value (Type 0) Heap)', True, True),
    'buffer-value-alias': ('(def owned (Buffer 2) (alloc 2 (int 0))) '
                           '(def value (Buffer 2) owned)', True, True),
    'flat-family-value': ('(data Bit (zero Bit) (one Bit)) '
                          '(def saved Bit one) (def value Bit saved)', True, True),
    'boxed-family-value': ('(data Box (box (pi b (Buffer 2) Box))) '
                           '(def saved Box (box (alloc 2 (int 0)))) (def value Box saved)', True, True),
    'global-affine-sum': ('(def fixed U64 7) (def value (pi x U64 U64) '
                          '(lam x U64 (uadd fixed (uadd x fixed))))', True, True),
    'global-proof': ('(def fixed U64 7) (def saved (Eq fixed 7) (refl fixed)) '
                     '(def value (Eq 7 7) saved)', True, True),
    'dependent-array': ('(def n U64 2) (def value (pi i U64 (Array n)) '
                         '(lam i U64 (array (int 7) (int 9))))', True, True),
    'erased-global-argument': ('(def saved (Eq 7 7) (refl 7)) '
                              '(def value U64 (app (lam0 p (Eq 7 7) 7) saved))', True, True),
    'generic-context-replay': ('(def identity (pi A (Type 0) (pi x A A)) '
                                 '(lam A (Type 0) (lam x A x))) '
                                 '(def value U64 (app identity U64 7))', True, True),
    'self-reference': ('(def value U64 value)', False, False),
    'forward-reference': ('(def first U64 second) (def second U64 7)', False, False),
    'wrong-global-type': ('(def first U64 7) (def value I64 first)', False, False),
}


def run(compiler, checker, output):
    output.mkdir(parents=True, exist_ok=True)
    exporter = output / 'core-native-delta'
    success(command([*compiler, 'build', '-O2', '-I', 'compiler', 'tests/core_native_delta.jh', '-o', exporter]))
    observations, checks, retained = [], [], {}

    def check(name, payload, accepted, origin, diagnostic=None):
        (output / f'{name}.tsv').write_bytes(payload)
        result = command(checker, payload, cwd=ROOT / 'proofs')
        (output / f'{name}.checker.stdout').write_bytes(result.stdout)
        (output / f'{name}.checker.stderr').write_bytes(result.stderr)
        require(result.returncode == (0 if accepted else 1),
                f'{name}: unexpected delta comparison: {result.stderr!r}')
        if accepted:
            require(result.stdout == b'native checked delta/ACU observation accepted\n',
                    f'{name}: missing acknowledgement')
        if diagnostic is not None:
            require(diagnostic in result.stderr, f'{name}: wrong rejection boundary: {result.stderr!r}')
        return {'case': name, 'origin': origin, 'accepted': accepted,
                'sha256': hashlib.sha256(payload).hexdigest()}

    for name, (source, native, admitted) in CASES.items():
        (output / f'{name}.jhc').write_text(source + '\n')
        result = command([exporter], source.encode())
        (output / f'{name}.native.stderr').write_bytes(result.stderr)
        require((result.returncode == 0) == native, f'{name}: native outcome changed: {result.stderr!r}')
        observations.append({'case': name, 'native': native, 'admitted': admitted,
                             'source_sha256': hashlib.sha256(source.encode()).hexdigest()})
        if native:
            require(result.stdout.endswith(b'\n'), f'{name}: missing protocol terminator')
            payload = result.stdout[:-1]
            fields = payload.split(b'\t')
            require(len(fields) == 3, f'{name}: malformed observation')
            Program.read(fields[0])
            Snapshot.read(fields[1])
            Snapshot.read(fields[2])
            retained[name] = payload
            checks.append(check(name, payload, admitted, 'actual checked Core.normal',
                                None if admitted else b'mixed admission rejected'))
        else:
            require(result.stderr, f'{name}: missing native diagnostic')

    fields = retained['constant-chain'].split(b'\t')
    after = Snapshot.read(fields[2])
    after.nodes[0] = (5, (), ())
    checks.append(check('mutated-prefix', b'\t'.join([fields[0], fields[1], after.encode()]), False,
                        'synthetic', b'native arena prefix changed'))
    after = Snapshot.read(fields[2])
    after.type = len(after.nodes)
    after.nodes.append((47, (999,), ()))
    checks.append(check('mutated-normal-result', b'\t'.join([fields[0], fields[1], after.encode()]), False,
                        'synthetic', b'fails proved delta/ACU comparator'))
    before, after = Snapshot.read(fields[1]), Snapshot.read(fields[2])
    before.term = before.type = after.term = 0
    checks.append(check('mutated-observed-root', b'\t'.join([fields[0], before.encode(), after.encode()]), False,
                        'synthetic', b'wrong observed source root'))
    program = Program.read(fields[0])
    self_term = len(program.nodes)
    program.nodes.append((1, (len(program.definitions) - 1,), ()))
    program.definitions[-1] = (program.definitions[-1][0], self_term)
    checks.append(check('mutated-forward-definition', b'\t'.join([program.encode(), fields[1], fields[2]]), False,
                        'synthetic', b'mixed admission rejected'))
    checks.append(check('mutated-noncanonical-program', b'\t'.join([fields[0] + b'\n', fields[1], fields[2]]), False,
                        'synthetic', b'invalid canonical mixed program'))
    checks.append(check('mutated-empty-protocol', b'', False, 'synthetic'))
    (output / 'manifest.json').write_text(json.dumps({
        'claim': 'native observation regression; installed delta/ACU typing and native observation regression; full source operational refinement remains open',
        'core_sha256': hashlib.sha256((ROOT / 'compiler/core.jh').read_bytes()).hexdigest(),
        'exporter_sha256': hashlib.sha256((ROOT / 'compiler/core_native_snapshot.jh').read_bytes()).hexdigest(),
        'cases': observations, 'checks': checks}, indent=2) + '\n')
    print(f'native checked delta correspondence: {len(observations)} source fixtures and '
          f'{len(checks)} exact-byte checks passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeDelta.lean')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        run(shlex.split(args.compiler), shlex.split(args.checker), args.output.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='native-delta-correspondence-') as directory:
            run(shlex.split(args.compiler), shlex.split(args.checker), Path(directory))


if __name__ == '__main__':
    main()
