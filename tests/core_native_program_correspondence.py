#!/usr/bin/env python3
"""Exact-byte regression evidence for ordered native global environments.

The native exporter checks the source first; the Lean process independently
checks its retained version-5 graph. Source/IO fidelity remains outside Lean.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import shlex
import tempfile

from core_certificate_process import ROOT, command, success
from core_typing_producer import Reader, encode_numbers, require


@dataclass
class Program:
    declarations: list[tuple[int, int]]
    nodes: list[tuple[int, tuple[int, ...], tuple[int, ...]]]

    @classmethod
    def read(cls, payload):
        reader = Reader(payload)
        require(reader.number() == 5, 'wrong native program version')
        count = reader.number()
        require(count <= 1024, 'declaration limit')
        declarations = [(reader.number(), reader.number()) for _ in range(count)]
        count = reader.number()
        require(count <= 4096, 'node limit')
        nodes = [(reader.number(), tuple(reader.vector(4)), tuple(reader.vector()))
                 for _ in range(count)]
        reader.end()
        result = cls(declarations, nodes)
        require(result.encode() == payload, 'noncanonical native program')
        return result

    def encode(self):
        fields = [5, len(self.declarations)]
        for ty, value in self.declarations:
            fields.extend((ty, value))
        fields.append(len(self.nodes))
        for tag, payload, refs in self.nodes:
            fields.extend((tag, len(payload), *payload, len(refs), *refs))
        return encode_numbers(fields)


CASES = {
    'empty': ('', True, True),
    'literal': ('(def value U64 7)', True, True),
    'chain': ('(def first U64 7) (def second U64 first) '
              '(def third (Eq second 7) (refl 7))', True, True),
    'type-alias': ('(def Scalar (Type 0) I64) '
                   '(def identity (pi A (Type 0) (pi x A A)) '
                   '(lam A (Type 0) (lam x A x))) '
                   '(def value Scalar (app identity Scalar (int -7)))', True, True),
    'proof-alias': ('(def evidence (Eq 7 7) (refl 7)) '
                    '(def value (Eq 7 7) evidence)', True, True),
    'erased-proof-argument': ('(def evidence (Eq 7 7) (refl 7)) '
                             '(def value U64 (app (lam0 p (Eq 7 7) 7) evidence))', True, True),
    'under-two-binders': ('(def fixed U64 7) '
                          '(def value (pi x U64 (pi y U64 U64)) '
                          '(lam x U64 (lam y U64 fixed)))', True, True),
    'dependent-array-reader': ('(def offset U64 1) '
                               '(def read (pi xs (Array 2) I64) '
                               '(lam xs (Array 2) (index xs offset (decide-lt 1 2)))) '
                               '(def value I64 (app read (array (int 7) (int 9))))', True, True),
    'global-type-under-binder': ('(def Scalar (Type 0) U64) '
                                '(def identity (pi x Scalar Scalar) (lam x Scalar x)) '
                                '(def value Scalar (app identity 7))', True, True),
    'erased-data-declaration': ('(def erased (pi0 x U64 U64) (lam0 x U64 x))', False, False),
    'wrong-global-type': ('(def first U64 7) (def second I64 first)', False, False),
    'false-global-equality': ('(def first U64 7) '
                              '(def evidence (Eq first 8) (refl first))', False, False),
    'self-reference': ('(def value U64 value)', False, False),
    'forward-reference': ('(def first U64 second) (def second U64 7)', False, False),
    'owned-global-gap': ('(def value (Buffer 1) (alloc 1 (int 0)))', True, False),
}


def run(compiler, checker, output):
    output.mkdir(parents=True, exist_ok=True)
    exporter = output / 'core-native-programs'
    success(command([*compiler, 'build', '-O2', '-I', 'compiler',
                     'tests/core_native_snapshots.jh', '-o', exporter]))
    observations = []
    retained = {}

    def check(name, payload, accepted, origin):
        (output / f'{name}.snapshot').write_bytes(payload)
        result = command([*checker, '64'], payload, cwd=ROOT / 'proofs')
        (output / f'{name}.checker.stderr').write_bytes(result.stderr)
        (output / f'{name}.checker.stdout').write_bytes(result.stdout)
        require((result.returncode == 0) == accepted,
                f'{name}: unexpected program admission: {result.stderr.decode(errors="replace")}')
        if accepted:
            require(result.stdout == b'exact native program accepted\n',
                    f'{name}: missing exact-byte program acknowledgement')
        return {'case': name, 'origin': origin, 'admission': 'accept' if accepted else 'reject',
                'snapshot_sha256': hashlib.sha256(payload).hexdigest()}

    for name, (source, native, admitted) in CASES.items():
        (output / f'{name}.jhc').write_text(source)
        result = command([str(exporter), 'program'], source.encode())
        (output / f'{name}.native.stderr').write_bytes(result.stderr)
        require((result.returncode == 0) == native,
                f'{name}: unexpected native check: {result.stderr.decode(errors="replace")}')
        if native:
            Program.read(result.stdout)
            retained[name] = result.stdout
            observation = check(name, result.stdout, admitted, 'actual Core exporter')
        else:
            require(result.stderr, f'{name}: missing native rejection diagnostic')
            observation = {'case': name, 'origin': 'actual Core exporter', 'native': 'reject'}
        observations.append(observation)

    boundary = output / 'core-native-global-boundary'
    success(command([*compiler, 'build', '-O2', '-I', 'compiler',
                     'tests/core_native_global_boundary.jh', '-o', boundary]))
    payload = success(command([boundary]))
    Program.read(payload)
    observations.append(check('opaque-ghost-global-code-gap', payload, False, 'actual Core API'))

    # These mutations bypass the source parser and exercise the independent
    # sequential visibility checks, including well-formed acyclic term graphs.
    scalar, seven, one, zero = (4, (), ()), (47, (7,), ()), (1, (1,), ()), (1, (0,), ())
    synthetic = {
        'self-global': Program([(0, 2)], [scalar, seven, zero]),
        'forward-global': Program([(0, 2), (0, 1)], [scalar, seven, one]),
        'missing-global': Program([(0, 2)], [scalar, seven, (1, (99,), ())]),
        'malformed-global': Program([(0, 2)], [scalar, seven, (1, (0,), (1,))]),
        'free-variable': Program([(0, 1)], [scalar, (0, (0,), ())]),
        'forged-erased-declaration': Program([(2, 4)], [
            scalar, (0, (0,), ()), (44, (1,), (0, 0)),
            (0, (0,), ()), (45, (1,), (0, 3))]),
        'unused-cycle': Program([(0, 1)], [scalar, seven, (17, (), (2, 2))]),
        'unused-malformed': Program([(0, 1)], [scalar, seven, (17, (), ())]),
        'invalid-root': Program([(0, 99)], [scalar, seven]),
        'definition-count': Program([(0, 1)] * 1025, [scalar, seven]),
    }
    additional = [check(name, program.encode(), False, 'synthetic')
                  for name, program in synthetic.items()]
    original = Program.read(retained['chain'])
    additional.append(check('reordered-declarations',
                            Program(original.declarations[::-1], original.nodes).encode(),
                            False, 'synthetic'))
    additional.append(check('trailing-newline', retained['literal'] + b'\n', False, 'synthetic'))
    additional.append(check('empty-bytes', b'', False, 'synthetic'))
    additional.append(check('old-version', encode_numbers([4, 0, 0]), False, 'synthetic'))
    manifest = {
        'claim': 'regression evidence; native source/IO fidelity is not a Lean refinement theorem',
        'core_sha256': hashlib.sha256((ROOT / 'compiler/core.jh').read_bytes()).hexdigest(),
        'exporter_sha256': hashlib.sha256((ROOT / 'compiler/core_native_snapshot.jh').read_bytes()).hexdigest(),
        'cases': observations,
        'additional_checks': additional,
    }
    (output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(f'native program correspondence: {len(CASES)} source fixtures, 1 Core API fixture and '
          f'{len(additional)} additional checks passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeProgram.lean')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        run(shlex.split(args.compiler), shlex.split(args.checker), args.output.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='native-program-correspondence-') as directory:
            run(shlex.split(args.compiler), shlex.split(args.checker), Path(directory))


if __name__ == '__main__':
    main()
