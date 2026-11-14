#!/usr/bin/env python3
"""Exact native family declarations versus the proved signature checker.

The envelope contains raw constructor types, never trusted signatures or layout
bits. Source/IO/runtime fidelity remains outside the Lean admission theorem.
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
class Family:
    data: int
    params: int
    arity: int
    globals: int
    constructors: list[int]


@dataclass
class Program:
    definitions: list[tuple[int, int]]
    families: list[Family]
    nodes: list[tuple[int, tuple[int, ...], tuple[int, ...]]]

    @classmethod
    def read(cls, payload):
        reader = Reader(payload)
        require(reader.number() == 6, 'wrong family program version')
        count = reader.number()
        require(count <= 1024, 'definition count limit')
        definitions = [(reader.number(), reader.number()) for _ in range(count)]
        count = reader.number()
        require(count <= 1024, 'family count limit')
        families = [Family(reader.number(), reader.number(), reader.number(), reader.number(),
                           reader.vector(4096)) for _ in range(count)]
        require(sum(len(f.constructors) for f in families) <= 4096, 'constructor count limit')
        count = reader.number()
        require(count <= 4096, 'node count limit')
        nodes = [(reader.number(), tuple(reader.vector(4)), tuple(reader.vector())) for _ in range(count)]
        reader.end()
        result = cls(definitions, families, nodes)
        require(result.encode() == payload, 'noncanonical family program')
        return result

    def encode(self):
        fields = [6, len(self.definitions)]
        for ty, value in self.definitions:
            fields.extend((ty, value))
        fields.append(len(self.families))
        for family in self.families:
            fields.extend((family.data, family.params, family.arity, family.globals,
                           len(family.constructors), *family.constructors))
        fields.append(len(self.nodes))
        for tag, payload, refs in self.nodes:
            fields.extend((tag, len(payload), *payload, len(refs), *refs))
        return encode_numbers(fields)


CASES = {
    'bits': ('(data Bit (zero Bit) (one Bit))', True, True),
    'nat': ('(data Nat (zero Nat) (succ (pi n Nat Nat)))', True, True),
    'parameter': ('(data D 1 1 (mk (pi0 n U64 (D n))))', True, True),
    'parameter-rec': ('(data D 1 1 (base (pi0 n U64 (D n))) (step (pi0 n U64 (pi r (D n) (D n)))))', True, True),
    'negative': ('(data Bad (mk (pi f (pi x Bad U64) Bad)))', False, False),
    'nonerased-prop-rec': ('(inductive Bad 0 (step (pi p Bad Bad)))', False, False),
    'beta-hidden-rec': ('(data Bad (mk (pi f (app (lam x U64 Bad) 0) Bad)))', False, False),
    'interleaved': ('(def n U64 7) (data Bit (zero Bit) (one Bit)) (def value (Eq n 7) (refl 7))', True, True),
    'constructor-use-gap': ('(data Bit (zero Bit) (one Bit)) (def value Bit zero)', True, False),
    'eqchain': ('(inductive Chain 2 (chainBase (pi n U64 (Chain n n))) (chainStep (pi x U64 (pi y U64 (pi0 p (Chain x y) (Chain x y))))))', True, True),
    'trivial-prop': ('(inductive Trivial 0 (intro Trivial))', True, True),
    'arity-limit': ('(inductive Big 17 (intro Big))', False, False),
    'changed-parameter': ('(data D 1 1 (mk (pi0 n U64 (D 0))))', False, False),
    'relevant-parameter': ('(data D 1 1 (mk (pi n U64 (D n))))', False, False),
    'earlier-family-field-gap': ('(data A (a A)) (data B (b (pi x A B)))', True, False),
    'buffer-field-gap': ('(data Box (box (pi b (Buffer 1) Box)))', True, False),
    'two-families': ('(data Bit (zero Bit) (one Bit)) (data Nat (z Nat) (s (pi n Nat Nat)))', True, True),
    'global-index': ('(def fixed U64 7) (inductive P 1 (intro (P fixed)))', True, True),
    'empty': ('', True, True),
    'literal-only': ('(def value U64 7)', True, True),
}


def run(compiler, checker, output):
    output.mkdir(parents=True, exist_ok=True)
    exporter = output / 'core-native-families'
    success(command([*compiler, 'build', '-O2', '-I', 'compiler',
                     'tests/core_native_snapshots.jh', '-o', exporter]))
    observations = []
    retained = {}

    def check(name, payload, accepted, origin):
        (output / f'{name}.snapshot').write_bytes(payload)
        result = command([*checker, '64'], payload, cwd=ROOT / 'proofs')
        (output / f'{name}.checker.stdout').write_bytes(result.stdout)
        (output / f'{name}.checker.stderr').write_bytes(result.stderr)
        require((result.returncode == 0) == accepted,
                f'{name}: unexpected family admission: {(result.stdout + result.stderr).decode(errors="replace")}')
        if accepted:
            require(result.stdout == b'exact native family program accepted\n',
                    f'{name}: missing exact family acknowledgement')
        return {'case': name, 'origin': origin, 'admission': 'accept' if accepted else 'reject',
                'snapshot_sha256': hashlib.sha256(payload).hexdigest()}

    for name, (source, native, admitted) in CASES.items():
        (output / f'{name}.jhc').write_text(source)
        result = command([exporter, 'families'], source.encode())
        (output / f'{name}.native.stderr').write_bytes(result.stderr)
        require((result.returncode == 0) == native,
                f'{name}: unexpected native family check: {result.stderr.decode(errors="replace")}')
        if native:
            Program.read(result.stdout)
            retained[name] = result.stdout
            observations.append(check(name, result.stdout, admitted, 'actual Core exporter'))
        else:
            require(result.stderr, f'{name}: missing native rejection diagnostic')
            observations.append({'case': name, 'origin': 'actual Core exporter', 'native': 'reject'})

    ind, u64, seven = (11, (0, 0), ()), (4, (), ()), (47, (7,), ())
    nat = [ind, (44, (0,), (0, 0))]
    synthetic = {
        'arity-over-limit': Program([], [Family(1, 0, 17, 0, [0])], [ind]),
        'parameters-over-arity': Program([], [Family(1, 1, 0, 0, [0])], [ind]),
        'proposition-parameters': Program([], [Family(0, 1, 0, 0, [0])], [ind]),
        'forward-declaration-boundary': Program([], [Family(1, 0, 0, 1, [0])], [ind]),
        'wrong-family-reference': Program([], [Family(1, 0, 0, 0, [0])], [(11, (1, 0), ())]),
        'wrong-constructor-result': Program([], [Family(1, 0, 0, 0, [0])], [u64]),
        'negative-recursion': Program([], [Family(1, 0, 0, 0, [3])],
            [ind, u64, (44, (0,), (0, 1)), (44, (0,), (2, 0))]),
        'relevant-proposition-recursion': Program([], [Family(0, 0, 0, 0, [1])], nat),
        'erased-data-recursion': Program([], [Family(1, 0, 0, 0, [1])],
            [ind, (44, (1,), (0, 0))]),
        'changed-parameter-index': Program([], [Family(1, 1, 1, 0, [8])], [
            u64, (0, (0,), ()), (11, (0, 1), (1,)), (0, (1,), ()),
            (11, (0, 1), (3,)), (47, (0,), ()), (11, (0, 1), (5,)),
            (44, (0,), (2, 6)), (44, (1,), (0, 7))]),
        'missing-constructor-root': Program([], [Family(1, 0, 0, 0, [99])], [ind]),
        'unused-cyclic-node': Program([], [Family(1, 0, 0, 0, [0])],
            [ind, (17, (), (1, 1))]),
        'unused-malformed-node': Program([], [Family(1, 0, 0, 0, [0])],
            [ind, (17, (), ())]),
        'global-order-reversal': Program([(0, 1)],
            [Family(1, 0, 0, 1, [2]), Family(1, 0, 0, 0, [3])],
            [u64, seven, ind, (11, (1, 0), ())]),
        'forged-ghost-definition': Program([(2, 3)], [], [
            u64, (0, (0,), ()), (44, (1,), (0, 0)), (45, (1,), (0, 1))]),
    }
    additional = [check(name, program.encode(), False, 'synthetic')
                  for name, program in synthetic.items()]
    additional.append(check('trailing-newline', retained['nat'] + b'\n', False, 'synthetic'))
    additional.append(check('empty-bytes', b'', False, 'synthetic'))
    additional.append(check('wrong-version', encode_numbers([5, 0, 0]), False, 'synthetic'))
    (output / 'manifest.json').write_text(json.dumps({
        'claim': 'signature regression evidence; native source/IO fidelity and family term typing remain open',
        'core_sha256': hashlib.sha256((ROOT / 'compiler/core.jh').read_bytes()).hexdigest(),
        'exporter_sha256': hashlib.sha256((ROOT / 'compiler/core_native_snapshot.jh').read_bytes()).hexdigest(),
        'cases': observations, 'additional_checks': additional,
    }, indent=2) + '\n')
    print(f'native family correspondence: {len(CASES)} source fixtures and '
          f'{len(additional)} additional checks passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeFamilies.lean')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        run(shlex.split(args.compiler), shlex.split(args.checker), args.output.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='native-family-correspondence-') as directory:
            run(shlex.split(args.compiler), shlex.split(args.checker), Path(directory))


if __name__ == '__main__':
    main()
