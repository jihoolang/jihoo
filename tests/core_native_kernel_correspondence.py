#!/usr/bin/env python3
"""Actual-Core snapshots checked by the full-native-syntax Lean kernel.

Constructor coverage is distinct from typing-rule coverage. Deliberate gaps
remain explicit fixtures, and every mutation is labelled as synthetic. The
runner supplies neither typing derivations nor conversion certificates.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import shlex
import shutil
import tempfile

from core_certificate_process import ROOT, command, success
from core_kernel_correspondence import CASES as RAW_CASES
from core_typing_producer import Reader, encode_numbers, require


@dataclass(frozen=True)
class Case:
    source: str
    mode: str = 'require'
    native: bool = True
    admitted: bool = True
    diagnostic: bytes | None = None


PREDICATE = '(lam n U64 (Eq n n))'
PACKED = f'(pack {PREDICATE} 7 (refl 7))'
IDENTITY = '(lam A (Type 0) (lam x A x))'
PROOF_IDENTITY = ('(def value (pi0 p (Eq 0 0) (Eq 0 0)) '
                  '(lam0 p (Eq 0 0) p))')

CASES = {
    ('erased-index' if name == 'erased-index-gap' else name):
        Case(source, native=native,
             admitted=True if name == 'erased-index-gap' else admitted,
             diagnostic=b'type mismatch' if not native else None)
    for name, (source, native, admitted) in RAW_CASES.items()
}
CASES.update({
    'universe': Case('(def value (Type 1) (Type 0))'),
    'prop-sort': Case('(def value (Type 0) Prop)'),
    'type-in-type': Case('(def value (Type 0) (Type 0))', native=False,
                         admitted=False, diagnostic=b'type mismatch'),
    'universe-limit': Case('(def value (Type 0) (Type 32))', native=False,
                           admitted=False, diagnostic=b'universe level limit'),
    'impredicative-prop': Case('(def value Prop (pi A (Type 0) (Eq 0 0)))'),
    'impredicative-high-universe': Case('(def value Prop (pi A (Type 31) (Eq 0 0)))'),
    'type-abstraction': Case(f'(def value (pi A (Type 0) (pi x A A)) {IDENTITY})'),
    'polymorphic-application': Case(f'(def value U64 (app {IDENTITY} U64 7))'),
    'code-polymorphic-application': Case(f'(def value U64 (app {IDENTITY} U64 7))',
                                        mode='code-require'),
    'code-scalar': Case('(def value U64 7)', mode='code-require'),
    'ghost-erased-proof': Case(PROOF_IDENTITY),
    'code-erased-proof-rejected': Case(PROOF_IDENTITY, mode='code-require', native=False,
                                        admitted=False, diagnostic=b'erased'),
    'code-erased-index': Case(RAW_CASES['erased-index-gap'][0], mode='code-require'),
    'signed-arithmetic': Case('(def value I64 (mul (int -7) (int 9)))', mode='code-require'),
    'arithmetic-evidence-add': Case('(def value (Lt 4 5) (lt-add 1 2 3 (decide-lt 1 2)))'),
    'arithmetic-evidence-cancel': Case('(def value (Lt 1 2) (lt-cancel 1 2 3 (decide-lt 4 5)))'),
    'arithmetic-evidence-le': Case('(def value (Lt 0 2) (lt-le 0 1 2 (decide-lt 0 1) (decide-lt 1 3)))'),
    'transport': Case(f'(def value (Eq 7 7) (transport {PREDICATE} (refl 7) (refl 7)))'),
    'refinement-pack': Case(f'(def value (Refine {PREDICATE}) {PACKED})'),
    'refinement-witness': Case(f'(def value U64 (witness {PACKED}))', mode='code-require'),
    'refinement-proof': Case(f'(def value (Eq 7 7) (proof {PACKED}))'),
    'owned-allocation-gap': Case('(def value (Buffer 2) (alloc 2 (int 0)))', admitted=False),
    'owned-consumption-gap': Case('(def value (pi b (Buffer 1) U64) '
                                  '(lam b (Buffer 1) (free b 7)))', admitted=False),
    'branch-gap': Case('(def value U64 (if-eq 0 0 p 7 8))', admitted=False),
    'fold-gap': Case('(def value I64 (fold 2 (int 0) '
                      '(lam i U64 (lam0 p (Lt i 2) (lam acc I64 acc)))))', admitted=False),
})


@dataclass
class Snapshot:
    ghost: int
    term: int
    type: int
    nodes: list[tuple[int, tuple[int, ...], tuple[int, ...]]]

    @classmethod
    def read(cls, payload):
        reader = Reader(payload)
        require(reader.number() == 4, 'wrong full-native snapshot version')
        ghost, term, ty = reader.number(), reader.number(), reader.number()
        require(ghost in (0, 1), 'invalid snapshot mode')
        count = reader.number()
        require(count <= 4096, 'native graph count limit')
        nodes = []
        for index in range(count):
            tag = reader.number()
            fields, refs = tuple(reader.vector(4)), tuple(reader.vector())
            require(tag < 54, 'unknown native constructor tag')
            require(all(ref < index for ref in refs), 'native graph reference is not backwards')
            nodes.append((tag, fields, refs))
        reader.end()
        require(term < count and ty < count, 'native selected root outside graph')
        result = cls(ghost, term, ty, nodes)
        require(result.encode() == payload, 'noncanonical native snapshot')
        return result

    def encode(self):
        fields = [4, self.ghost, self.term, self.type, len(self.nodes)]
        for tag, payload, refs in self.nodes:
            fields.extend((tag, len(payload), *payload, len(refs), *refs))
        return encode_numbers(fields)


def run(compiler, checker, output):
    output.mkdir(parents=True, exist_ok=True)
    exporter = output / 'core-native-snapshots'
    writer = output / 'core-native-schema'
    for source, target in (('tests/core_native_snapshots.jh', exporter),
                           ('tests/core_native_schema.jh', writer)):
        success(command([*compiler, 'build', '-O2', '-I', 'compiler', source, '-o', target]))
    schema = success(command(['python3', 'tests/native_kernel_schema.py',
                              '--native-writer', writer]))
    (output / 'schema-report.txt').write_bytes(schema)
    observations, additional, retained = [], [], {}

    def check(name, payload, accepted, *, fuel=64, diagnostic=None, origin='synthetic'):
        (output / f'{name}.snapshot').write_bytes(payload)
        result = command([*checker, str(fuel)], payload, cwd=ROOT / 'proofs')
        require(result.returncode == (0 if accepted else 1),
                f'{name}: Lean outcome changed: {result.stderr!r}')
        if diagnostic is not None:
            require(diagnostic in result.stderr,
                    f'{name}: wrong rejection boundary: {result.stderr!r}')
        record = {'case': name, 'origin': origin, 'fuel': fuel,
                  'admission': 'accept' if accepted else 'reject',
                  'snapshot_sha256': hashlib.sha256(payload).hexdigest()}
        return record

    for name, case in CASES.items():
        (output / f'{name}.core').write_text(case.source + '\n')
        result = command([exporter, case.mode], case.source.encode())
        require(result.returncode in (0, 1), f'{name}: native exporter crashed: {result.stderr!r}')
        require((result.returncode == 0) == case.native,
                f'{name}: native outcome changed: {result.stderr!r}')
        if not case.native:
            require(case.diagnostic is not None and case.diagnostic in result.stderr,
                    f'{name}: unexpected native rejection: {result.stderr!r}')
            (output / f'{name}.native-rejection.txt').write_bytes(result.stderr)
            observations.append({'case': name, 'mode': case.mode, 'native': 'reject',
                                 'admission': 'not run'})
            continue
        snapshot = Snapshot.read(result.stdout)
        require(snapshot.ghost == int(not case.mode.startswith('code-')),
                f'{name}: exporter mode changed')
        retained[name] = result.stdout
        record = check(name, result.stdout, case.admitted, origin='actual Core exporter',
                       diagnostic=None if case.admitted else b'native-syntax admission rejects')
        record.update({'mode': case.mode, 'native': 'accept'})
        observations.append(record)

    for name in ('dependent', 'nested-capture', 'dependent-array', 'dependent-reader',
                 'type-abstraction', 'polymorphic-application', 'transport', 'refinement-proof'):
        case = CASES[name]
        payload = success(command([exporter, 'infer'], case.source.encode()))
        Snapshot.read(payload)
        additional.append(check(f'{name}.inferred', payload, True, origin='actual Core exporter'))

    for fuel in (0, 1):
        additional.append(check(f'fuel-{fuel}', retained['dependent'], False, fuel=fuel,
                                diagnostic=b'native-syntax admission rejects'))

    original = Snapshot.read(retained['dependent'])
    false_eq_nodes = [*original.nodes, (47, (7,), ()), (47, (8,), ())]
    eq_root = len(false_eq_nodes)
    false_eq_nodes.append((8, (), (eq_root - 2, eq_root - 1)))
    false_eq = Snapshot(1, original.term, eq_root, false_eq_nodes).encode()
    Snapshot.read(false_eq)
    additional.append(check('false-equality-mutation', false_eq, False,
                            diagnostic=b'native-syntax admission rejects'))

    bound = Snapshot.read(retained['less-evidence'])
    false_lt_nodes = [*bound.nodes, (47, (0,), ())]
    lt_root = len(false_lt_nodes)
    false_lt_nodes.append((7, (), (lt_root - 1, lt_root - 1)))
    false_lt = Snapshot(1, bound.term, lt_root, false_lt_nodes).encode()
    Snapshot.read(false_lt)
    additional.append(check('false-bound-mutation', false_lt, False,
                            diagnostic=b'native-syntax admission rejects'))

    mode = Snapshot.read(retained['ghost-erased-proof'])
    additional.append(check('erasure-mode-mutation', Snapshot(0, mode.term, mode.type, mode.nodes).encode(),
                            False, diagnostic=b'native-syntax admission rejects'))
    for name, term, ty, nodes in (
            ('invalid-term-root', len(original.nodes), original.type, original.nodes),
            ('invalid-type-root', original.term, len(original.nodes), original.nodes),
            ('unreachable-self-edge', original.term, original.type,
             [*original.nodes, (6, (), (len(original.nodes),))]),
            ('unreachable-malformed-arity', original.term, original.type,
             [*original.nodes, (10, (), ())]),
            ('unsupported-global', len(original.nodes), original.type,
             [*original.nodes, (1, (0,), ())]),
            ('unsupported-family', len(original.nodes), original.type,
             [*original.nodes, (11, (0, 0), ())])):
        additional.append(check(name, Snapshot(original.ghost, term, ty, nodes).encode(),
                                False, diagnostic=b'native-syntax admission rejects'))
    additional.append(check('trailing-newline', retained['literal'] + b'\n', False))
    additional.append(check('empty-snapshot', b'', False))

    revision = None
    if (ROOT / '.git').exists() and shutil.which('git') is not None:
        result = command(['git', 'rev-parse', 'HEAD'])
        if result.returncode == 0:
            revision = result.stdout.decode().strip()
    manifest = {
        'claim': 'regression evidence; source/IO/runtime fidelity is not a Lean refinement theorem',
        'core_sha256': hashlib.sha256((ROOT / 'compiler/core.jh').read_bytes()).hexdigest(),
        'exporter_sha256': hashlib.sha256((ROOT / 'compiler/core_native_snapshot.jh').read_bytes()).hexdigest(),
        'commit': revision,
        'schema': schema.decode().strip(),
        'cases': observations,
        'additional_checks': additional,
    }
    (output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(f'native kernel correspondence: {len(CASES)} native fixtures and '
          f'{len(additional)} additional checks passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean -DwarningAsError=true --run CheckNativeInference.lean')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        run(shlex.split(args.compiler), shlex.split(args.checker), args.output.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='native-kernel-correspondence-') as directory:
            run(shlex.split(args.compiler), shlex.split(args.checker), Path(directory))


if __name__ == '__main__':
    main()
