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
    'branch-eq': Case('(def value U64 (if-eq 0 0 p 7 8))'),
    'branch-lt-bounds': Case(
        '(def value (pi n U64 I64) (lam n U64 '
        '(if-lt n 2 p (index (array (int 7) (int 9)) n p) (int -1))))',
        mode='code-require'),
    'branch-dependent-result': Case(
        '(def value (pi n U64 (Eq n n)) '
        '(lam n U64 (if-eq n 0 p (refl n) (refl n))))'),
    'branch-true-conversion': Case('(def value (Eq (if-eq 0 0 p 7 8) 7) (refl 7))'),
    'branch-false-conversion': Case('(def value (Eq (if-lt 3 2 p 7 8) 8) (refl 8))'),
    'branch-type-argument': Case(
        f'(def value I64 (app {IDENTITY} (if-eq 0 0 p I64 U64) (int 7)))',
        mode='code-require'),
    'transport-proof-dependent-type': Case(
        '(def value (pi F (pi0 p (Eq 7 7) Prop) '
        '(pi0 q (app F (refl 7)) (app F (transport (lam n U64 (Eq n n)) (refl 7) (refl 7))))) '
        '(lam F (pi0 p (Eq 7 7) Prop) (lam0 q (app F (refl 7)) q)))'),
    'branch-type-mismatch': Case('(def value U64 (if-eq 0 0 p 7 (int -1)))',
                                  native=False, admitted=False, diagnostic=b'type mismatch'),
    'branch-proof-used-as-data': Case('(def value U64 (if-eq 0 0 p p 7))',
                                      native=False, admitted=False, diagnostic=b'erased'),
    'branch-scope-escape': Case(
        '(def value (pi F (pi0 p (Eq 0 0) (Type 0)) '
        '(pi f (pi0 p (Eq 0 0) (app F p)) U64)) '
        '(lam F (pi0 p (Eq 0 0) (Type 0)) '
        '(lam f (pi0 p (Eq 0 0) (app F p)) (if-eq 0 0 p (app f p) 7))))',
        native=False, admitted=False, diagnostic=b'escapes'),
    'absurd-impossible-context': Case(
        '(def value (pi0 p (Lt 0 0) U64) (lam0 p (Lt 0 0) (absurd U64 p)))',
        mode='code-require'),
    'absurd-polymorphic-target': Case(
        '(def value (pi A (Type 0) (pi0 p (Lt 0 0) A)) '
        '(lam A (Type 0) (lam0 p (Lt 0 0) (absurd A p))))'),
    'absurd-function-rejected': Case(
        '(def value (pi0 p (Lt 0 0) (pi x U64 U64)) '
        '(lam0 p (Lt 0 0) (absurd (pi x U64 U64) p)))',
        native=False, admitted=False, diagnostic=b'function'),
    'absurd-fake-proof': Case('(def value U64 (absurd U64 (refl 0)))',
                               native=False, admitted=False, diagnostic=b'absurd needs evidence'),
    'absurd-neutral-application-ghost': Case(
        '(def value (pi F (pi n U64 (Type 0)) (pi0 p (Lt 0 0) (app F 0))) '
        '(lam F (pi n U64 (Type 0)) (lam0 p (Lt 0 0) (absurd (app F 0) p))))'),
    'absurd-neutral-application-code-gap': Case(
        '(def value (pi F (pi n U64 (Type 0)) (pi0 p (Lt 0 0) (app F 0))) '
        '(lam F (pi n U64 (Type 0)) (lam0 p (Lt 0 0) (absurd (app F 0) p))))',
        mode='code-require', admitted=False),
    'ghost-absurd-function-result': Case(
        (ROOT / 'tests/core_preserves/ghost-absurd-function-result.jhc').read_text()),
    'fold-i64': Case(
        '(def value I64 (fold 2 (int 0) (lam i U64 (lam0 p (Lt i 2) (lam acc I64 (add acc (int 1)))))))',
        mode='code-require'),
    'fold-open-count': Case(
        '(def value (pi n U64 I64) (lam n U64 (fold n (int 0) (lam i U64 (lam0 p (Lt i n) (lam acc I64 (add acc (int 1))))))))',
        mode='code-require'),
    'loop-u64': Case(
        '(def value U64 (loop 2 (lam k U64 U64) 0 (lam i U64 (lam0 p (Lt i 2) (lam acc U64 (uadd acc 1))))))',
        mode='code-require'),
    'loop-i64': Case(
        '(def value I64 (loop 2 (lam k U64 I64) (int 0) (lam i U64 (lam0 p (Lt i 2) (lam acc I64 (add acc (int 1)))))))',
        mode='code-require'),
    'loop-refinement': Case(
        '(def value (Refine (lam c U64 (Eq c 2))) (loop 2 (lam k U64 (Refine (lam c U64 (Eq c k)))) (pack (lam c U64 (Eq c 0)) 0 (refl 0)) (lam i U64 (lam0 p (Lt i 2) (lam acc (Refine (lam c U64 (Eq c i))) (pack (lam c U64 (Eq c (uadd i 1))) (uadd i 1) (refl (uadd i 1))))))))',
        mode='code-require'),
    'loop-nat-induction': Case(
        '(def value (pi n U64 (Lt n (uadd n 1))) (lam n U64 (loop n (lam k U64 (Lt k (uadd k 1))) (decide-lt 0 1) (lam i U64 (lam0 p (Lt i n) (lam0 acc (Lt i (uadd i 1)) (lt-add i (uadd i 1) 1 acc)))))))',
        mode='require'),
    'loop-concrete-proof': Case(
        '(def value (Lt 2 3) (loop 2 (lam k U64 (Lt k (uadd k 1))) (decide-lt 0 1) (lam i U64 (lam0 p (Lt i 2) (lam0 acc (Lt i (uadd i 1)) (lt-add i (uadd i 1) 1 acc))))))',
        mode='require'),
    'loop-zero-count': Case(
        '(def value U64 (loop 0 (lam k U64 U64) 0 (lam i U64 (lam0 p (Lt i 0) (lam acc U64 (uadd acc 1))))))',
        mode='code-require'),
    'fold-unsigned-accumulator': Case(
        '(def value U64 (fold 2 0 (lam i U64 (lam0 p (Lt i 2) (lam acc U64 (uadd acc 1))))))',
        mode='code-require',
        native=False,
        admitted=False,
        diagnostic=b'an i64 or an owned value'),
    'loop-wrong-init': Case(
        '(def value U64 (loop 2 (lam k U64 U64) (int 0) (lam i U64 (lam0 p (Lt i 2) (lam acc U64 (uadd acc 1))))))',
        mode='code-require',
        native=False,
        admitted=False,
        diagnostic=b'type mismatch'),
    'loop-wrong-step': Case(
        '(def value U64 (loop 2 (lam k U64 U64) 0 (lam i U64 (lam0 p (Lt i 2) (lam acc I64 (add acc (int 1)))))))',
        mode='code-require',
        native=False,
        admitted=False,
        diagnostic=b'type mismatch'),
    'loop-wrong-count': Case(
        '(def value U64 (loop (int 2) (lam k U64 U64) 0 (lam i U64 (lam0 p (Lt i 2) (lam acc U64 (uadd acc 1))))))',
        mode='code-require',
        native=False,
        admitted=False,
        diagnostic=b'type mismatch'),
    'loop-type-motive': Case(
        '(def value (Type 0) (loop 2 (lam k U64 (Type 0)) U64 (lam i U64 (lam0 p (Lt i 2) (lam acc U64 (uadd acc 1))))))',
        mode='require',
        native=False,
        admitted=False,
        diagnostic=b'runtime data or evidence'),
    'loop-array-layout': Case(
        '(def value (Array 0) (loop 2 (lam k U64 (Array k)) (array) (lam i U64 (lam0 p (Lt i 2) (lam acc U64 (uadd acc 1))))))',
        mode='code-require',
        native=False,
        admitted=False,
        diagnostic=b'a scalar, a refinement or an owned value'),
    'loop-function-accumulator': Case(
        '(def value (pi x U64 U64) (loop 2 (lam k U64 (pi x U64 U64)) (lam x U64 x) (lam i U64 (lam0 p (Lt i 2) (lam acc U64 (uadd acc 1))))))',
        mode='code-require',
        native=False,
        admitted=False,
        diagnostic=b'a scalar, a refinement or an owned value'),
    'loop-false-induction-entry': Case(
        '(def value (Lt 2 3) (loop 2 (lam k U64 (Lt k (uadd k 1))) (decide-lt 0 0) (lam i U64 (lam0 p (Lt i 2) (lam0 acc (Lt i (uadd i 1)) (lt-add i (uadd i 1) 1 acc))))))',
        mode='require',
        native=False,
        admitted=False,
        diagnostic=b'decide-lt needs a true'),
    'loop-wrong-induction-step': Case(
        '(def value (Lt 2 3) (loop 2 (lam k U64 (Lt k (uadd k 1))) (decide-lt 0 1) (lam i U64 (lam0 p (Lt i 2) (lam0 acc (Lt i (uadd i 1)) acc)))))',
        mode='require',
        native=False,
        admitted=False,
        diagnostic=b'type mismatch'),
    'loop-relevant-proof-accumulator': Case(
        '(def value (Lt 2 3) (loop 2 (lam k U64 (Lt k (uadd k 1))) (decide-lt 0 1) (lam i U64 (lam0 p (Lt i 2) (lam acc (Lt i (uadd i 1)) acc)))))',
        mode='require',
        native=False,
        admitted=False,
        diagnostic=b'proof binders must be erased'),
    'loop-not-unrolled': Case(
        '(def value (Eq (loop 2 (lam k U64 U64) 0 (lam i U64 (lam0 p (Lt i 2) (lam acc U64 (uadd acc 1))))) 2) (refl 2))',
        mode='require',
        native=False,
        admitted=False,
        diagnostic=b'type mismatch'),
    'loop-owned-accumulator-gap': Case(
        '(def value (Buffer 1) (loop 2 (lam k U64 (Buffer 1)) (alloc 1 (int 0)) (lam i U64 (lam0 p (Lt i 2) (lam acc (Buffer 1) acc)))))',
        mode='code-require',
        admitted=False),
    'fold-owned-accumulator-gap': Case(
        '(def value (Buffer 1) (fold 2 (alloc 1 (int 0)) (lam i U64 (lam0 p (Lt i 2) (lam acc (Buffer 1) acc)))))',
        mode='code-require',
        admitted=False),
    'effectful-lambda-pure-profile-gap': Case(
        '(def value I64 (fold 2 (int 0) (lam i U64 (lam0 p (Lt i 2) (lam acc I64 (free (alloc 1 (int 0)) acc))))))',
        mode='code-require',
        admitted=False),
    'effectful-function-expression-rejected': Case(
        '(def value I64 (fold 2 (int 0) (free (alloc 1 (int 0)) (lam i U64 (lam0 p (Lt i 2) (lam acc I64 (add acc (int 1))))))))',
        mode='code-require',
        native=False,
        admitted=False,
        diagnostic=b'loop body that touches memory'),
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
    transformer = output / 'core-native-transforms'
    for source, target in (('tests/core_native_snapshots.jh', exporter),
                           ('tests/core_native_schema.jh', writer),
                           ('tests/core_native_transforms.jh', transformer)):
        success(command([*compiler, 'build', '-O2', '-I', 'compiler', source, '-o', target]))
    schema = success(command(['python3', 'tests/native_kernel_schema.py',
                              '--native-writer', writer]))
    (output / 'schema-report.txt').write_bytes(schema)
    transform_bytes = success(command([transformer]))
    transform_path = output / 'native-transform-observations.tsv'
    transform_path.write_bytes(transform_bytes)
    transforms = success(command(['lake', 'env', 'lean', '-DwarningAsError=true', '--run',
                                  'CheckNativeTransforms.lean', transform_path], cwd=ROOT / 'proofs'))
    (output / 'transform-report.txt').write_bytes(transforms)
    observations, additional, retained = [], [], {}

    def check(name, payload, accepted, *, fuel=64, diagnostic=None, origin='synthetic',
              declaration=False):
        (output / f'{name}.snapshot').write_bytes(payload)
        result = command([*checker, str(fuel), *(['definition'] if declaration else [])],
                         payload, cwd=ROOT / 'proofs')
        require(result.returncode == (0 if accepted else 1),
                f'{name}: Lean outcome changed: {result.stderr!r}')
        if diagnostic is not None:
            require(diagnostic in result.stderr,
                    f'{name}: wrong rejection boundary: {result.stderr!r}')
        record = {'case': name, 'origin': origin, 'fuel': fuel, 'declaration': declaration,
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

    # A declaration derives ghost/code mode from its type's sort, independently
    # of the observation-mode flag supplied in the serialized envelope.
    for name in ('literal', 'universe', 'type-abstraction', 'polymorphic-application',
                 'ghost-erased-proof', 'erased-index', 'transport', 'refinement-witness'):
        additional.append(check(f'{name}.definition', retained[name], True,
                                origin='actual Core exporter', declaration=True))
    erased_identity = Snapshot(1, 2, 3, [
        (4, (), ()), (0, (0,), ()), (45, (1,), (0, 1)), (44, (1,), (0, 0))]).encode()
    Snapshot.read(erased_identity)
    additional.append(check('erased-identity-ghost-observation', erased_identity, True))
    additional.append(check('forged-ghost-declaration', erased_identity, False,
                            declaration=True, diagnostic=b'native-syntax admission rejects'))

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
        'transforms': transforms.decode().strip(),
        'transform_observations_sha256': hashlib.sha256(transform_bytes).hexdigest(),
        'cases': observations,
        'additional_checks': additional,
    }
    (output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(f'native kernel correspondence: {len(CASES)} native fixtures and '
          f'{len(additional)} additional checks passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeInference.lean')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        run(shlex.split(args.compiler), shlex.split(args.checker), args.output.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='native-kernel-correspondence-') as directory:
            run(shlex.split(args.compiler), shlex.split(args.checker), Path(directory))


if __name__ == '__main__':
    main()
