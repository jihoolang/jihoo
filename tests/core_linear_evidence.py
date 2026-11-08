#!/usr/bin/env python3
"""Check actual Core.require artifacts in the proved first-order evidence model.

The theorem concerns the retained bytes, not exporter/source provenance. This
suite tests that boundary and never publishes a failed checker/validator result.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import shlex
import tempfile

from core_certificate_process import ROOT, command, success
from core_typing_producer import Snapshot, Unsupported, require
from core_typing_certificates import snapshot_bytes


class EvidenceChecker:
    def __init__(self, exporter, checker):
        self.exporter, self.checker = exporter, checker
        self.published = 0

    def validate(self, snapshot, term, ty):
        return command([*self.checker, term, ty], snapshot, cwd=ROOT / 'proofs')

    def obtain(self, source):
        return success(command([self.exporter, 'require'], source))

    def generate(self, source, *, consumer=None):
        retained = self.obtain(source)
        roots = Snapshot.read(retained)
        success(self.validate(retained, roots.term, roots.type))
        if consumer:
            consumer(retained)
        self.published += 1
        return retained


FIXTURES = {
    'literal-equality': '(def value (Eq 3 3) (refl 3))',
    'closed-add-equality': '(def value (Eq (uadd 2 3) 5) (refl 5))',
    'closed-decide': '(def value (Lt (uadd 1 1) (uadd 1 2)) (decide-lt (uadd 1 1) 3))',
    'zero': '(def value (Lt 0 1) (zero-le 0))',
    'symbolic-identity': '(def value (pi n U64 (Eq (uadd n 0) n)) (lam n U64 (refl n)))',
    'commute': '(def value (pi x U64 (pi y U64 (Eq (uadd x y) (uadd y x)))) '
               '(lam x U64 (lam y U64 (refl (uadd x y)))))',
    'association': '(def value (pi x U64 (pi y U64 (Eq (uadd (uadd x 1) (uadd y x)) '
                   '(uadd (uadd x x) (uadd 1 y))))) '
                   '(lam x U64 (lam y U64 (refl (uadd (uadd x 1) (uadd y x))))))',
    'symbolic-zero-le': '(def value (pi n U64 (Lt 0 (uadd n 1))) (lam n U64 (zero-le n)))',
    'converted-zero-le': '(def value (pi n U64 (Lt (uadd 0 0) (uadd 1 n))) '
                         '(lam n U64 (zero-le n)))',
    'nested-zero-le': '(def value (pi x U64 (pi y U64 (Lt 0 (uadd 1 (uadd y x))))) '
                      '(lam x U64 (lam y U64 (zero-le (uadd x y)))))',
    'wide-zero-le': '(def value (Lt 0 (uadd 18446744073709551615 1)) '
                    '(zero-le 18446744073709551615))',
    'wide-equality': '(def value (Eq (uadd 18446744073709551615 1) '
                     '(uadd 1 18446744073709551615)) (refl (uadd 18446744073709551615 1)))',
}
OUTSIDE = {
    'beta-evidence': '(def value (Eq 1 1) (app (lam x U64 (refl x)) 1))',
    'evidence-hypothesis': '(def value (pi0 p (Eq 1 1) (Eq 1 1)) (lam0 p (Eq 1 1) p))',
    'subtraction': '(def value (Eq (usub 3 1 (decide-lt 1 4)) 2) (refl 2))',
}


def test(compiler, checker, output):
    exporter = output / 'snapshot'
    success(command([*compiler, 'build', '-O2', '-I', 'compiler', 'tests/core_typing_snapshots.jh',
                     '-o', exporter]))
    gate = EvidenceChecker(exporter, checker)
    cases = {}
    delivered = []
    for name, source in FIXTURES.items():
        try:
            cases[name] = gate.generate(source.encode(), consumer=delivered.append)
        except Unsupported as error:
            raise Unsupported(f'{name}: {error}') from error
        require(delivered[-1] == cases[name], 'published artifact changed')
    b = cases['literal-equality']
    s = Snapshot.read(b)
    rejected = 0

    def reject(name, data, term=None, ty=None):
        nonlocal rejected
        result = gate.validate(data, s.term if term is None else term, s.type if ty is None else ty)
        require(result.returncode == 1 and b'rejected' in result.stderr, f'{name}: {result}')
        rejected += 1

    # True statements with wrong evidence must not pass a truth-only oracle.
    malformed = {
        'false-equality': ([(1, 0), (1, 1), (13, 0), (7, 0, 1)], 2, 3),
        'false-less': ([(1, 1), (15, 0, 0), (6, 0, 0)], 1, 2),
        'wrong-proof-true-equality': ([(1, 0), (1, 1), (15, 0, 1), (7, 1, 1)], 2, 3),
        'wrong-proof-true-less': ([(1, 0), (1, 1), (13, 1), (6, 0, 1)], 2, 3),
        'free-variable': ([(0, 0), (13, 0), (7, 0, 0)], 1, 2),
        'false-under-lambda': ([(3,), (0, 0), (1, 1), (16, 1, 2), (13, 1),
                                (7, 1, 3), (9, 0, 0, 4), (8, 0, 0, 5)], 6, 7),
        'erased-scalar-binder': ([(3,), (0, 0), (13, 1), (7, 1, 1),
                                  (9, 1, 0, 2), (8, 1, 0, 3)], 4, 5),
        'wrong-lambda-domain': ([(4,), (1, 1), (13, 1), (7, 1, 1),
                                 (9, 0, 0, 2), (8, 0, 0, 3)], 4, 5),
        'universal-constant-mismatch': ([(3,), (1, 0), (1, 1), (13, 1), (7, 2, 2),
                                         (9, 0, 0, 3), (8, 0, 0, 4)], 5, 6),
    }
    for name, (graph, term, ty) in malformed.items():
        reject(name, snapshot_bytes(s, graph=graph, term=term, ty=ty), term, ty)
    reject('trailing-data', b + b';')
    reject('excessive-token', b'1' * 65 + b';')
    duplicate = snapshot_bytes(s, graph=[*s.graph, s.graph[s.term]], term=len(s.graph))
    reject('changed-term-root', duplicate)
    duplicate_type = snapshot_bytes(s, graph=[*s.graph, s.graph[s.type]], ty=len(s.graph))
    reject('changed-type-root', duplicate_type)
    # Root selection is exact. A separately requested valid duplicate remains
    # valid; this API does not authenticate an independently expected graph.
    success(gate.validate(duplicate, len(s.graph), s.type))
    dead = snapshot_bytes(s, graph=[*s.graph, (0, 0)])
    success(gate.validate(dead, s.term, s.type))
    bad_dead = snapshot_bytes(s, graph=[*s.graph, (16, len(s.graph), len(s.graph))])
    reject('invalid-unreachable-node', bad_dead)
    graph = [(1, 0)]
    for _ in range(14):
        graph.append((16, len(graph)-1, len(graph)-1))
    root = len(graph)-1
    graph += [(13, root), (7, root, root)]
    reject('repeated-reference-budget', snapshot_bytes(s, graph=graph, term=root+1, ty=root+2), root+1, root+2)
    for name, source in OUTSIDE.items():
        snapshot = success(command([exporter, 'require'], source.encode()))
        ss = Snapshot.read(snapshot)
        reject(f'valid-core-outside-{name}', snapshot, ss.term, ss.type)
    failed = output / 'failed-exporter'
    # A nonzero exit is fatal even if stdout is a completely valid artifact.
    failed.write_bytes(b"#!/bin/sh\nprintf '%s' '" + b + b"'\nexit 1\n")
    failed.chmod(0o755)
    blocked = EvidenceChecker(failed, checker)
    try:
        blocked.generate(b'ignored', consumer=delivered.append)
    except Unsupported:
        pass
    else:
        raise AssertionError('failed exporter published')
    require(blocked.published == 0 and len(delivered) == len(FIXTURES), 'failed export delivered')
    class Corrupt(EvidenceChecker):
        def obtain(self, source):
            graph, term, ty = malformed['wrong-proof-true-equality']
            return snapshot_bytes(s, graph=graph, term=term, ty=ty)
    invalid = Corrupt(exporter, checker)
    try:
        invalid.generate(b'ignored', consumer=delivered.append)
    except Unsupported:
        pass
    else:
        raise AssertionError('invalid evidence published')
    require(invalid.published == 0 and len(delivered) == len(FIXTURES), 'invalid evidence delivered')
    print(f'linear evidence: {len(cases)} real-Core.require cases, {rejected} rejections, '
          'exact retained-byte delivery and failed-export/validation gates')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean --run CheckLinearEvidence.lean')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-linear-evidence-') as folder:
        test(shlex.split(args.compiler), shlex.split(args.checker), Path(folder))


if __name__ == '__main__':
    main()
