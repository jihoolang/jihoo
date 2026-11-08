#!/usr/bin/env python3
"""Validate retained actual inference/normalization observations for one application."""
from __future__ import annotations
import argparse
from pathlib import Path
import shlex
import tempfile
from core_certificate_process import ROOT, command, success
from core_typing_producer import Snapshot, Unsupported, require
from core_typing_certificates import snapshot_bytes


class ApplicationChecker:
    def __init__(self, exporter, checker):
        self.exporter, self.checker = exporter, checker
        self.published = 0

    def obtain(self, source):
        return success(command([self.exporter, 'apply'], source))

    def validate(self, parts, roots):
        return command([*self.checker, *roots], b'\n'.join(parts), cwd=ROOT / 'proofs')

    def generate(self, source, *, consumer=None):
        retained = self.obtain(source)
        parts = retained.split(b'\n')
        require(len(parts) == 4, 'expected four retained snapshots')
        success(self.validate(parts, roots_of(parts)))
        if consumer:
            consumer(retained)
        self.published += 1
        return parts


def roots_of(parts):
    f, n, i, r = map(Snapshot.read, parts)
    return [f.term, f.type, n.type, i.term, i.type, r.type]


FIXTURES = {
    'identity-evidence': '(def value (Eq 7 7) (app (lam x U64 (refl x)) 7))',
    'normalized-function-type': '(def value (Eq 8 8) (app (lam x U64 (refl (uadd 1 x))) 7))',
    'expression-argument': '(def value (Eq 7 7) (app (lam x U64 (refl x)) (uadd 3 4)))',
    'zero-le': '(def value (Lt 0 8) (app (lam x U64 (zero-le x)) 7))',
    'wide-zero-le': '(def value (Lt 0 (uadd 18446744073709551615 1)) '
                    '(app (lam x U64 (zero-le x)) 18446744073709551615))',
    'wide-argument': '(def value (Lt 0 (uadd (uadd 18446744073709551615 1) 1)) '
                     '(app (lam x U64 (zero-le x)) (uadd 18446744073709551615 1)))',
    'partial-proof-function': '(def value (pi y U64 (Eq (uadd 3 y) (uadd y 3))) '
                              '(app (lam x U64 (lam y U64 (refl (uadd x y)))) 3))',
    'two-retained-binders': '(def value (pi y U64 (pi z U64 '
                            '(Eq (uadd 3 (uadd y z)) (uadd z (uadd y 3))))) '
                            '(app (lam x U64 (lam y U64 (lam z U64 '
                            '(refl (uadd x (uadd y z)))))) 3))',
    'unused-wide-argument': '(def value (Eq 5 5) '
                            '(app (lam x U64 (refl 5)) (uadd 18446744073709551615 1)))',
}
OUTSIDE = {
    'nested-function-application': '(def value (Eq 7 7) '
        '(app (app (lam x U64 (lam y U64 (refl (uadd x y)))) 3) 4))',
    'proof-argument': '(def value (Eq 1 1) (app (lam0 p (Eq 1 1) p) (refl 1)))',
    'subtraction-argument': '(def value (Eq 2 2) '
        '(app (lam x U64 (refl x)) (usub 3 1 (decide-lt 1 4))))',
}


def test(compiler, checker, output):
    exporter = output / 'snapshot'
    success(command([*compiler, 'build', '-O2', '-I', 'compiler', 'tests/core_typing_snapshots.jh',
                     '-o', exporter]))
    gate = ApplicationChecker(exporter, checker)
    cases, delivered = {}, []
    for name, source in FIXTURES.items():
        try:
            cases[name] = gate.generate(source.encode(), consumer=delivered.append)
        except Unsupported as error:
            raise Unsupported(f'{name}: {error}') from error
        require(delivered[-1] == b'\n'.join(cases[name]), 'retained artifact changed')
        snapshots = list(map(Snapshot.read, cases[name]))
        require(all(s.graph == snapshots[0].graph for s in snapshots), 'different frozen graphs')
        # Existing joint mode still returns the same real application roots.
        legacy = success(command([exporter, 'both'], source.encode())).split(b'\n')
        require(Snapshot.read(legacy[0]).term == snapshots[3].term and
                Snapshot.read(legacy[0]).type == snapshots[3].type and
                Snapshot.read(legacy[1]).type == snapshots[2].type, 'legacy inference roots changed')
    parts = cases['normalized-function-type']
    roots = roots_of(parts)
    f, n, i, r = map(Snapshot.read, parts)
    require(f.type != n.type and i.type != r.type, 'positive control must exercise both transformations')
    rejected = 0
    def reject(name, changed, selected=None):
        nonlocal rejected
        result = gate.validate(changed, roots if selected is None else selected)
        require(result.returncode == 1 and b'rejected' in result.stderr, f'{name}: {result}')
        rejected += 1
    for k in range(6):
        wrong = list(roots); wrong[k] += 1
        reject(f'wrong-root-{k}', parts, wrong)
    changed = list(parts)
    changed[2] = snapshot_bytes(i, ty=r.type)
    reject('convertible-but-not-exact-substitution', changed, roots_of(changed))
    changed = list(parts)
    changed[0] = snapshot_bytes(f, ty=n.type)
    reject('convertible-but-not-exact-function-inference', changed, roots_of(changed))
    changed = list(parts); changed[1] = cases['identity-evidence'][1]
    reject('other-valid-normalization-snapshot', changed)
    def shared(graph):
        return [snapshot_bytes(s, graph=graph) for s in [f, n, i, r]]
    graph = [*f.graph, (1, 0), (7, len(f.graph), len(f.graph)),
             (8, 0, f.graph.index((3,)), len(f.graph)+1)]
    changed = shared(graph)
    changed[1] = snapshot_bytes(n, graph=graph, ty=len(graph)-1)
    reject('false-normalization-observation', changed, roots_of(changed))
    # Hand-built backward-edge graph isolates the intended checks. Both
    # equivalent lambdas and both literal arguments precede the application.
    # The unchanged counterpart must pass the complete application validator.
    valid = [(3,), (0, 0), (13, 1), (9, 0, 0, 2), (9, 0, 0, 2),
             (1, 7), (1, 8), (7, 1, 1), (8, 0, 0, 7), (7, 5, 5), (10, 3, 5)]
    def valid_trace(graph, function=3, result=9):
        trace = [snapshot_bytes(f, graph=graph, term=function, ty=8),
                 snapshot_bytes(f, graph=graph, term=function, ty=8),
                 snapshot_bytes(f, graph=graph, term=10, ty=result),
                 snapshot_bytes(f, graph=graph, term=10, ty=result)]
        # Python explicitly checks every backward edge. Lean additionally
        # checks whole-graph validity/resources and the retained function type.
        for artifact in trace:
            Snapshot.read(artifact)
        success(command(['lake', 'env', 'lean', '--run', 'CheckCorePrincipal.lean', function, 8, 8],
                        trace[0] + b'\n' + trace[1], cwd=ROOT / 'proofs'))
        return trace
    control = valid_trace(valid)
    success(gate.validate(control, roots_of(control)))
    graph = list(valid); graph[10] = (10, 3, 6)
    changed = valid_trace(graph)
    reject('graph-valid-changed-argument-7-to-8', changed, roots_of(changed))
    # Changing the result consistently to Eq 8 8 restores acceptance.
    repaired = valid_trace([*graph, (7, 6, 6)], result=11)
    success(gate.validate(repaired, roots_of(repaired)))
    graph = list(valid); graph[10] = (10, 4, 5)
    changed = valid_trace(graph)
    reject('graph-valid-equivalent-distinct-function-id', changed, roots_of(changed))
    # Selecting that exact equivalent lambda restores acceptance, proving the
    # failure above is ID association rather than type or graph invalidity.
    repaired = valid_trace(graph, function=4)
    success(gate.validate(repaired, roots_of(repaired)))
    extended = shared([*f.graph, (18,)])
    success(gate.validate(extended, roots))
    extended[1] = snapshot_bytes(n, graph=[*f.graph, (19, 0)])
    reject('changed-unreachable-node', extended)
    changed = list(parts); changed[3] += b';'
    reject('trailing-artifact', changed)
    changed = list(parts); changed[0] = b'1' * 65 + b';'
    reject('oversized-token', changed)
    # All trees and the whole graph fit existing preflight limits. The unused
    # argument still triggers the conservative substitution-product guard.
    graph = [(3,), (1, 1), (1, 0)]
    large = 1
    for _ in range(7):
        graph.append((16, large, large)); large = len(graph)-1
    eq = len(graph); graph.append((7, large, large))
    proof = len(graph); graph.append((13, large))
    fn = len(graph); graph.append((9, 0, 0, proof))
    ft = len(graph); graph.append((8, 0, 0, eq))
    arg = 2
    for _ in range(4):
        graph.append((16, arg, arg)); arg = len(graph)-1
    application = len(graph); graph.append((10, fn, arg))
    ff = snapshot_bytes(f, graph=graph, term=fn, ty=ft)
    aa = snapshot_bytes(f, graph=graph, term=application, ty=eq)
    success(command(['lake', 'env', 'lean', '--run', 'CheckCorePrincipal.lean', fn, ft, ft],
                    ff + b'\n' + ff, cwd=ROOT / 'proofs'))
    reject('substitution-product-before-expansion', [ff, ff, aa, aa], [fn, ft, ft, application, eq, eq])
    for name, source in OUTSIDE.items():
        outside = success(command([exporter, 'apply'], source.encode())).split(b'\n')
        reject(f'actual-core-outside-{name}', outside, roots_of(outside))
    failed = output / 'failed-exporter'
    failed.write_bytes(b"#!/bin/sh\nprintf '%s' '" + b'\n'.join(parts) + b"'\nexit 1\n")
    failed.chmod(0o755)
    blocked = ApplicationChecker(failed, checker)
    try:
        blocked.generate(b'ignored', consumer=delivered.append)
    except Unsupported:
        pass
    else:
        raise AssertionError('failed exporter published')
    require(blocked.published == 0 and len(delivered) == len(cases), 'failed export delivered')
    class Corrupt(ApplicationChecker):
        def obtain(self, source):
            bad = list(parts); bad[2] = snapshot_bytes(i, ty=r.type)
            return b'\n'.join(bad)
    corrupt = Corrupt(exporter, checker)
    try:
        corrupt.generate(b'ignored', consumer=delivered.append)
    except Unsupported:
        pass
    else:
        raise AssertionError('invalid application published')
    require(corrupt.published == 0 and len(delivered) == len(cases), 'bad result delivered')
    print(f'first-order application: {len(cases)} actual-core traces, {rejected} rejections, '
          'legacy roots, substitution product guard and failed-publication gates')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean --run CheckFirstOrderApplication.lean')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-application-') as folder:
        test(shlex.split(args.compiler), shlex.split(args.checker), Path(folder))


if __name__ == '__main__':
    main()
