#!/usr/bin/env python3
"""Validate exact actual Core.infer types alongside requested proof types.

The pair is frozen once in a common post-require graph. Execution and export
fidelity are tested boundaries, not a proof of compiler/core.jh itself.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import shlex
import tempfile

from core_certificate_process import ROOT, command, success
from core_typing_producer import Snapshot, Unsupported, require
from core_typing_certificates import snapshot_bytes
from core_linear_evidence import FIXTURES, OUTSIDE


class PrincipalChecker:
    def __init__(self, exporter, checker):
        self.exporter, self.checker = exporter, checker
        self.published = 0

    def obtain(self, source):
        return success(command([self.exporter, 'both'], source))

    def validate(self, requested, inferred, term, req, inf):
        return command([*self.checker, term, req, inf], requested + b'\n' + inferred, cwd=ROOT / 'proofs')

    def generate(self, source, *, consumer=None):
        retained = self.obtain(source)
        parts = retained.split(b'\n')
        require(len(parts) == 2, 'expected exactly two retained snapshots')
        requested, inferred = parts
        r, i = Snapshot.read(requested), Snapshot.read(inferred)
        success(self.validate(requested, inferred, r.term, r.type, i.type))
        if consumer:
            consumer(retained)
        self.published += 1
        return requested, inferred


def test(compiler, checker, output):
    exporter = output / 'snapshot'
    success(command([*compiler, 'build', '-O2', '-I', 'compiler', 'tests/core_typing_snapshots.jh',
                     '-o', exporter]))
    gate = PrincipalChecker(exporter, checker)
    cases, delivered = {}, []
    for name, source in FIXTURES.items():
        try:
            cases[name] = gate.generate(source.encode(), consumer=delivered.append)
        except Unsupported as error:
            raise Unsupported(f'{name}: {error}') from error
        require(delivered[-1] == b'\n'.join(cases[name]), 'retained pair changed before publication')
        r, i = map(Snapshot.read, cases[name])
        require(r.graph == i.graph and r.term == i.term, 'exporter did not freeze a common graph')
        # The existing require mode must remain byte-for-byte compatible.
        require(cases[name][0] == success(command([exporter, 'require'], source.encode())),
                'legacy require output changed')
        old_infer = Snapshot.read(success(command([exporter, 'infer'], source.encode())))
        require(old_infer.graph[old_infer.type] == i.graph[i.type], 'legacy inferred root changed')
    rb, ib = cases['closed-add-equality']
    r, i = Snapshot.read(rb), Snapshot.read(ib)
    require(r.type != i.type, 'positive control requires a distinct declared type')
    rejected = 0

    def reject(name, requested, inferred, term=None, req=None, inf=None):
        nonlocal rejected
        result = gate.validate(requested, inferred, r.term if term is None else term,
                               r.type if req is None else req, i.type if inf is None else inf)
        require(result.returncode == 1 and b'rejected' in result.stderr, f'{name}: {result}')
        rejected += 1

    # Both types are semantically equivalent, but actual infer(refl 5) must be
    # Eq 5 5; treating the declared Eq (2+3) 5 as inferred is not correspondence.
    convertible = snapshot_bytes(i, ty=r.type)
    reject('convertible-but-wrong-principal', rb, convertible, inf=r.type)
    other_r, other_i = cases['zero']
    reject('other-valid-inference', rb, other_i)
    reject('other-valid-request', other_r, ib)
    reject('swapped-artifact-roles', ib, rb)
    reject('wrong-requested-root', rb, ib, req=i.type)
    reject('wrong-inferred-root', rb, ib, inf=r.type)
    reject('wrong-term-root', rb, ib, term=r.type)
    extra = [*i.graph, i.graph[i.type]]
    reject('distinct-equivalent-inferred-root', rb, snapshot_bytes(i, graph=extra, ty=len(i.graph)))
    # Both records include an extra unreachable valid node. Its exact identity
    # must agree, even though it cannot affect either selected type's meaning.
    extra_r = snapshot_bytes(r, graph=[*r.graph, (18,)])
    extra_i = snapshot_bytes(i, graph=[*i.graph, (18,)])
    success(gate.validate(extra_r, extra_i, r.term, r.type, i.type))
    changed_i = snapshot_bytes(i, graph=[*i.graph, (19, 0)])
    reject('changed-unreachable-node', extra_r, changed_i)
    reject('trailing-data', rb, ib + b';')
    reject('excessive-token', rb, b'1' * 65 + b';')
    # General semantic evidence previously admits this true mathematical claim,
    # but actual Decide requires normalized Natural nodes, each below 2^64.
    wide_source = ('(def value (Lt 0 (uadd 18446744073709551615 1)) '
                   '(decide-lt 0 (uadd 18446744073709551615 1)))').encode()
    actual = command([exporter, 'both'], wide_source)
    require(actual.returncode == 1 and b'decide-lt needs a true closed inequality' in actual.stderr,
            f'wide Decide must fail for the intended reason: {actual}')
    graph = [(1, 0), (1, 18446744073709551615), (1, 1), (16, 1, 2), (15, 0, 3), (6, 0, 3)]
    wide = snapshot_bytes(r, graph=graph, term=4, ty=5)
    success(command(['lake', 'env', 'lean', '--run', 'CheckLinearEvidence.lean', 4, 5], wide,
                    cwd=ROOT / 'proofs'))
    reject('semantic-wide-decision-not-core-compatible', wide, wide, term=4, req=5, inf=5)
    # Invalid evidence cannot be rescued by pairing it with a true proposition.
    graph = [(1, 0), (1, 1), (13, 0), (6, 0, 1)]
    wrong = snapshot_bytes(r, graph=graph, term=2, ty=3)
    reject('true-claim-wrong-proof', wrong, wrong, term=2, req=3, inf=3)
    graph = [(1, 0)]
    for _ in range(14):
        graph.append((16, len(graph)-1, len(graph)-1))
    value = len(graph)-1
    graph += [(13, value), (7, value, value)]
    shared = snapshot_bytes(r, graph=graph, term=value+1, ty=value+2)
    reject('shared-expansion-budget', shared, shared, term=value+1, req=value+2, inf=value+2)
    for name, source in OUTSIDE.items():
        a, b = success(command([exporter, 'both'], source.encode())).split(b'\n')
        ar, bi = Snapshot.read(a), Snapshot.read(b)
        reject(f'actual-core-outside-{name}', a, b, term=ar.term, req=ar.type, inf=bi.type)
    failed = output / 'failed-exporter'
    valid_pair = rb + b'\n' + ib
    failed.write_bytes(b"#!/bin/sh\nprintf '%s' '" + valid_pair + b"'\nexit 1\n")
    failed.chmod(0o755)
    blocked = PrincipalChecker(failed, checker)
    try:
        blocked.generate(b'ignored', consumer=delivered.append)
    except Unsupported:
        pass
    else:
        raise AssertionError('nonzero exporter published')
    require(blocked.published == 0 and len(delivered) == len(FIXTURES), 'failed export delivered')
    class Corrupt(PrincipalChecker):
        def obtain(self, source):
            return rb + b'\n' + convertible
    corrupt = Corrupt(exporter, checker)
    try:
        corrupt.generate(b'ignored', consumer=delivered.append)
    except Unsupported:
        pass
    else:
        raise AssertionError('incorrect inferred type published')
    require(corrupt.published == 0 and len(delivered) == len(FIXTURES), 'invalid inference delivered')
    print(f'core principal: {len(cases)} actual infer/require pairs, {rejected} rejections, '
          'legacy modes, wide-Decide diagnostic, failed-export/validation publication gates')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean --run CheckCorePrincipal.lean')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-core-principal-') as folder:
        test(shlex.split(args.compiler), shlex.split(args.checker), Path(folder))


if __name__ == '__main__':
    main()
