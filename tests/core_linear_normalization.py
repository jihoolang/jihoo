#!/usr/bin/env python3
"""Per-run ghost symbolic-sum validation, not compiler/runtime refinement.

The once-retained input is admitted before invoking the actual core driver;
only the independently validated exact output is passed to a consumer.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import shlex
import sys
import tempfile

from core_certificate_process import ROOT, command, success
from core_typing_producer import Snapshot, Unsupported, require
from core_typing_certificates import snapshot_bytes
from core_checked_normalization import record_bytes


class LinearNormalizer:
    def __init__(self, driver, checker):
        self.driver, self.checker = driver, checker
        self.invoked = self.published = 0

    def gate(self, before, arity, depth=128, fuel=64):
        return command([*self.checker, '--input', arity, depth, fuel], before, cwd=ROOT / 'proofs')

    def validate(self, before, after, record, arity, depth=128, fuel=64):
        return command([*self.checker, arity, depth, fuel], b'\n'.join([before, after, record]),
                       cwd=ROOT / 'proofs')

    def consume(self, before, depth, fuel):
        self.invoked += 1
        return success(command([self.driver, '--normal', depth, fuel], before)).split(b'\n')

    def generate(self, before, arity, *, depth=128, fuel=64, consumer=None):
        success(self.gate(before, arity, depth, fuel))
        after, record = self.consume(before, depth, fuel)
        success(self.validate(before, after, record, arity, depth, fuel))
        if consumer:
            consumer(b'\n'.join([before, after, record]))
        self.published += 1
        return after, record


FIXTURES = {
    'constant': ('7', 0),
    'fold': ('(uadd 3 4)', 0),
    'variable': ('x', 1),
    'zero': ('(uadd x 0)', 1),
    'reorder': ('(uadd 1 x)', 1),
    'association': ('(uadd (uadd 2 x) (uadd 3 y))', 2),
    'multiplicity': ('(uadd (uadd x y) (uadd x x))', 2),
    'wide': ('(uadd 18446744073709551615 1)', 0),
    'wide-symbolic': ('(uadd (uadd 18446744073709551615 x) (uadd 1 x))', 1),
}


def test(compiler, checker, output):
    exporter, driver = output / 'snapshot', output / 'normal'
    for source, binary in [('core_typing_snapshots.jh', exporter), ('core_typed_beta_replay.jh', driver)]:
        success(command([*compiler, 'build', '-O2', '-I', 'compiler', f'tests/{source}', '-o', binary]))
    normalizer = LinearNormalizer(driver, checker)
    cases = {}
    for name, (body, arity) in FIXTURES.items():
        ty = 'U64'
        for variable in reversed(['x', 'y'][:arity]):
            body, ty = f'(lam {variable} U64 {body})', f'(pi {variable} U64 {ty})'
        exported = success(command([exporter, 'require'], f'(def value {ty} {body})'.encode()))
        snapshot = Snapshot.read(exported)
        root = snapshot.term
        # Test adapter selects the open body and its scalar type, retaining the
        # complete actual graph. The theorem begins at these supplied roots.
        for _ in range(arity):
            require(snapshot.graph[root][:2] == (9, 0), 'expected non-erased lambda')
            root = snapshot.graph[root][3]
        scalar = snapshot.graph.index((3,))
        before = snapshot_bytes(snapshot, term=root, ty=scalar)
        after, record = normalizer.generate(before, arity)
        cases[name] = before, after, record, arity
    b, a, r, n = cases['reorder']
    require(Snapshot.read(a).term != Snapshot.read(b).term, 'positive control must really reorder')
    rejected = 0

    def reject(name, before, after, record, arity=n, depth=128, fuel=64):
        nonlocal rejected
        result = normalizer.validate(before, after, record, arity, depth, fuel)
        require(result.returncode == 1 and b'rejected' in result.stderr, f'{name}: {result}')
        rejected += 1

    reject('wrong-depth', b, a, r, depth=127)
    reject('wrong-fuel', b, a, r, fuel=63)
    reject('out-of-scope', b, a, r, arity=0)
    reject('excessive-arity', b, a, r, arity=129)
    reject('other-input', cases['variable'][0], a, r)
    reject('other-output', b, cases['variable'][1], r)
    reject('trailing-record', b, a, r + b';')
    sa, sb = Snapshot.read(a), Snapshot.read(b)
    dup = snapshot_bytes(sa, graph=[*sa.graph, sa.graph[sa.term]], term=len(sa.graph))
    reject('equivalent-distinct-root', b, dup, r)
    tydup = snapshot_bytes(sa, graph=[*sa.graph, (3,)], ty=len(sa.graph))
    reject('distinct-type-root-even-with-record', b, tydup, record_bytes(b, tydup))
    for name, extra in [('wrong-constant', [(1, 2), (16, sb.term, len(sa.graph))]),
                        ('wrong-coefficient', [(16, sa.term, sa.term)])]:
        changed = snapshot_bytes(sa, graph=[*sa.graph, *extra], term=len(sa.graph) + len(extra) - 1)
        reject(name, b, changed, record_bytes(b, changed))
    extended = snapshot_bytes(sb, graph=[*sb.graph, (18,)])
    ext_after, _ = normalizer.generate(extended, n)
    se = Snapshot.read(ext_after)
    graph = list(se.graph)
    graph[len(sb.graph)] = (19, 0)
    changed = snapshot_bytes(se, graph=graph)
    reject('changed-unreachable-prefix', extended, changed, record_bytes(extended, changed))
    # This is semantic validation, not directed-step replay or normality.
    success(normalizer.validate(b, b, record_bytes(b, b), n))
    invalid = [
        ('out-of-scope', snapshot_bytes(sb, graph=[(3,), (0, 1)], term=1, ty=0)),
        ('unsupported-subtraction', snapshot_bytes(sb, graph=[(3,), (1, 1), (15, 1, 1),
                                                             (17, 1, 1, 2)], term=3, ty=0)),
        ('wrong-type', snapshot_bytes(sb, graph=[(4,), (1, 1)], term=1, ty=0)),
        ('oversized-token', b'1' * 65 + b';'),
    ]
    graph = [(3,), (0, 0)]
    for _ in range(14):
        graph.append((16, len(graph) - 1, len(graph) - 1))
    invalid.append(('shared-expansion', snapshot_bytes(sb, graph=graph, term=len(graph)-1, ty=0)))
    for name, before in invalid:
        old = normalizer.invoked, normalizer.published
        try:
            normalizer.generate(before, n, consumer=lambda _: (_ for _ in ()).throw(RuntimeError('published')))
        except Unsupported:
            pass
        else:
            raise AssertionError(f'{name} admitted')
        require(old == (normalizer.invoked, normalizer.published), f'{name}: invoked downstream')
    # A real Core failure after successful admission also blocks publication.
    success(normalizer.gate(b, n, depth=1))
    old = normalizer.published
    try:
        normalizer.generate(b, n, depth=1)
    except Unsupported:
        pass
    else:
        raise AssertionError('actual depth-exhausted Core accepted')
    require(normalizer.published == old, 'actual Core failure published')
    # Even semantically plausible output is not published on a failed driver.
    failed = output / 'failed-driver'
    failed.write_text('#!/bin/sh\nprintf "plausible output"\nexit 1\n')
    failed.chmod(0o755)
    broken = LinearNormalizer(failed, checker)
    try:
        broken.generate(b, n)
    except Unsupported:
        pass
    else:
        raise AssertionError('nonzero driver accepted')
    require(broken.published == 0, 'failed driver published')
    class Corrupt(LinearNormalizer):
        def consume(self, before, depth, fuel):
            self.invoked += 1
            return cases['variable'][1], r
    corrupt = Corrupt(driver, checker)
    try:
        corrupt.generate(b, n, consumer=lambda _: (_ for _ in ()).throw(RuntimeError('published')))
    except Unsupported:
        pass
    else:
        raise AssertionError('invalid output published')
    require(corrupt.invoked == 1 and corrupt.published == 0, 'bad output reached consumer')
    print(f'linear Core.normal: {len(cases)} real-core cases, {rejected} tamper rejections, '
          f'{len(invalid)} preflight rejections, failed-driver/output gates')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean --run CheckLinearNormal.lean')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-linear-normal-') as folder:
        test(shlex.split(args.compiler), shlex.split(args.checker), Path(folder))


if __name__ == '__main__':
    main()
