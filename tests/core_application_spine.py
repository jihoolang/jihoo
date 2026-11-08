#!/usr/bin/env python3
"""Retain and validate actual Core observations across a first-order application spine."""
from __future__ import annotations
import argparse
from pathlib import Path
import shlex
import tempfile
from core_certificate_process import ROOT, command, success
from core_typing_producer import Snapshot, Producer, Unsupported, require
from core_typing_certificates import snapshot_bytes
from core_first_order_application import FIXTURES as SINGLE, OUTSIDE


class SpineChecker:
    def __init__(self, exporter, checker):
        self.exporter, self.checker = exporter, checker
        self.published = 0
        self.reads = 0

    def obtain(self, source):
        self.reads += 1
        return success(command([self.exporter, 'spine'], source))

    def validate(self, parts, roots):
        return command([*self.checker, *roots], b'\n'.join(parts), cwd=ROOT / 'proofs')

    def generate(self, source, *, consumer=None):
        retained = self.obtain(source)
        parts = retained.split(b'\n')
        require(4 <= len(parts) <= 34 and len(parts) % 2 == 0, 'expected 1..16 retained pairs')
        success(self.validate(parts, roots_of(parts)))
        if consumer:
            consumer(retained)
        self.published += 1
        return parts


def roots_of(parts):
    snapshots = list(map(Snapshot.read, parts))
    initial, final, requested = snapshots[0], snapshots[-2], snapshots[-1]
    return [initial.term, initial.type, final.term, final.type, requested.type]


def constant_spine(count):
    term = '(refl 5)'
    for i in range(count):
        term = f'(lam x{i} U64 {term})'
    for _ in range(count):
        term = f'(app {term} 0)'
    return f'(def value (Eq 5 5) {term})'


FIXTURES = {
    **SINGLE,
    'curried-two': OUTSIDE['nested-function-application'],
    'curried-three': '(def value (Eq 9 9) '
        '(app (app (app (lam x U64 (lam y U64 (lam z U64 '
        '(refl (uadd x (uadd y z)))))) 2) 3) 4))',
    'remaining-dependent-binder': '(def value (pi z U64 (Eq (uadd z 7) (uadd 7 z))) '
        '(app (app (lam x U64 (lam y U64 (lam z U64 '
        '(refl (uadd x (uadd y z)))))) 3) 4))',
    'curried-expression-arguments': '(def value (Eq 10 10) '
        '(app (app (lam x U64 (lam y U64 (refl (uadd x y)))) (uadd 1 2)) (uadd 3 4)))',
    'curried-wide-zero-le': '(def value (Lt 0 (uadd (uadd 18446744073709551615 1) 1)) '
        '(app (app (lam x U64 (lam y U64 (zero-le (uadd x y)))) 18446744073709551615) 1))',
    'sixteen-links': constant_spine(16),
}


def test(compiler, checker, output, existing_exporter=None):
    exporter = existing_exporter or output / 'snapshot'
    if existing_exporter is None:
        success(command([*compiler, 'build', '-O2', '-I', 'compiler', 'tests/core_typing_snapshots.jh',
                         '-o', exporter]))
    gate = SpineChecker(exporter, checker)
    cases, delivered = {}, []
    for name, source in FIXTURES.items():
        try:
            cases[name] = gate.generate(source.encode(), consumer=delivered.append)
        except Unsupported as error:
            raise Unsupported(f'{name}: {error}') from error
        require(gate.reads == gate.published == len(cases), 'source/export must be consumed once')
        require(delivered[-1] == b'\n'.join(cases[name]), 'retained bytes changed before publication')
        snapshots = list(map(Snapshot.read, cases[name]))
        require(all(s.graph == snapshots[0].graph for s in snapshots), 'different frozen graphs')
        legacy = success(command([exporter, 'both'], source.encode())).split(b'\n')
        require(Snapshot.read(legacy[0]).term == snapshots[-1].term and
                Snapshot.read(legacy[0]).type == snapshots[-1].type and
                Snapshot.read(legacy[1]).graph == snapshots[0].graph[:len(Snapshot.read(legacy[1]).graph)] and
                Producer(Snapshot.read(legacy[1])).term(Snapshot.read(legacy[1]).type) ==
                Producer(snapshots[-2]).term(snapshots[-2].type), 'legacy inference observation changed')
        if name in SINGLE:
            single = success(command([exporter, 'apply'], source.encode())).split(b'\n')
            old = list(map(Snapshot.read, single))
            require([(s.term, Producer(s).term(s.type)) for s in old] ==
                    [(s.term, Producer(s).term(s.type)) for s in snapshots],
                    'single-link inference meaning changed')
    parts = cases['curried-two']
    roots = roots_of(parts)
    rejected = 0
    def reject(name, changed, selected=None):
        nonlocal rejected
        result = gate.validate(changed, roots if selected is None else selected)
        require(result.returncode == 1 and b'rejected' in result.stderr, f'{name}: {result}')
        rejected += 1
    for k in range(5):
        wrong = list(roots); wrong[k] += 1
        reject(f'wrong-root-{k}', parts, wrong)
    reject('reordered-links', [parts[0], *parts[3:5], *parts[1:3], parts[5]])
    reject('skipped-first-link', [parts[0], *parts[3:]])
    reject('replayed-link', [*parts[:3], *parts[1:3], *parts[3:]])
    reject('no-links', [parts[0], parts[-1]])
    reject('seventeen-links', [cases['sixteen-links'][0], *cases['sixteen-links'][1:3],
                               *cases['sixteen-links'][1:]], roots_of(cases['sixteen-links']))
    reject('odd-snapshot-count', parts[:-1])
    changed = list(parts); changed[2] = cases['curried-three'][2]
    reject('different-valid-intermediate', changed)
    for at in range(1, len(parts)-1, 2):
        changed = list(parts)
        normal = Snapshot.read(changed[at])
        changed[at] = snapshot_bytes(normal, term=roots[2])
        reject(f'wrong-normalized-term-root-{at}', changed)
    changed = list(parts); changed[0] += b';'
    reject('trailing-token', changed)
    changed = list(parts); changed[0] = b'1' * 65 + b';'
    reject('oversized-token', changed)
    snapshots = list(map(Snapshot.read, parts))
    extended = [snapshot_bytes(s, graph=[*s.graph, (18,)]) for s in snapshots]
    success(gate.validate(extended, roots))
    extended[3] = snapshot_bytes(snapshots[3], graph=[*snapshots[3].graph, (19, 0)])
    reject('changed-unreachable-node', extended)

    # Every reference is backward. Equivalent intermediate applications and
    # arguments exist before the final App, so failures isolate association and
    # substitution rather than malformed graphs. Repaired controls must pass.
    graph = []
    def node(*fields):
        graph.append(fields)
        return len(graph)-1
    u = node(3); x = node(0, 1); y = node(0, 0); total = node(16, x, y)
    proof = node(13, total); inner = node(9, 0, u, proof); fn = node(9, 0, u, inner)
    three = node(1, 3); four = node(1, 4); five = node(1, 5)
    eq = node(7, total, total); pi = node(8, 0, u, eq); ft = node(8, 0, u, pi)
    partial_sum = node(16, three, y); partial_eq = node(7, partial_sum, partial_sum)
    partial_type = node(8, 0, u, partial_eq)
    partial = node(10, fn, three); duplicate = node(10, fn, three)
    full_sum = node(16, three, four); full_type = node(7, full_sum, full_sum)
    other_sum = node(16, three, five); other_type = node(7, other_sum, other_sum)
    final = node(10, partial, four)
    template = snapshots[0]
    def handmade(arena, intermediate=partial, result=full_type):
        bindings = [(fn, ft), (fn, ft), (intermediate, partial_type),
                    (intermediate, partial_type), (final, result), (final, result)]
        artifacts = [snapshot_bytes(template, graph=arena, term=t, ty=a) for t, a in bindings]
        for artifact in artifacts:
            Snapshot.read(artifact)
        return artifacts
    control = handmade(graph)
    success(gate.validate(control, roots_of(control)))
    changed = list(control)
    changed[3] = snapshot_bytes(template, graph=graph, term=partial, ty=ft)
    reject('well-formed-wrong-intermediate-normal-type', changed, roots_of(changed))
    changed = handmade(graph, intermediate=duplicate)
    reject('equivalent-distinct-intermediate-id', changed, roots_of(changed))
    repaired_graph = list(graph); repaired_graph[final] = (10, duplicate, four)
    repaired = handmade(repaired_graph, intermediate=duplicate)
    success(gate.validate(repaired, roots_of(repaired)))
    changed_graph = list(graph); changed_graph[final] = (10, partial, five)
    changed = handmade(changed_graph)
    reject('graph-valid-changed-final-argument', changed, roots_of(changed))
    repaired = handmade(changed_graph, result=other_type)
    success(gate.validate(repaired, roots_of(repaired)))
    changed = handmade(graph)
    changed[-1] = snapshot_bytes(template, graph=graph, term=final, ty=other_type)
    reject('substituted-well-formed-requested-type', changed, roots_of(changed))
    # Substitution, not mere conversion: actual Core's declared Eq 8 8 is
    # convertible to its inferred Eq (1+7) (1+7), but cannot replace that output.
    changed = list(cases['normalized-function-type'])
    inferred, requested = map(Snapshot.read, changed[-2:])
    require(inferred.type != requested.type, 'distinct type roots required')
    changed[-2] = snapshot_bytes(inferred, ty=requested.type)
    reject('convertible-non-substitution-output', changed, roots_of(changed))

    # Shared DAGs expand into repeated references. Each of eight substitutions
    # passes in isolation; seven accumulated links pass and eight exceed 32768.
    graph = []
    u = node(3); variable = node(0, 0); summed = variable
    for _ in range(6):
        summed = node(16, summed, summed)
    eq = node(7, summed, summed); proof = node(13, summed)
    types, functions = [eq], [proof]
    for _ in range(12):
        types.append(node(8, 0, u, types[-1]))
        functions.append(node(9, 0, u, functions[-1]))
    arg = node(1, 0)
    for _ in range(3):
        arg = node(16, arg, arg)
    apps = [functions[12]]
    for _ in range(8):
        apps.append(node(10, apps[-1], arg))
    singles = [node(10, functions[12-k], arg) for k in range(8)]
    def artifact(term, ty):
        result = snapshot_bytes(template, graph=graph, term=term, ty=ty)
        Snapshot.read(result)
        return result
    def budget_trace(count):
        result = [artifact(apps[0], types[12])]
        for k in range(count):
            result.extend([artifact(apps[k], types[12-k]), artifact(apps[k+1], types[11-k])])
        result.append(artifact(apps[count], types[12-count]))
        return result
    for k, app in enumerate(singles):
        seed = artifact(functions[12-k], types[12-k])
        out = artifact(app, types[11-k])
        single = [seed, seed, out, out]
        success(gate.validate(single, roots_of(single)))
    short = budget_trace(7)
    success(gate.validate(short, roots_of(short)))
    excessive = budget_trace(8)
    reject('cumulative-repeated-reference-substitution-budget', excessive, roots_of(excessive))
    unsupported = {**OUTSIDE, 'higher-order-argument':
        '(def value (Eq 7 7) (app (lam0 f (pi x U64 (Eq x x)) (app f 7)) '
        '(lam x U64 (refl x))))'}
    for name, source in unsupported.items():
        if name == 'nested-function-application':
            continue
        outside = success(command([exporter, 'spine'], source.encode())).split(b'\n')
        reject(f'actual-core-outside-{name}', outside, roots_of(outside))
    too_long = command([exporter, 'spine'], constant_spine(17).encode())
    require(too_long.returncode != 0 and not too_long.stdout and b'16 links' in too_long.stderr,
            'exporter must fail closed at link limit')
    invalid_source = command([exporter, 'spine'], b'(def value (Eq 1 2) (refl 1))')
    require(invalid_source.returncode != 0 and not invalid_source.stdout, 'invalid Core was exported')

    # Valid bytes with failed process exit still must not reach the consumer,
    # including under Python -O. Failed validation is likewise never published.
    failed = output / 'failed-exporter'
    failed.write_bytes(b"#!/bin/sh\nprintf '%s' '" + b'\n'.join(parts) + b"'\nexit 1\n")
    failed.chmod(0o755)
    class Corrupt(SpineChecker):
        def obtain(self, source):
            return b'\n'.join(excessive)
    for blocked in [SpineChecker(failed, checker), Corrupt(exporter, checker)]:
        try:
            blocked.generate(b'ignored', consumer=delivered.append)
        except Unsupported:
            pass
        else:
            raise AssertionError('failed operation published')
        require(blocked.published == 0 and len(delivered) == len(cases), 'failed operation delivered')
    print(f'application spine: {len(cases)} actual-Core traces, {rejected} rejections, '
          'graph-valid repaired controls, cumulative budget, read-once and publication gates')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean --run CheckApplicationSpine.lean')
    parser.add_argument('--exporter', type=Path, help='reuse an already-built current-checkout exporter')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-spine-') as folder:
        test(shlex.split(args.compiler), shlex.split(args.checker), Path(folder), args.exporter)


if __name__ == '__main__':
    main()
