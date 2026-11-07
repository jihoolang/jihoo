#!/usr/bin/env python3
"""Generate finite head beta witnesses with actual Core.substitute snapshots.

Untrusted, fuel-bounded orchestration; every prefix is checked before reuse, and
final normality/literal truth is checked before publication. No all-term
normalization, exporter fidelity or runtime/Core.normal equivalence is claimed.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import shlex
import sys
import subprocess
import tempfile

from core_typing_producer import Snapshot, Unsupported, CHILD_START, encode_numbers, produce, require
from core_certificate_process import ROOT, command, success
from core_typing_certificates import snapshot_bytes
from core_typed_beta_replay import replay_bytes

STEP_LIMIT, NODE_LIMIT, WORK_LIMIT = 64, 32768, 2000000


def measured(snapshot):
    stats = []
    for node in snapshot.graph:
        refs = node[1:] if node[0] == 11 else node[CHILD_START[node[0]]:] if node[0] in CHILD_START else ()
        size = 1 + sum(stats[k][0] for k in refs)
        depth = 1 + max((stats[k][1] for k in refs), default=0)
        require(size <= 200000 and depth <= 128, 'graph expansion/depth limit')
        stats.append((size, depth))
    return stats


def head_request(snapshot):
    """Walk graph IDs without unfolding. Guard the selected substitution first."""
    stats = measured(snapshot)
    path, root = [], snapshot.term
    while snapshot.graph[root][0] == 10:
        _, function, argument = snapshot.graph[root]
        f = snapshot.graph[function]
        if f[0] == 9:
            body = f[3]
            require(stats[body][0] * (stats[argument][0] + 1) <= 200000 and
                    stats[body][1] + stats[argument][1] <= 128, 'substitution work limit')
            return path
        path.append(0)
        root = function
    return None


def charge(s):
    stats = measured(s)
    return len(s.graph), 4 * (stats[s.term][0] + stats[s.type][0])


def chain_bytes(records):
    return encode_numbers([5, len(records)]) + b''.join(records)


class Normalizer:
    def __init__(self, driver, checker):
        self.driver, self.checker = driver, checker
        self.invoked = self.published = 0

    def validate(self, before, after, typing, records, *args):
        return command([*self.checker, *args],
            b'\n'.join([before, after, typing, chain_bytes(records)]), cwd=ROOT / 'proofs')

    def consume(self, retained, path):
        self.invoked += 1
        return success(command([self.driver, *map(str, path)], retained)).split(b'\n')

    def generate(self, before, typing, *, fuel=STEP_LIMIT, claim=(), consumer=None):
        require(0 <= fuel <= STEP_LIMIT, 'fuel range')
        # The exact immutable bytes are used throughout; no path is re-read.
        success(command(['lake', 'env', 'lean', '--run', 'CheckTyping.lean', '--snapshot'],
                        before + b'\n' + typing, cwd=ROOT / 'proofs'))
        initial = Snapshot.read(before)
        current, records = before, []
        initial_nodes, initial_work = charge(initial)
        used_nodes = used_work = 0
        while True:
            s = Snapshot.read(current)
            nodes, work = charge(s)
            require(initial_nodes + nodes + used_nodes <= NODE_LIMIT and
                    initial_work + work + used_work <= WORK_LIMIT, 'aggregate witness budget')
            path = head_request(s)
            if path is None:
                success(self.validate(before, current, typing, records, *claim))
                if consumer:
                    consumer(current)
                self.published += 1
                return current, records
            require(len(records) < fuel, 'head-normalization fuel exhausted')
            after, record = self.consume(current, path)
            candidate = Snapshot.read(after)
            next_nodes, next_work = charge(candidate)
            used_nodes += nodes + next_nodes
            used_work += work + next_work
            require(initial_nodes + next_nodes + used_nodes <= NODE_LIMIT and
                    initial_work + next_work + used_work <= WORK_LIMIT, 'aggregate witness budget')
            # Verify the whole prefix from the original typed input BEFORE
            # passing this candidate graph to another Core invocation.
            success(self.validate(before, after, typing, [*records, record], '--prefix'))
            current, records = after, [*records, record]


FIXTURES = {
    'zero-step': ('(def value (Eq 7 7) (refl 7))', ['eq', '7', '7'], 0),
    'lambda-body': ('(def value (pi n U64 (Eq n n)) '
        '(lam n U64 (app (lam m U64 (refl m)) n)))', [], 0),
    'one-step': ('(def value (Eq 7 7) (app (lam x U64 (refl x)) 7))', ['eq', '7', '7'], 1),
    'higher-order': ('(def value (Eq 7 7) '
        '(app (lam f (pi x U64 U64) (refl (app f 7))) (lam x U64 x)))', ['eq', '7', '7'], 1),
    'function-spine': ('(def value (Eq 7 7) '
        '(app (app (lam0 f (pi x U64 (Eq x x)) f) (lam x U64 (refl x))) 7))', ['eq', '7', '7'], 2),
    'bound': ('(def value (Lt 1 2) '
        '(app (lam0 p (Lt 1 2) p) (app (lam0 q (Lt 1 2) q) (decide-lt 1 2))))', ['lt', '1', '2'], 2),
    'scalar': ('(def value U64 (app (lam x U64 x) (app (lam y U64 y) 7)))', [], 2),
}


def test(compiler, checker, output):
    output.mkdir(parents=True, exist_ok=True)
    exporter, driver = output / 'snapshot', output / 'replay'
    for source, binary in [('core_typing_snapshots.jh', exporter), ('core_typed_beta_replay.jh', driver)]:
        success(command([*compiler, 'build', '-O2', '-I', 'compiler', f'tests/{source}', '-o', binary]))
    normalizer = Normalizer(driver, checker)
    cases = {}
    for name, (source, claim, count) in FIXTURES.items():
        before = success(command([exporter, 'require'], source.encode()))
        typing = produce(before)
        after, records = normalizer.generate(before, typing, claim=claim)
        assert len(records) == count, (name, len(records))
        cases[name] = before, after, typing, records, claim
    zero = cases['zero-step']
    normalizer.generate(zero[0], zero[2], fuel=0, claim=zero[4])
    rejected = 0

    def reject(name, before, after, typing, records, *args):
        nonlocal rejected
        result = normalizer.validate(before, after, typing, records, *args)
        assert result.returncode == 1 and b'rejected' in result.stderr, (name, result)
        rejected += 1

    b, a, t, rs, q = cases['function-spine']
    reject('unfinished-empty', b, b, t, [])
    # A valid typed prefix is not a completed normalization certificate.
    middle, _ = success(command([driver, '0'], b)).split(b'\n')
    success(normalizer.validate(b, middle, t, rs[:1], '--prefix'))
    reject('unfinished-prefix', b, middle, t, rs[:1])
    reject('beta-convertible-nonstep', b, b, t, [replay_bytes(b, b, [0])], '--prefix')
    reject('two-steps-as-one', b, a, t, [replay_bytes(b, a, [0])], '--prefix')
    reject('missing-step', b, a, t, rs[1:])
    reject('reordered', b, a, t, list(reversed(rs)))
    reject('duplicate-step', b, a, t, [rs[0], *rs])
    reject('wrong-final-snapshot', b, b, t, rs)
    other = cases['bound']
    reject('other-valid-input', other[0], a, t, rs)
    reject('other-valid-typing', b, a, other[2], rs)
    reject('wrong-true-claim', b, a, t, rs, 'eq', '8', '8')
    reject('false-equality', b, a, t, rs, 'eq', '7', '8')
    reject('false-bound', b, a, t, rs, 'lt', '1', '1')
    # Change a valid but unreachable node in an intermediate retained graph.
    sm = Snapshot.read(middle)
    changed = snapshot_bytes(sm, graph=[*sm.graph, (18,)])
    reject('broken-whole-graph-link', b, a, t,
           [replay_bytes(b, changed, [0]), *rs[1:]])
    out = Snapshot.read(a)
    dup = snapshot_bytes(out, graph=[*out.graph, out.graph[out.term]], term=len(out.graph))
    reject('equivalent-final-root-id', b, dup, t, rs)
    tydup = snapshot_bytes(out, graph=[*out.graph, out.graph[out.type]], ty=len(out.graph))
    reject('equivalent-final-type-id', b, tydup, t, rs)
    reject('changed-type-id-in-record', b, tydup, t, [rs[0], replay_bytes(middle, tydup, [])])
    # A real valid beta step in an argument violates the independent head policy.
    sb, _, st, _, _ = cases['scalar']
    arg_after, arg_record = success(command([driver, '1'], sb)).split(b'\n')
    reject('non-head-beta-step', sb, arg_after, st, [arg_record], '--prefix')
    reject('path-limit', b, a, t, [replay_bytes(b, a, [0] * 129)])
    reject('too-many-steps', b, a, t, rs * 33)
    reject('noncanonical-record', b, a, t, [rs[0] + b';', *rs[1:]])
    reject('excessive-token', b, a, t, [b'1' * 65 + b';' + rs[0]])
    # Valid snapshots repeated within the step limit exceed total serialized nodes.
    large_graph = [*out.graph, *([(18,)] * (4096-len(out.graph)))]
    large = snapshot_bytes(out, graph=large_graph)
    reject('aggregate-node-budget', b, a, t, [replay_bytes(large, large, [])] * 5)
    # Expanded roots are charged per occurrence even when the DAG is shared.
    graph = [(1, 0)]
    for _ in range(14):
        graph.append((16, len(graph)-1, len(graph)-1))
    graph.append((3,))
    big = snapshot_bytes(out, graph=graph, term=14, ty=15)
    reject('aggregate-expanded-work', b, a, t, [replay_bytes(big, big, [])] * 9)
    # Guard selected beta expansion before invoking Core, with a smaller control.
    def expansion_snapshot(levels):
        graph = [(3,), (0, 0)]
        body = 1
        for _ in range(levels):
            graph.append((16, body, body)); body = len(graph)-1
        graph.append((9, 0, 0, body)); function = len(graph)-1
        graph.append((1, 7)); arg = len(graph)-1
        for _ in range(levels):
            graph.append((16, arg, arg)); arg = len(graph)-1
        graph.append((10, function, arg))
        return Snapshot.read(snapshot_bytes(out, graph=graph, term=len(graph)-1, ty=0))
    assert head_request(expansion_snapshot(2)) == []
    try:
        head_request(expansion_snapshot(9))
    except Unsupported as error:
        assert 'substitution work' in str(error)
    else:
        raise AssertionError('expanding beta request reached Core')
    # No downstream publication after fuel exhaustion or invalid input/output.
    published = normalizer.published
    for fuel in [0, 1]:
        try:
            normalizer.generate(b, t, fuel=fuel, consumer=lambda _: (_ for _ in ()).throw(AssertionError('published')))
        except Unsupported as e:
            assert 'fuel exhausted' in str(e)
        else:
            raise AssertionError('fuel exhaustion accepted')
    assert normalizer.published == published
    invoked = normalizer.invoked
    try:
        normalizer.generate(b, other[2])
    except Unsupported:
        pass
    else:
        raise AssertionError('invalid input consumed')
    assert normalizer.invoked == invoked
    original = normalizer.consume
    def corrupt(retained, path):
        after, record = original(retained, path)
        return changed, record
    normalizer.consume = corrupt
    try:
        normalizer.generate(b, t)
    except Unsupported:
        pass
    else:
        raise AssertionError('corrupt intermediate reused')
    assert normalizer.invoked == invoked + 1 and normalizer.published == published
    normalizer.consume = original
    disk = output / 'once.snapshot'; disk.write_bytes(b)
    retained = disk.read_bytes(); disk.write_bytes(other[0])
    seen = []
    normalizer.generate(retained, t, claim=q, consumer=seen.append)
    assert seen == [a]
    # The standalone producer emits no partial bundle on failure.
    input_path, typing_path = output / 'input.snapshot', output / 'input.typing'
    input_path.write_bytes(b); typing_path.write_bytes(t)
    cli = [sys.executable, __file__, '--generate', str(input_path), str(typing_path),
           '--driver', str(driver), '--checker', shlex.join(checker)]
    failed = command([*cli, '--fuel', '0'])
    assert failed.returncode == 1 and failed.stdout == b'' and b'fuel exhausted' in failed.stderr
    bundle = success(command([*cli, '--claim', *q]))
    assert bundle.split(b'\n') == [b, a, t, chain_bytes(rs)]
    print(f'finite head normalization: {len(cases)+2} accepts, {rejected} rejections, '
          '2 fuel failures, 2 gated failures, read-once publication')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean --run CheckNormalization.lean')
    parser.add_argument('--generate', nargs=2, metavar=('SNAPSHOT', 'TYPING'))
    parser.add_argument('--driver', type=Path)
    parser.add_argument('--fuel', type=int, default=STEP_LIMIT)
    parser.add_argument('--claim', nargs=3, default=(), metavar=('RELATION', 'LEFT', 'RIGHT'))
    args = parser.parse_args()
    if args.generate:
        try:
            require(args.driver is not None, '--generate requires an actual Core replay driver')
            retained = []
            for path in args.generate:
                with open(path, 'rb') as stream:
                    payload = stream.read(8 * 1024 * 1024 + 1)
                require(len(payload) <= 8 * 1024 * 1024, 'input byte limit')
                retained.append(payload)
            before, typing = retained
            normalizer = Normalizer(args.driver.resolve(), shlex.split(args.checker))
            after, records = normalizer.generate(before, typing, fuel=args.fuel, claim=args.claim)
            sys.stdout.buffer.write(b'\n'.join([before, after, typing, chain_bytes(records)]))
            return 0
        except (Unsupported, AssertionError, OSError, subprocess.TimeoutExpired) as error:
            print(f'normalization producer rejected: {error}', file=sys.stderr)
            return 1
    with tempfile.TemporaryDirectory(prefix='jihoo-head-normalization-') as folder:
        test(shlex.split(args.compiler), shlex.split(args.checker), Path(folder))


if __name__ == '__main__':
    sys.exit(main())
