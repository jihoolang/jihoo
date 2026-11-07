#!/usr/bin/env python3
"""Checked type-index beta normalization after finite term head normalization.

The producer is untrusted. Only exact retained snapshots validated by the Lean
checker are reused, and only a completed requested literal observation is published.
"""
from __future__ import annotations

import argparse
from dataclasses import replace
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile

from core_head_normalization import Normalizer, STEP_LIMIT, chain_bytes, head_request
from core_typing_producer import Snapshot, Unsupported, produce, require
from core_typing_certificates import ROOT, command, success, snapshot_bytes
from core_typed_beta_replay import replay_bytes


def index_request(snapshot):
    node = snapshot.graph[snapshot.type]
    require(node[0] in (6, 7), 'only Eq/Lt type indices are supported')
    for child, root in enumerate(node[1:]):
        path = head_request(replace(snapshot, term=root))
        if path is not None:
            return [child, *path]
    return None


class TypeNormalizer:
    def __init__(self, driver, checker):
        self.driver, self.checker = driver, checker
        self.invoked = self.published = 0

    def bundle(self, before, middle, after, typing, heads, types):
        return b'\n'.join([before, middle, after, typing, chain_bytes(heads), chain_bytes(types)])

    def validate(self, before, middle, after, typing, heads, types, *args):
        return command([*self.checker, *args], self.bundle(before, middle, after, typing, heads, types),
                       cwd=ROOT / 'proofs')

    def consume(self, retained, path):
        self.invoked += 1
        return success(command([self.driver, '--type', *map(str, path)], retained)).split(b'\n')

    def generate(self, before, typing, *, claim, fuel=STEP_LIMIT, consumer=None):
        require(len(claim) == 3 and claim[0] in ('eq', 'lt'), 'literal claim required')
        require(0 <= fuel <= STEP_LIMIT, 'fuel range')
        head = Normalizer(self.driver, ['lake', 'env', 'lean', '--run', 'CheckNormalization.lean'])
        middle, heads = head.generate(before, typing, fuel=fuel)
        current, types = middle, []
        # This gate also checks the whole combined resource budget before the
        # first type-root operation. No output typing certificate is supplied.
        success(self.validate(before, middle, current, typing, heads, types, '--prefix'))
        while True:
            path = index_request(Snapshot.read(current))
            if path is None:
                success(self.validate(before, middle, current, typing, heads, types, *claim))
                bundle = self.bundle(before, middle, current, typing, heads, types)
                if consumer:
                    consumer(bundle)
                self.published += 1
                return middle, current, heads, types
            require(len(heads) + len(types) < fuel, 'combined normalization fuel exhausted')
            after, record = self.consume(current, path)
            # Whole-graph continuity, path, term identity, formation and the
            # combined budget are verified before the next Core invocation.
            success(self.validate(before, middle, after, typing, heads, [*types, record], '--prefix'))
            current, types = after, [*types, record]


FIXTURES = {
    'literal': ('(def value (Eq 7 7) (refl 7))', ['eq', '7', '7'], 0, 0),
    'left': ('(def value (Eq (app (lam x U64 x) 7) 7) (refl 7))', ['eq', '7', '7'], 0, 1),
    'both': ('(def value (Eq (app (lam x U64 x) 7) (app (lam y U64 y) 7)) (refl 7))', ['eq', '7', '7'], 0, 2),
    'bound': ('(def value (Lt (app (lam x U64 x) 1) (app (lam y U64 y) 2)) (decide-lt 1 2))', ['lt', '1', '2'], 0, 2),
    'composed': ('(def value (Eq (app (lam x U64 x) 7) 7) (app (lam y U64 (refl y)) 7))', ['eq', '7', '7'], 1, 1),
    'higher-order': ('(def value (Eq (app (lam f (pi x U64 U64) (app f 7)) (lam x U64 x)) 7) (refl 7))', ['eq', '7', '7'], 0, 2),
}


def test(compiler, checker, output):
    exporter, driver = output / 'snapshot', output / 'replay'
    for source, binary in [('core_typing_snapshots.jh', exporter), ('core_typed_beta_replay.jh', driver)]:
        success(command([*compiler, 'build', '-O2', '-I', 'compiler', f'tests/{source}', '-o', binary]))
    normalizer = TypeNormalizer(driver, checker)
    cases = {}
    for name, (source, claim, nh, nt) in FIXTURES.items():
        before = success(command([exporter, 'require'], source.encode()))
        try:
            typing = produce(before)
        except Unsupported as error:
            raise Unsupported(f'{name}: {error}') from error
        middle, after, heads, types = normalizer.generate(before, typing, claim=claim)
        assert (len(heads), len(types)) == (nh, nt), name
        cases[name] = (before, middle, after, typing, heads, types, claim)
    rejected = 0

    def reject(name, b, m, a, t, hs, ts, *args):
        nonlocal rejected
        r = normalizer.validate(b, m, a, t, hs, ts, *args)
        assert r.returncode == 1 and b'rejected' in r.stderr, (name, r)
        rejected += 1

    b, m, a, t, hs, ts, q = cases['both']
    middle, first = success(command([driver, '--type', '0'], m)).split(b'\n')
    success(normalizer.validate(b, m, middle, t, hs, [first], '--prefix'))
    reject('unfinished-empty', b, m, m, t, hs, [], *q)
    reject('unfinished-prefix', b, m, middle, t, hs, [first], *q)
    reject('convertible-nonstep', b, m, m, t, hs, [replay_bytes(m, m, [0])], '--prefix')
    reject('missing', b, m, a, t, hs, ts[1:], *q)
    reject('reordered', b, m, a, t, hs, list(reversed(ts)), *q)
    reject('duplicate', b, m, a, t, hs, [ts[0], *ts], *q)
    reject('false-equality', b, m, a, t, hs, ts, 'eq', '7', '8')
    reject('other-true-claim', b, m, a, t, hs, ts, 'eq', '8', '8')
    reject('wrong-relation', b, m, a, t, hs, ts, 'lt', '7', '8')
    other = cases['bound']
    reject('other-valid-typing', b, m, a, other[3], hs, ts, *q)
    reject('other-valid-input', other[0], m, a, t, hs, ts, *q)
    sm, sa = Snapshot.read(middle), Snapshot.read(a)
    changed = snapshot_bytes(sm, graph=[*sm.graph, (18,)])
    reject('unreachable-middle-node', b, m, a, t, hs,
           [replay_bytes(m, changed, [0]), ts[1]], *q)
    dup = snapshot_bytes(sa, graph=[*sa.graph, sa.graph[sa.term]], term=len(sa.graph))
    reject('equivalent-term-id', b, m, dup, t, hs, [ts[0], replay_bytes(middle, dup, [1])], *q)
    tydup = snapshot_bytes(sa, graph=[*sa.graph, sa.graph[sa.type]], ty=len(sa.graph))
    reject('unbound-final-type-id', b, m, tydup, t, hs, ts, *q)
    wrong_term = snapshot_bytes(sa, term=sa.type)
    reject('changed-evidence', b, m, wrong_term, t, hs,
           [ts[0], replay_bytes(middle, wrong_term, [1])], *q)
    # Valid alternative index contraction is not the deterministic request.
    right, right_record = success(command([driver, '--type', '1'], m)).split(b'\n')
    reject('right-before-left', b, m, right, t, hs, [right_record], '--prefix')
    reject('term-type-role-swap', b, m, a, t, ts, hs, *q)
    cb, cm, ca, ct, ch, cs, cq = cases['composed']
    reject('changed-phase-boundary', cb, cb, ca, ct, ch, cs, *cq)
    reject('type-record-in-head-slot', cb, cm, ca, ct, cs, ch, *cq)
    reject('path-limit', b, m, a, t, hs, [replay_bytes(m, a, [0] * 129)], *q)
    reject('combined-chain-limit', cb, cm, ca, ct, ch * 33, cs * 32, *cq)
    reject('noncanonical-record', b, m, a, t, hs, [ts[0] + b';', ts[1]], *q)
    # Normalized type must be the requested literal, not just head normal.
    arithmetic = success(command([exporter, 'require'], b'(def value (Eq (uadd 3 4) 7) (refl 7))'))
    ar_typing = produce(arithmetic)
    reject('arithmetic-outside-beta-policy', arithmetic, arithmetic, arithmetic, ar_typing, [], [], *q)
    old = command(['lake', 'env', 'lean', '--run', 'CheckNormalization.lean', *q],
                  b'\n'.join([b, m, t, chain_bytes([])]), cwd=ROOT / 'proofs')
    assert old.returncode == 1, 'fixture already accepted by literal-only endpoint'
    published, invoked = normalizer.published, normalizer.invoked
    for fuel in [0, 1]:
        try:
            normalizer.generate(b, t, claim=q, fuel=fuel)
        except Unsupported as e:
            assert 'fuel exhausted' in str(e)
        else:
            raise AssertionError('exhaustion published')
    assert normalizer.published == published
    invoked = normalizer.invoked
    try:
        normalizer.generate(b, other[3], claim=q)
    except AssertionError:
        pass
    else:
        raise AssertionError('invalid input used')
    assert normalizer.invoked == invoked
    original = normalizer.consume
    def corrupt(retained, path):
        after, record = original(retained, path)
        return changed, record
    normalizer.consume = corrupt
    try:
        normalizer.generate(b, t, claim=q)
    except AssertionError:
        pass
    else:
        raise AssertionError('invalid intermediate used')
    assert normalizer.invoked == invoked + 1 and normalizer.published == published
    normalizer.consume = original
    final_seen = []
    try:
        normalizer.generate(b, t, claim=['eq', '7', '8'], consumer=final_seen.append)
    except AssertionError:
        pass
    else:
        raise AssertionError('invalid final claim published')
    assert normalizer.published == published and final_seen == []
    disk = output / 'input.snapshot'; disk.write_bytes(b)
    retained = disk.read_bytes(); disk.write_bytes(other[0])
    seen = []
    normalizer.generate(retained, t, claim=q, consumer=seen.append)
    assert seen == [normalizer.bundle(b, m, a, t, hs, ts)]
    input_path, typing_path = output / 'cli.snapshot', output / 'cli.typing'
    input_path.write_bytes(b); typing_path.write_bytes(t)
    cli = [sys.executable, __file__, '--generate', str(input_path), str(typing_path),
           '--driver', str(driver), '--checker', shlex.join(checker), '--claim', *q]
    failed = command([*cli, '--fuel', '0'])
    assert failed.returncode == 1 and failed.stdout == b'' and b'fuel exhausted' in failed.stderr
    assert success(command(cli)) == normalizer.bundle(b, m, a, t, hs, ts)
    print(f'type-index normalization: {len(cases)+1} accepts, {rejected} rejections, '
          '2 fuel failures, 3 gated failures, read-once publication')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean --run CheckTypeNormalization.lean')
    parser.add_argument('--generate', nargs=2, metavar=('SNAPSHOT', 'TYPING'))
    parser.add_argument('--driver', type=Path)
    parser.add_argument('--fuel', type=int, default=STEP_LIMIT)
    parser.add_argument('--claim', nargs=3, metavar=('RELATION', 'LEFT', 'RIGHT'))
    args = parser.parse_args()
    if args.generate:
        try:
            require(args.driver is not None and args.claim is not None, 'driver and literal claim required')
            retained = []
            for path in args.generate:
                with open(path, 'rb') as stream:
                    payload = stream.read(8 * 1024 * 1024 + 1)
                require(len(payload) <= 8 * 1024 * 1024, 'input byte limit')
                retained.append(payload)
            before, typing = retained
            normalizer = TypeNormalizer(args.driver.resolve(), shlex.split(args.checker))
            middle, after, heads, types = normalizer.generate(before, typing, claim=args.claim, fuel=args.fuel)
            sys.stdout.buffer.write(normalizer.bundle(before, middle, after, typing, heads, types))
            return 0
        except (Unsupported, AssertionError, OSError, subprocess.TimeoutExpired) as error:
            print(f'type-index producer rejected: {error}', file=sys.stderr)
            return 1
    with tempfile.TemporaryDirectory(prefix='jihoo-type-index-') as folder:
        test(shlex.split(args.compiler), shlex.split(args.checker), Path(folder))


if __name__ == '__main__':
    sys.exit(main())
