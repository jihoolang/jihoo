#!/usr/bin/env python3
"""Validate actual ghost Core.normal output within a conservative beta/add profile.

This is per-run validation, not a formal Core.normal refinement theorem.
Unsupported symbolic arithmetic, overflow and resource exhaustion fail closed.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile
from core_typing_producer import Snapshot, Unsupported, produce, require, encode_numbers
from core_typing_certificates import ROOT, command, snapshot_bytes


def success(result):
    """Enforce subprocess failure even when Python assertions are disabled."""
    if result.returncode != 0:
        raise Unsupported(f'command failed ({result.returncode}): {result.args}: '
                          f'{result.stderr.decode(errors="replace")}')
    return result.stdout


def record_bytes(before, after, depth=128, fuel=64):
    return encode_numbers([6, depth, fuel]) + before + after


class CheckedNormalizer:
    def __init__(self, driver, checker):
        self.driver, self.checker = driver, checker
        self.invoked = self.published = 0

    def gate(self, before, typing, depth=128, fuel=64):
        return command([*self.checker, '--input', str(depth), str(fuel)],
                       before + b'\n' + typing, cwd=ROOT / 'proofs')

    def validate(self, before, after, typing, record, depth=128, fuel=64):
        return command([*self.checker, str(depth), str(fuel)],
                       b'\n'.join([before, after, typing, record]), cwd=ROOT / 'proofs')

    def consume(self, before, depth, fuel):
        self.invoked += 1
        return success(command([self.driver, '--normal', str(depth), str(fuel)], before)).split(b'\n')

    def generate(self, before, typing, *, depth=128, fuel=64, consumer=None):
        success(self.gate(before, typing, depth, fuel))
        after, record = self.consume(before, depth, fuel)
        success(self.validate(before, after, typing, record, depth, fuel))
        bundle = b'\n'.join([before, after, typing, record])
        if consumer:
            consumer(bundle)
        self.published += 1
        return after, record


FIXTURES = {
    'literal': '(def value U64 7)',
    'add': '(def value U64 (uadd 3 4))',
    'nested-add': '(def value U64 (uadd (uadd 1 2) (uadd 3 4)))',
    'evidence': '(def value (Eq 7 7) (refl (uadd 3 4)))',
    'original-type': '(def value (Eq (uadd 3 4) (uadd 3 4)) (refl (uadd 3 4)))',
    'beta-add': '(def value U64 (uadd (app (lam x U64 x) 3) 4))',
    'higher-order': '(def value U64 (app (lam f (pi x U64 U64) (app f (uadd 3 4))) (lam x U64 x)))',
    'lambda-body': '(def value (pi x U64 U64) (lam x U64 (uadd 3 4)))',
    'dependent': '(def value (pi x U64 (Eq (uadd 3 4) (uadd 3 4))) (lam x U64 (refl (uadd 3 4))))',
    'max-word': '(def value U64 (uadd 18446744073709551614 1))',
    'bound': '(def value (Lt 1 2) (decide-lt 1 2))',
}
REJECTED = {
    'symbolic-add': '(def value (pi x U64 U64) (lam x U64 (uadd x 1)))',
    'closed-symbolic-body': '(def value U64 (app (lam x U64 (uadd x 1)) 6))',
    'symbolic-reorder': '(def value (pi x U64 U64) (lam x U64 (uadd 1 x)))',
    'overflow': '(def value U64 (uadd 18446744073709551615 1))',
    'subtraction': '(def value U64 (usub 3 1 (decide-lt 1 4)))',
    'elements': '(def value (Array 1) (array (int 7)))',
}


def test(compiler, checker, output):
    success(command([sys.executable, ROOT / "tests/core_checked_normalization_optimized.py"]))
    exporter, driver = output / 'snapshot', output / 'normal'
    for source, binary in [('core_typing_snapshots.jh', exporter), ('core_typed_beta_replay.jh', driver)]:
        success(command([*compiler, 'build', '-O2', '-I', 'compiler', f'tests/{source}', '-o', binary]))
    normalizer = CheckedNormalizer(driver, checker)
    cases = {}
    for name, source in FIXTURES.items():
        before = success(command([exporter, 'require'], source.encode()))
        try:
            typing = produce(before)
        except Unsupported as e:
            raise Unsupported(f'{name}: {e}') from e
        after, record = normalizer.generate(before, typing)
        cases[name] = before, after, typing, record
    b, a, t, r = cases['add']
    sa = Snapshot.read(a)
    assert sa.graph[sa.term] == (1, 7), 'actual Core.normal must fold addition'
    sb = Snapshot.read(b)
    assert sb.graph[sb.term][0] == 16
    # substitute-only replay cannot account for this operation.
    assert command([driver], b).returncode == 1
    rejected = 0
    def reject(name, before, after, typing, record, depth=128, fuel=64):
        nonlocal rejected
        result = normalizer.validate(before, after, typing, record, depth, fuel)
        assert result.returncode == 1 and b'rejected' in result.stderr, (name, result)
        rejected += 1
    reject('wrong-depth', b, a, t, r, 127)
    reject('wrong-fuel', b, a, t, r, 128, 63)
    reject('depth-zero', b, a, t, record_bytes(b, a, 0), 0)
    reject('depth-excess', b, a, t, record_bytes(b, a, 129), 129)
    reject('fuel-excess', b, a, t, record_bytes(b, a, 128, 65), 128, 65)
    reject('fuel-exhaustion', b, a, t, record_bytes(b, a, 128, 0), 128, 0)
    reject('convertible-uncomputed-output', b, b, t, record_bytes(b, b))
    other = cases['bound']
    reject('other-valid-input', other[0], a, t, r)
    reject('other-valid-typing', b, a, other[2], r)
    reject('other-valid-output', b, other[1], t, r)
    dup = snapshot_bytes(sa, graph=[*sa.graph, sa.graph[sa.term]], term=len(sa.graph))
    reject('equivalent-distinct-root', b, dup, t, r)
    tydup = snapshot_bytes(sa, graph=[*sa.graph, sa.graph[sa.type]], ty=len(sa.graph))
    reject('substituted-type-root', b, tydup, t, record_bytes(b, tydup))
    # The original prefix is immutable, even if changed nodes are unreachable.
    extended = snapshot_bytes(sb, graph=[*sb.graph, (18,)])
    ext_typing = produce(extended)
    ext_after, _ = normalizer.generate(extended, ext_typing)
    se = Snapshot.read(ext_after)
    graph = list(se.graph); graph[len(sb.graph)] = (19, 0)
    changed = snapshot_bytes(se, graph=graph)
    reject('changed-unreachable-prefix', extended, changed, ext_typing, record_bytes(extended, changed))
    reject('trailing-record', b, a, t, r + b';')
    reject('wrong-operation-tag', b, a, t, encode_numbers([4]) + r.split(b';', 1)[1])
    reject('excessive-token', b, a, t, b'1' * 65 + b';' + r)
    rejected_inputs = 0
    for name, source in REJECTED.items():
        before = success(command([exporter, 'require'], source.encode()))
        typing = produce(before)
        invoked, published = normalizer.invoked, normalizer.published
        result = normalizer.gate(before, typing)
        assert result.returncode == 1 and b'rejected' in result.stderr, name
        try:
            normalizer.generate(before, typing)
        except Unsupported:
            pass
        else:
            raise AssertionError(f'{name} admitted')
        assert normalizer.invoked == invoked and normalizer.published == published
        rejected_inputs += 1
        if name in ('symbolic-reorder', 'subtraction', 'closed-symbolic-body'):
            actual, record = success(command([driver, '--normal', '128', '64'], before)).split(b'\n')
            reject(f'unsupported-actual-result-{name}', before, actual, typing, record)
    # Shared references are charged by expanded size, before invoking Core.
    graph = [(3,), (1, 0)]
    for _ in range(14):
        graph.append((16, len(graph)-1, len(graph)-1))
    large = snapshot_bytes(sb, graph=graph, term=len(graph)-1, ty=0)
    large_typing = produce(large)
    success(command(['lake', 'env', 'lean', '--run', 'CheckTyping.lean', '--snapshot'],
                    large + b'\n' + large_typing, cwd=ROOT / 'proofs'))
    assert normalizer.gate(large, large_typing).returncode == 1
    rejected_inputs += 1
    # Actual Core depth failure occurs after valid admission; no output escapes.
    success(normalizer.gate(b, t, depth=1))
    seen = []; published = normalizer.published
    try:
        normalizer.generate(b, t, depth=1, consumer=seen.append)
    except Unsupported:
        pass
    else:
        raise AssertionError('Core resource failure published')
    assert seen == [] and normalizer.published == published
    invoked = normalizer.invoked
    try:
        normalizer.generate(b, other[2])
    except Unsupported:
        pass
    else:
        raise AssertionError('invalid typing invoked Core')
    assert normalizer.invoked == invoked
    original = normalizer.consume
    def corrupt(before, depth, fuel):
        after, record = original(before, depth, fuel)
        return dup, record
    normalizer.consume = corrupt
    try:
        normalizer.generate(b, t, consumer=seen.append)
    except Unsupported:
        pass
    else:
        raise AssertionError('invalid output published')
    assert seen == [] and normalizer.published == published
    normalizer.consume = original
    disk = output / 'once.snapshot'; disk.write_bytes(b)
    retained = disk.read_bytes(); disk.write_bytes(other[0])
    normalizer.generate(retained, t, consumer=seen.append)
    assert seen == [b'\n'.join([b, a, t, r])]
    # Public CLI retains inputs once and publishes only a complete valid bundle.
    disk.write_bytes(b); typed = output / 'once.typing'; typed.write_bytes(t)
    cli = [sys.executable, __file__, '--generate', str(disk), str(typed),
           '--driver', str(driver), '--checker', shlex.join(checker)]
    failed = command([*cli, '--depth', '1'])
    assert failed.returncode == 1 and failed.stdout == b''
    assert success(command(cli)) == b'\n'.join([b, a, t, r])
    print(f'actual ghost Core.normal: {len(cases)+2} accepts, {rejected} output/request rejections, '
          f'{rejected_inputs} unsupported inputs gated, 1 Core resource failure, 2 invalid input/output gates, read-once publication')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean --run CheckCoreNormal.lean')
    parser.add_argument('--generate', nargs=2, metavar=('SNAPSHOT', 'TYPING'))
    parser.add_argument('--driver', type=Path)
    parser.add_argument('--depth', type=int, default=128)
    parser.add_argument('--fuel', type=int, default=64)
    args = parser.parse_args()
    if args.generate:
        try:
            require(args.driver is not None, '--driver is required')
            retained = []
            for path in args.generate:
                with open(path, 'rb') as stream:
                    data = stream.read(8 * 1024 * 1024 + 1)
                require(len(data) <= 8 * 1024 * 1024, 'input byte limit')
                retained.append(data)
            before, typing = retained
            normalizer = CheckedNormalizer(args.driver.resolve(), shlex.split(args.checker))
            after, record = normalizer.generate(before, typing, depth=args.depth, fuel=args.fuel)
            sys.stdout.buffer.write(b'\n'.join([before, after, typing, record]))
            return 0
        except (Unsupported, AssertionError, OSError, subprocess.TimeoutExpired) as error:
            print(f'checked Core.normal producer rejected: {error}', file=sys.stderr)
            return 1
    with tempfile.TemporaryDirectory(prefix='jihoo-checked-normal-') as folder:
        test(shlex.split(args.compiler), shlex.split(args.checker), Path(folder))


if __name__ == '__main__':
    sys.exit(main())
