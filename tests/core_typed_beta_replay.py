#!/usr/bin/env python3
"""Typed single beta replay on actual imported Core snapshots.

The four retained canonical byte artifacts are checked before downstream use.
Exporter/importer fidelity and this orchestration remain tested IO boundaries.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import shlex
import tempfile

from core_typing_producer import Snapshot, produce, encode_numbers
from core_typing_certificates import ROOT, command, success, snapshot_bytes

FIXTURES = {
    'head': ('(def value U64 (app (lam x U64 x) 7))', []),
    'dependent': ('(def value (Eq 7 7) (app (lam x U64 (refl x)) 7))', []),
    'body': ('(def value (pi n U64 (Eq n n)) '
             '(lam n U64 (app (lam m U64 (refl m)) n)))', [1]),
    'capture': ('(def value (pi n U64 (pi xs (Array n) (Array n))) '
                '(lam n U64 (app (lam m U64 (lam xs (Array m) xs)) n)))', [1]),
    'argument': ('(def value (Eq 7 7) '
                 '(app (lam x U64 (refl x)) (app (lam y U64 y) 7)))', [1]),
    'function': ('(def value U64 '
                 '(app (app (lam n U64 (lam x U64 x)) 1) 7))', [0]),
    'array-element': ('(def value (Array 2) '
                      '(array (int 1) (app (lam x I64 x) (int 2))))', [1]),
    'annotation': ('(def value (pi xs (Array 1) (Array 1)) '
                   '(lam xs (Array (app (lam x U64 x) 1)) xs))', [0, 0]),
    'proof': ('(def value I64 (index (array (int 4)) 0 '
              '(app (lam0 p (Lt 0 1) p) (decide-lt 0 1))))', [2]),
    'refl': ('(def value (Eq 7 7) (refl (app (lam x U64 x) 7)))', [0]),
    'sum': ('(def value U64 (uadd 1 (app (lam x U64 x) 7)))', [1]),
}


def replay_bytes(before, after, path):
    return encode_numbers([4]) + before + after + encode_numbers([len(path), *path])


class Replay:
    def __init__(self, typing_checker, beta_checker, driver):
        self.typing_checker, self.beta_checker, self.driver = typing_checker, beta_checker, driver
        self.invoked = self.published = 0

    def validate(self, before, after, typing, replay, path):
        return command([*self.beta_checker, *map(str, path)],
                       b'\n'.join([before, after, typing, replay]), cwd=ROOT / 'proofs')

    def checked(self, before, typing, path, *, consumer=None):
        # Both calls receive the same immutable bytes, never a path re-read.
        success(command([*self.typing_checker, '--snapshot'], before + b'\n' + typing,
                        cwd=ROOT / 'proofs'))
        self.invoked += 1
        after, replay = success(command([self.driver, *map(str, path)], before)).split(b'\n')
        success(self.validate(before, after, typing, replay, path))
        if consumer:
            consumer(after)
        self.published += 1
        return after, replay


def test(compiler, checker, output):
    output.mkdir(parents=True, exist_ok=True)
    exporter, driver = output / 'snapshot', output / 'replay'
    for source, binary in [('core_typing_snapshots.jh', exporter), ('core_typed_beta_replay.jh', driver)]:
        success(command([*compiler, 'build', '-O2', '-I', 'compiler', f'tests/{source}', '-o', binary]))
    typing_checker = ['lake', 'env', 'lean', '--run', 'CheckTyping.lean']
    replay = Replay(typing_checker, checker, driver)
    cases = {}
    for name, (source, path) in FIXTURES.items():
        before = success(command([exporter, 'require'], source.encode()))
        typing = produce(before)
        after, artifact = replay.checked(before, typing, path)
        s, t = Snapshot.read(before), Snapshot.read(after)
        assert s.type == t.type
        assert t.graph[:len(s.graph)] == s.graph
        cases[name] = (before, after, typing, artifact, path)
    rejected = 0

    def reject(name, b, a, t, r, path):
        nonlocal rejected
        result = replay.validate(b, a, t, r, path)
        assert result.returncode == 1 and b'rejected' in result.stderr, (name, result)
        rejected += 1

    b, a, t, r, path = cases['head']
    s, out = Snapshot.read(b), Snapshot.read(a)
    # Convertibility is insufficient: an unchanged redex is not one step.
    reject('reflexive-conversion', b, b, t, replay_bytes(b, b, []), [])
    reject('wrong-request', b, a, t, r, [0])
    reject('wrong-described-path', b, a, t, replay_bytes(b, a, [1]), [])
    reject('absent-redex', b, a, t, replay_bytes(b, a, [1]), [1])
    reject('invalid-child', b, a, t, replay_bytes(b, a, [99]), [99])
    reject('oversized-path', b, a, t, replay_bytes(b, a, [0] * 129), [0] * 129)
    # Another independently valid typed snapshot must not replace the retained input.
    other = cases['dependent']
    reject('different-typed-input', b, other[1], other[2], other[3], other[4])
    reject('different-typed-certificate', b, a, other[2], r, [])
    # Unreachable sort mutation: both graphs still decode the same selected terms.
    graph = list(s.graph)
    inert = next(i for i, n in enumerate(graph) if n[0] == 19)
    graph[inert] = (19, (graph[inert][1] + 1) % 33)
    changed_input = snapshot_bytes(s, graph=graph)
    reject('unreachable-input', changed_input, a, t, r, [])
    graph = list(out.graph)
    graph[inert] = (19, (graph[inert][1] + 1) % 33)
    changed_output = snapshot_bytes(out, graph=graph)
    reject('unreachable-output', b, changed_output, t, r, [])
    # Exact output and type IDs, even when their graph nodes have equal denotations.
    duplicate = list(out.graph) + [out.graph[out.term], out.graph[out.type]]
    out_dup = snapshot_bytes(out, graph=duplicate)
    root_changed = snapshot_bytes(out, graph=duplicate, term=len(duplicate) - 2)
    type_changed = snapshot_bytes(out, graph=duplicate, ty=len(duplicate) - 1)
    reject('equivalent-output-id', b, root_changed, t, replay_bytes(b, out_dup, []), [])
    reject('equivalent-type-id-association', b, type_changed, t, replay_bytes(b, out_dup, []), [])
    reject('type-id-must-remain-original', b, type_changed, t, replay_bytes(b, type_changed, []), [])
    # Root substitution to another formed type must fail even when artifact agrees.
    wrong_type_graph = list(out.graph) + [(4,)]
    wrong_type = snapshot_bytes(out, graph=wrong_type_graph, ty=len(wrong_type_graph) - 1)
    reject('substituted-formed-type', b, wrong_type, t, replay_bytes(b, wrong_type, []), [])
    # Same ID but altered type interpretation is independently checked too.
    graph = list(out.graph); graph[out.type] = (4,)
    changed_type = snapshot_bytes(out, graph=graph)
    reject('altered-original-type', b, changed_type, t, replay_bytes(b, changed_type, []), [])
    # Complete malformed graph validity includes nodes not reachable from the output.
    graph = list(out.graph) + [(10, len(out.graph), 0)]
    cyclic = snapshot_bytes(out, graph=graph)
    reject('unreachable-cycle', b, cyclic, t, replay_bytes(b, cyclic, []), [])
    for label, payload in [('trailing', r + b';'), ('noncanonical', b'00;' + r[4:]),
                           ('huge-token', b'1' * 65 + b';' + r), ('truncated', r[:-1])]:
        reject(label, b, a, t, payload, [])
    # No producer normalization shortcut: two nested contractions cannot be collapsed.
    nb, na, nt, nr, np = cases['argument']
    fully_reduced, _ = success(command([driver], na)).split(b'\n')
    reject('two-contractions-not-one', nb, fully_reduced, nt,
           replay_bytes(nb, fully_reduced, np), np)
    # Whole-DAG bounds count shared children repeatedly before any expansion.
    graph = list(out.graph)
    for _ in range(18):
        graph.append((16, len(graph) - 1, len(graph) - 1))
    oversized = snapshot_bytes(out, graph=graph)
    reject('exponential-unreachable-dag', b, oversized, t, replay_bytes(b, oversized, []), [])
    graph = list(out.graph) + [(18,)] * 4097
    oversized = snapshot_bytes(out, graph=graph)
    reject('graph-count-limit', b, oversized, t, replay_bytes(b, oversized, []), [])
    reject('input-byte-limit', b, a, t, r + b';' * (8 * 1024 * 1024), [])
    # Read-once handoff: replacing disk input after retention cannot change the consumed bytes.
    disk = output / 'once.snapshot'; disk.write_bytes(b)
    retained = disk.read_bytes(); disk.write_bytes(other[0])
    got = []
    replay.checked(retained, t, [], consumer=got.append)
    assert got == [a]
    invoked, published = replay.invoked, replay.published
    try:
        replay.checked(b, other[2], [], consumer=got.append)
    except AssertionError:
        pass
    else:
        raise AssertionError('invalid input reached replay')
    assert (replay.invoked, replay.published, len(got)) == (invoked, published, 1)
    # A corrupt output never reaches the downstream consumer.
    original = replay.validate
    replay.validate = lambda before, after, typing, artifact, path: original(
        before, changed_output, typing, artifact, path)
    try:
        replay.checked(b, t, [], consumer=got.append)
    except AssertionError:
        pass
    else:
        raise AssertionError('invalid output published')
    assert replay.published == published and len(got) == 1
    print(f'typed beta replay: {len(cases) + 1} accepts, {rejected} rejections, 2 gated handoffs')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean --run CheckBetaReplay.lean')
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    compiler, checker = shlex.split(args.compiler), shlex.split(args.checker)
    if args.output_dir:
        test(compiler, checker, args.output_dir.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='jihoo-typed-beta-') as folder:
            test(compiler, checker, Path(folder))


if __name__ == '__main__':
    main()
