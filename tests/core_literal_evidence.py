#!/usr/bin/env python3
"""Literal truth from exact actual-Core typing snapshots and head canonical forms.

The validator does not decide the requested relation directly. It validates the
snapshot's original typing and head normality; Lean derives literal truth.
No normalization or full executable-checker refinement is claimed.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import shlex
import tempfile

from core_typing_producer import Snapshot, produce, encode_certificate
from core_certificate_process import ROOT, command, success
from core_typing_certificates import snapshot_bytes

FIXTURES = {
    'literal-equality': ('(def value (Eq 7 7) (refl 7))', ['eq', '7', '7']),
    'beta-index': ('(def value (Eq 7 7) (refl (app (lam x U64 x) 7)))', ['eq', '7', '7']),
    'addition-index': ('(def value (Eq 2 2) (refl (uadd 1 1)))', ['eq', '2', '2']),
    'literal-bound': ('(def value (Lt 1 2) (decide-lt 1 2))', ['lt', '1', '2']),
    'higher-order-index': ('(def value (Eq 7 7) '
        '(refl (app (lam f (pi x U64 U64) (app f 7)) (lam x U64 x))))', ['eq', '7', '7']),
}
UNFINISHED = {
    'head-redex': ('(def value (Eq 7 7) (app (lam x U64 (refl x)) 7))', ['eq', '7', '7']),
    'function-spine': ('(def value (Eq 7 7) '
        '(app (app (lam0 f (pi x U64 (Eq x x)) f) (lam x U64 (refl x))) 7))', ['eq', '7', '7']),
    'nonliteral-type': ('(def value (Eq (uadd 1 1) 2) (refl 2))', ['eq', '2', '2']),
}


def test(compiler, checker, output):
    output.mkdir(parents=True, exist_ok=True)
    exporter = output / 'snapshot'
    success(command([*compiler, 'build', '-O2', '-I', 'compiler',
                     'tests/core_typing_snapshots.jh', '-o', exporter]))
    accepted = rejected = 0

    def check(snapshot, typing, args):
        return command([*checker, *args], snapshot + b'\n' + typing, cwd=ROOT / 'proofs')

    def reject(name, snapshot, typing, args):
        nonlocal rejected
        result = check(snapshot, typing, args)
        assert result.returncode == 1 and b'rejected' in result.stderr, (name, result)
        rejected += 1

    cases = {}
    for name, (source, args) in {**FIXTURES, **UNFINISHED}.items():
        snapshot = success(command([exporter, 'require'], source.encode()))
        typing = produce(snapshot)
        # Even unsupported observations have independently valid input typing.
        success(command(['lake', 'env', 'lean', '--run', 'CheckTyping.lean', '--snapshot'],
                        snapshot + b'\n' + typing, cwd=ROOT / 'proofs'))
        if name in FIXTURES:
            success(check(snapshot, typing, args))
            accepted += 1
        else:
            reject(name, snapshot, typing, args)
        cases[name] = snapshot, typing, args

    s, c, args = cases['literal-equality']
    for requested in [['eq', '8', '8'], ['eq', '7', '8'], ['lt', '7', '8'],
                      ['lt', '2', '1'], ['lt', '0', '0'], ['unknown', '7', '7'],
                      ['eq', '-1', '7'], ['eq', str(2**64), str(2**64)],
                      ['eq', '1' * 21, '7']]:
        reject('wrong-request', s, c, requested)
    other, other_c, _ = cases['literal-bound']
    reject('different-valid-typing', s, other_c, args)
    reject('different-valid-snapshot', other, c, args)
    decoded = Snapshot.read(s)
    graph = list(decoded.graph) + [(18,)]
    reject('unreachable-node', snapshot_bytes(decoded, graph=graph), c, args)
    duplicate = list(decoded.graph) + [decoded.graph[decoded.term]]
    reject('equivalent-root-id', snapshot_bytes(decoded, graph=duplicate, term=len(duplicate)-1), c, args)
    # Matched FALSE requested types and head-normal terms: shape observation
    # alone passes, but fabricated typing data must not establish false truth.
    def step(rule, subject, target, premises=()):
        return dict(rule=rule, context=[], subject=subject, target=target, premises=list(premises))
    for name, graph, term, ty, steps, requested in [
        ('forged-false-equality', [(3,), (1, 0), (1, 1), (13, 1), (7, 1, 2)], 3, 4,
         [step(11, 1, 0), step(11, 2, 0), step(17, 3, 4, [0]), step(4, 4, 4, [0, 1])],
         ['eq', '0', '1']),
        ('forged-false-bound', [(3,), (1, 0), (15, 1, 1), (6, 1, 1)], 2, 3,
         [step(11, 1, 0), step(16, 2, 3), step(3, 3, 3, [0, 0])], ['lt', '0', '0']),
    ]:
        false_s = snapshot_bytes(decoded, graph=graph, term=term, ty=ty)
        false_c = encode_certificate(dict(graph=graph, termRoot=term, typeRoot=ty,
            steps=steps, typingStep=len(steps)-2, formationStep=len(steps)-1))
        reject(name, false_s, false_c, requested)
    reject('noncanonical', s + b';', c, args)
    reject('truncated-typing', s, c[:-1], args)
    print(f'closed literal evidence: {accepted} accepts, {rejected} rejections '
          '(including 3 independently typed unsupported observations)')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean --run CheckEvidence.lean')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-evidence-') as folder:
        test(shlex.split(args.compiler), shlex.split(args.checker), Path(folder))


if __name__ == '__main__':
    main()
