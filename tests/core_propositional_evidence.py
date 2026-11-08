#!/usr/bin/env python3
"""Actual Core correspondence for closed propositions and higher-order proof assumptions."""
from __future__ import annotations
import argparse
from pathlib import Path
import shlex
import tempfile
from core_certificate_process import ROOT, command, success
from core_typing_producer import Snapshot, Unsupported, require
from core_typing_certificates import snapshot_bytes
from core_principal_evidence import PrincipalChecker

P, Q, R, FALSE = '(Eq 7 7)', '(Lt 0 8)', '(Eq 9 9)', '(Eq 0 1)'
def arrow(a, b):
    return f'(pi0 ignored {a} {b})'
def definition(ty, value):
    return f'(def value {ty} {value})'

FIXTURES = {
    'identity': definition(arrow(P, P), f'(lam0 p {P} p)'),
    'false-identity': definition(arrow(FALSE, FALSE), f'(lam0 p {FALSE} p)'),
    'weaken': definition(arrow(P, arrow(FALSE, P)), f'(lam0 p {P} (lam0 unused {FALSE} p))'),
    'modus-ponens': definition(arrow(arrow(P, Q), arrow(P, Q)),
        f'(lam0 f {arrow(P,Q)} (lam0 p {P} (app f p)))'),
    'composition': definition(arrow(arrow(P,Q), arrow(arrow(Q,R), arrow(P,R))),
        f'(lam0 f {arrow(P,Q)} (lam0 g {arrow(Q,R)} (lam0 p {P} (app g (app f p)))))'),
    'identity-applied': definition(P, f'(app (lam0 p {P} p) (refl 7))'),
    'higher-order-applied': definition(P,
        f'(app (app (lam0 f {arrow(P,P)} (lam0 p {P} (app f p))) (lam0 p {P} p)) (refl 7))'),
    'quantified-assumption': definition(arrow('(pi n U64 (Eq n n))', '(Eq 3 3)'),
        '(lam0 f (pi n U64 (Eq n n)) (app f 3))'),
    'false-quantified-assumption': definition(arrow('(pi n U64 (Eq n 0))', '(Eq 1 0)'),
        '(lam0 f (pi n U64 (Eq n 0)) (app f 1))'),
    'quantified-applied': definition('(Eq 7 7)',
        '(app (lam0 f (pi n U64 (Eq n n)) (app f 7)) (lam n U64 (refl n)))'),
    'closed-function-under-proof': definition(arrow(FALSE, '(pi n U64 (Eq n n))'),
        f'(lam0 unused {FALSE} (lam n U64 (refl n)))'),
    'wide-closed-principal': definition('(Lt 0 (uadd 18446744073709551615 1))',
        '(zero-le 18446744073709551615)'),
    'converted-proof-argument': definition('(Eq 5 5)',
        '(app (lam0 p (Eq 5 5) p) (refl (uadd 2 3)))'),
    'converted-request': definition('(pi0 p (Eq (uadd 2 3) 5) (Eq 5 (uadd 3 2)))',
        '(lam0 p (Eq 5 5) p)'),
}
OUTSIDE = {
    'mixed-scalar-proof-context': definition('(pi n U64 (pi0 p (Eq n n) (Eq n n)))',
        '(lam n U64 (lam0 p (Eq n n) p))'),
    'proof-dependent-scalar-lambda': definition(arrow(P, '(pi n U64 (Eq 7 7))'),
        f'(lam0 p {P} (lam n U64 p))'),
    'erased-natural-index': definition('(pi0 n U64 (Eq n n))', '(lam0 n U64 (refl n))'),
    'runtime-function-argument': definition('(Eq 7 7)',
        '(app (lam f (pi n U64 U64) (refl (app f 7))) (lam n U64 n))'),
    # Core normalizes the Pi before application. This profile does not replace
    # the actual inferred root with a convertible modeled result. PR #90's
    # retained normalization observations cover the corresponding scalar case.
    'normalized-pi-changes-substitution': definition('(Eq 8 8)',
        '(app (lam n U64 (refl (uadd 1 n))) 7)'),
}
INVALID = {
    'false-premise-not-provided': definition(FALSE, f'(app (lam0 p {FALSE} p) (refl 0))'),
    'wrong-hypothesis': definition(arrow(P,Q), f'(lam0 p {P} p)'),
    'unbound-proof': definition(P, 'p'),
    'non-erased-proof': definition(arrow(P,P), f'(lam p {P} p)'),
    'proof-used-as-index': definition(arrow(P,P), f'(lam0 p {P} (refl p))'),
}


def test(compiler, checker, output, existing_exporter=None):
    exporter = existing_exporter or output / 'snapshot'
    if existing_exporter is None:
        success(command([*compiler, 'build', '-O2', '-I', 'compiler', 'tests/core_typing_snapshots.jh',
                         '-o', exporter]))
    gate = PrincipalChecker(exporter, checker)
    cases, delivered = {}, []
    for name, source in FIXTURES.items():
        try:
            cases[name] = gate.generate(source.encode(), consumer=delivered.append)
        except Unsupported as error:
            raise Unsupported(f'{name}: {error}') from error
        require(delivered[-1] == b'\n'.join(cases[name]), 'retained pair changed')
    rb, ib = cases['identity']
    r, i = map(Snapshot.read, (rb, ib))
    rejected = 0
    def reject(name, pair, selected=None):
        nonlocal rejected
        rr, ii = map(Snapshot.read, pair)
        roots = selected or [rr.term, rr.type, ii.type]
        result = gate.validate(*pair, *roots)
        require(result.returncode == 1 and b'rejected' in result.stderr, f'{name}: {result}')
        rejected += 1
    for k in range(3):
        roots = [r.term, r.type, i.type]; roots[k] += 1
        reject(f'wrong-root-{k}', (rb, ib), roots)
    reject('different-valid-inference', (rb, cases['false-identity'][1]))
    extended = [snapshot_bytes(s, graph=[*s.graph, (18,)]) for s in [r,i]]
    success(gate.validate(*extended, r.term, r.type, i.type))
    extended[1] = snapshot_bytes(i, graph=[*i.graph, (19,0)])
    reject('changed-unreachable-node', extended)
    # Two distinct hypotheses. Every edge is backward and both body variables
    # exist before either lambda. Replacing Var 0 by Var 1 must change the
    # inferred result, even though both propositions are true.
    graph = [(1,0), (1,1), (7,0,0), (6,0,1), (0,0), (0,1),
             (9,1,3,4), (9,1,2,6), (8,1,3,3), (8,1,2,8),
             (8,1,3,2), (8,1,2,10)]
    def pair(arena, term=7, ty=9):
        artifact = snapshot_bytes(r, graph=arena, term=term, ty=ty)
        Snapshot.read(artifact)
        return artifact, artifact
    control = pair(graph)
    success(gate.validate(*control, 7, 9, 9))
    changed = list(graph); changed[6] = (9,1,3,5)
    reject('graph-valid-wrong-hypothesis-slot', pair(changed))
    repaired = pair(changed, ty=11)
    success(gate.validate(*repaired, 7, 11, 11))
    reject('unbound-top-level-hypothesis', pair(graph, term=4, ty=3))
    # A genuine closed proof with its correct inferred type cannot authorize
    # a false requested proposition, even in a completely graph-valid bundle.
    literal_graph = [(1,0), (1,1), (13,0), (7,0,0), (7,0,1)]
    good = snapshot_bytes(r, graph=literal_graph, term=2, ty=3)
    bad = snapshot_bytes(r, graph=literal_graph, term=2, ty=4)
    success(gate.validate(good, good, 2, 3, 3))
    reject('closed-false-request-with-correct-inference', (bad, good))
    reject('swapped-well-formed-inferred-arrow',
           (control[0], snapshot_bytes(r, graph=graph, term=7, ty=11)))
    rr, ii = map(Snapshot.read, cases['converted-request'])
    require(rr.type != ii.type, 'distinct requested and inferred types required')
    reject('convertible-but-not-exact-inference',
           (cases['converted-request'][0], snapshot_bytes(ii, ty=rr.type)))
    # Repeated references are charged for every instantiated body occurrence.
    # Each substitution passes alone; seven chained calls pass and eight fail.
    graph = []
    def node(*fields):
        graph.append(fields)
        return len(graph)-1
    u = node(3); variable = node(0,0); summed = variable
    for _ in range(6):
        summed = node(16,summed,summed)
    eq = node(7,summed,summed); proof = node(13,summed)
    types, functions = [eq], [proof]
    for _ in range(12):
        types.append(node(8,0,u,types[-1]))
        functions.append(node(9,0,u,functions[-1]))
    arg = node(1,0)
    for _ in range(3):
        arg = node(16,arg,arg)
    apps = [functions[12]]
    for _ in range(8):
        apps.append(node(10,apps[-1],arg))
    singles = [node(10,functions[12-k],arg) for k in range(8)]
    for k, application in enumerate(singles):
        single = pair(graph, term=application, ty=types[11-k])
        success(gate.validate(*single, application, types[11-k], types[11-k]))
    prefix = pair(graph, term=apps[7], ty=types[5])
    success(gate.validate(*prefix, apps[7], types[5], types[5]))
    reject('cumulative-substitution-budget', pair(graph, term=apps[8], ty=types[4]))
    for name, source in OUTSIDE.items():
        pair_bytes = success(command([exporter, 'both'], source.encode())).split(b'\n')
        reject(f'actual-core-outside-{name}', pair_bytes)
    for name, source in INVALID.items():
        result = command([exporter, 'both'], source.encode())
        require(result.returncode != 0 and not result.stdout, f'{name}: invalid source exported')
        diagnostic = {'unbound-proof': b'unknown name or invalid U64 literal: p',
                      'non-erased-proof': b'proof binders must be erased'}.get(name, b'type mismatch')
        require(diagnostic in result.stderr, f'{name}: wrong diagnostic {result.stderr}')
    # Failure gates reuse the production process boundary, not removable asserts.
    failed = output / 'failed-exporter'
    failed.write_bytes(b"#!/bin/sh\nprintf '%s' '" + rb + b'\n' + ib + b"'\nexit 1\n")
    failed.chmod(0o755)
    class Invalid(PrincipalChecker):
        def obtain(self, source):
            return b'\n'.join(pair([(1,0),(1,1),(7,0,1),(0,0)], term=3, ty=2))
    for blocked in [PrincipalChecker(failed, checker), Invalid(exporter, checker)]:
        try:
            blocked.generate(b'ignored', consumer=delivered.append)
        except Unsupported:
            pass
        else:
            raise AssertionError('failed result published')
        require(blocked.published == 0 and len(delivered) == len(cases), 'failed operation delivered')
    print(f'propositional evidence: {len(cases)} actual-Core proofs, {rejected} artifact/profile '
          f'rejections, {len(INVALID)} source rejections, repaired graph controls and publication gates')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean --run CheckPropositionalEvidence.lean')
    parser.add_argument('--exporter', type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-propositions-') as folder:
        test(shlex.split(args.compiler), shlex.split(args.checker), Path(folder), args.exporter)

if __name__ == '__main__':
    main()
