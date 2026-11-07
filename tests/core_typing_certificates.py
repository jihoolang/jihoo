#!/usr/bin/env python3
"""Exercise actual Core.check/infer/require against independent proved DATA checks.

The driver is rebuilt against this checkout. Its complete post-call graph and
selected roots are retained once, and never replaced by an expected fixture or
producer-created arena. The untrusted producer only supplies rule data. The
Lean checker proves restricted declarative ghost typing and type formation for
accepted bytes. Compilation, exporter fidelity, Python association, and IO are
tested boundaries, not a proof that every Core.infer execution refines the model.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

from core_typing_producer import (
    Snapshot, Unsupported, encode_certificate, encode_numbers, graph_tokens,
    inspect_certificate, produce, require,
)

from core_certificate_process import ROOT, command, success
FIXTURES = {
    'lambda': '(def value (pi x U64 U64) (lam x U64 x))',
    'application': '(def value U64 (app (lam x U64 x) 7))',
    'dependent': '(def value (Eq 7 7) (app (lam x U64 (refl x)) 7))',
    'dependent-conversion': '(def value (Eq 7 7) (app (lam x U64 (refl (uadd x 1))) 6))',
    'annotations': '(def value (pi n U64 (pi xs (Array n) (Array n))) '
                   '(lam n U64 (lam xs (Array n) xs)))',
    'open-substitution': '(def value (pi n U64 (Eq n n)) '
                         '(lam n U64 (app (lam m U64 (refl m)) n)))',
    'capture': '(def value (pi n U64 (pi xs (Array n) (Array n))) '
               '(lam n U64 (app (lam m U64 (lam xs (Array m) xs)) n)))',
    'mixed': '(def value (pi n U64 (pi0 p (Eq n n) (Eq n n))) '
             '(lam n U64 (lam0 p (Eq n n) p)))',
    'beta-conversion': '(def value (Eq (app (lam x U64 x) 7) 7) (refl 7))',
    'array': '(def value (Array 2) (array (int -2) (int 5)))',
    'index': '(def value I64 (index (array (int -2) (int 5)) 1 (decide-lt 1 2)))',
    'subtract': '(def value U64 (usub 7 2 (decide-lt 2 8)))',
}
OUTSIDE = {
    'erased-u64': ('(def value (pi0 n U64 U64) (lam0 n U64 1))', 'binder mode'),
    'zeroLe': ('(def value (Lt 0 (uadd 7 1)) (zero-le 7))', 'no typing rule'),
    'nonliteral-decide': ('(def value (Lt (uadd 1 1) 3) (decide-lt (uadd 1 1) 3))',
                          'literal true endpoints'),
    'open-arithmetic': ('(def value (pi n U64 (Eq (uadd n 0) n)) '
                        '(lam n U64 (refl n)))', 'unsupported conversion'),
    'proof-irrelevance': (
        '(def value (pi n U64 (pi0 p (Lt 0 (uadd n 1)) '
        '(pi0 q (Lt 0 (uadd n 1)) (Eq (usub n 0 p) (usub n 0 q))))) '
        '(lam n U64 (lam0 p (Lt 0 (uadd n 1)) '
        '(lam0 q (Lt 0 (uadd n 1)) (refl (usub n 0 p))))))', 'unsupported conversion'),
}


def snapshot_bytes(snapshot, *, graph=None, term=None, ty=None):
    return encode_numbers([3, snapshot.term if term is None else term,
                           snapshot.type if ty is None else ty,
                           *graph_tokens(snapshot.graph if graph is None else graph)])


def association(snapshot, certificate):
    """Tested IO guard, not a theorem: compare exact graph bytes and root IDs."""
    s, c = Snapshot.read(snapshot), inspect_certificate(certificate)
    require((s.term, s.type) == (c['termRoot'], c['typeRoot']), 'selected roots changed')
    require(s.graph_bytes == encode_numbers(graph_tokens(c['graph'])), 'complete graph changed')


def changed(c, **fields):
    out = copy.deepcopy(c)
    out.update(fields)
    return out


def test(compiler, checker, output):
    output.mkdir(parents=True, exist_ok=True)
    driver = output / 'core-typing-snapshots'
    build = [*compiler, 'build', '-O2', '-I', 'compiler',
             'tests/core_typing_snapshots.jh', '-o', str(driver)]
    success(command(build))
    counts = dict(accepted=0, checker_rejected=0, association_rejected=0,
                  unsupported_actual=0, core_rejected=0)

    def lean(payload, *flags):
        return command([*checker, *flags], payload, cwd=ROOT / 'proofs')

    def accepted(snapshot, payload):
        association(snapshot, payload)
        result = lean(snapshot + b'\n' + payload, '--snapshot')
        success(result)
        assert b'accepted' in result.stdout, result
        counts['accepted'] += 1

    def rejected(name, payload):
        result = lean(payload)
        assert result.returncode == 1 and b'rejected' in result.stderr, (name, result)
        (output / f'reject-{name}.typing').write_bytes(payload)
        counts['checker_rejected'] += 1

    snapshots, certificates, records = {}, {}, []
    for fixture, source in FIXTURES.items():
        for mode in ('infer', 'require'):
            name = f'{fixture}-{mode}'
            # Run real parse/check/inference, not a Python expected-typing table.
            raw = success(command([driver, mode], source.encode()))
            path = output / f'{name}.snapshot'
            path.write_bytes(raw)
            retained = path.read_bytes()  # exactly one read for all consumers
            certificate = produce(retained)
            accepted(retained, certificate)
            snapshot = Snapshot.read(retained)
            data = inspect_certificate(certificate)
            assert len(snapshot.graph) == len(data['graph'])
            assert any(n[0] in (18, 19) for n in snapshot.graph), 'administrative sorts were filtered'
            (output / f'{name}.typing').write_bytes(certificate)
            (output / f'{name}.core').write_text(source + '\n')
            snapshots[name], certificates[name] = retained, data
            records.append(dict(name=name, nodes=len(data['graph']), steps=len(data['steps']),
                                snapshot_sha256=hashlib.sha256(retained).hexdigest(),
                                certificate_sha256=hashlib.sha256(certificate).hexdigest()))
    # Coverage facts about independently generated proof DATA, not fixture truths.
    covered = {step['rule'] for c in certificates.values() for step in c['steps']}
    assert {0, 1, 2, 4, 5, *range(10, 22), 30, 31, 33, 34, 36, 37} <= covered, covered
    assert any(step['context'] for c in certificates.values() for step in c['steps'])
    assert any(len(step['context']) >= 2 for c in certificates.values() for step in c['steps'])

    # Atomic immutable-byte association survives replacement of the path.
    source_path = output / 'retained-once.snapshot'
    source_path.write_bytes(snapshots['application-infer'])
    retained = source_path.read_bytes()
    source_path.write_bytes(snapshots['capture-require'])
    accepted(retained, produce(retained))

    # Each forged replacement is independently WELL TYPED. The formal checker
    # cannot prove which executable produced it. Only the exact-root/full-graph
    # association guard rejects substitution of a different accepted artifact.
    def substituted(name, snapshot, alternative_snapshot):
        certificate = produce(alternative_snapshot)
        success(lean(certificate))
        bound = lean(snapshot + b'\n' + certificate, '--snapshot')
        assert bound.returncode == 1 and b'rejected' in bound.stderr, (name, bound)
        try:
            association(snapshot, certificate)
        except Unsupported:
            counts['association_rejected'] += 1
        else:
            raise AssertionError(f'accepted switched artifact: {name}')

    original = snapshots['application-infer']
    s = Snapshot.read(original)
    natural = next(i for i, n in enumerate(s.graph) if n[0] == 1)
    substituted('term-root', original, snapshot_bytes(s, term=natural))
    duplicate_type = next(i for i, n in enumerate(s.graph) if n == s.graph[s.type] and i != s.type)
    substituted('same-type-different-id', original, snapshot_bytes(s, ty=duplicate_type))
    altered_graph = list(s.graph)
    sort = next(i for i, n in enumerate(altered_graph) if n[0] == 19)
    altered_graph[sort] = (19, 1)
    substituted('unreachable-administrative-sort', original, snapshot_bytes(s, graph=altered_graph))
    substituted('different-real-execution', original, snapshots['capture-require'])

    # The separately proved snapshot codec rejects malformed framing and source
    # metadata, rather than silently treating producer output as its own source.
    cert = encode_certificate(certificates['application-infer'])
    for name, bundle in (
        ('missing-separator', original + cert),
        ('extra-separator', original + b'\n\n' + cert),
        ('trailing-newline', original + b'\n' + cert + b'\n'),
        ('wrong-snapshot-schema', encode_numbers([2]) + original.split(b';', 1)[1] + b'\n' + cert),
        ('snapshot-root-range', snapshot_bytes(s, term=len(s.graph)) + b'\n' + cert),
        ('snapshot-noncanonical', b'110;' + original.split(b';', 1)[1] + b'\n' + cert),
    ):
        result = lean(bundle, '--snapshot')
        assert result.returncode == 1 and b'rejected' in result.stderr, (name, result)
        counts['checker_rejected'] += 1
        (output / f'reject-bound-{name}.bundle').write_bytes(bundle)

    base = certificates['capture-require']
    # Wrong conclusions, different rules and contexts, and topological corruption.
    for label, fields in (
        ('term-root', dict(termRoot=len(base['graph']))),
        ('type-root', dict(typeRoot=len(base['graph']))),
        ('typing-step', dict(typingStep=len(base['steps']))),
        ('formation-step', dict(formationStep=len(base['steps']))),
        ('formation-is-typing', dict(formationStep=base['typingStep'])),
        ('typing-is-formation', dict(typingStep=base['formationStep'])),
        ('sort-is-type', dict(typeRoot=next(i for i, n in enumerate(base['graph']) if n[0] == 19))),
    ):
        rejected(label, encode_certificate(changed(base, **fields)))
    for label, selector, edit in (
        ('unknown-rule', lambda s: True, lambda s, _: s.update(rule=999)),
        ('missing-premise', lambda s: bool(s['premises']), lambda s, _: s['premises'].pop()),
        ('future-premise', lambda s: bool(s['premises']), lambda s, i: s['premises'].__setitem__(0, i)),
        ('variable-context', lambda s: s['rule'] == 10, lambda s, _: s.update(context=[])),
        ('context-limit', lambda s: True, lambda s, _: s.update(context=[0] * 129)),
        ('premise-limit', lambda s: True, lambda s, _: s.update(premises=[0] * 4097)),
        ('wrong-subject', lambda s: s['rule'] == 19, lambda s, _: s.update(subject=base['typeRoot'])),
        ('wrong-target', lambda s: s['rule'] == 19, lambda s, _: s.update(target=base['termRoot'])),
    ):
        c = copy.deepcopy(base)
        i = next(i for i, step in enumerate(c['steps']) if selector(step))
        edit(c['steps'][i], i)
        rejected(label, encode_certificate(c))
    c = copy.deepcopy(base)
    c['steps'] += [copy.deepcopy(c['steps'][0])] * (4097 - len(c['steps']))
    rejected('step-limit', encode_certificate(c))
    c = copy.deepcopy(base)
    c['graph'] += [(3,)] * (4097 - len(c['graph']))
    rejected('graph-limit', encode_certificate(c))
    for tag, label in ((9, 'lambda-mode'), (8, 'pi-mode')):
        c = copy.deepcopy(base)
        i = next(i for i, node in enumerate(c['graph']) if node[0] == tag)
        node = c['graph'][i]
        c['graph'][i] = (tag, 1 - node[1], *node[2:])
        rejected(label, encode_certificate(c))
    # Change every U64 lambda/Pi mode together: this is more than a disagreement
    # between syntax and claimed type; the fragment forbids erased U64 binders.
    c = copy.deepcopy(certificates['lambda-require'])
    c['graph'] = [(n[0], 1, *n[2:]) if n[0] in (8, 9) else n for n in c['graph']]
    rejected('coordinated-erased-u64', encode_certificate(c))
    c = copy.deepcopy(certificates['annotations-require'])
    i = next(i for i, n in enumerate(c['graph']) if n[0] == 5)
    c['graph'][i] = (5, next(j for j, n in enumerate(c['graph'][:i]) if n == (3,)))
    rejected('ill-typed-annotation', encode_certificate(c))
    c = copy.deepcopy(certificates['capture-require'])
    i = next(i for i, n in enumerate(c['graph']) if n == (0, 1))
    c['graph'][i] = (0, 0)
    rejected('captured-open-variable', encode_certificate(c))
    for name, rule in (('dependent-conversion-require', 34), ('beta-conversion-require', 33)):
        c = copy.deepcopy(certificates[name])
        step = next(step for step in c['steps'] if step['rule'] == rule)
        step['target'] = step['subject']
        rejected(f'false-conversion-{rule}', encode_certificate(c))
    c = copy.deepcopy(certificates['dependent-conversion-require'])
    step = next(step for step in c['steps'] if step['rule'] == 34)
    step['context'] = [next(i for i, n in enumerate(c['graph']) if n == (3,))]
    rejected('conversion-context', encode_certificate(c))
    c = copy.deepcopy(certificates['dependent-conversion-require'])
    step = next(step for step in c['steps'] if step['rule'] == 34)
    step['rule'] = 30
    rejected('equality-is-not-conversion-evidence', encode_certificate(c))

    # Every additional step below is a valid conversion reflexivity witness,
    # but repeatedly unfolding its shared DAG would exceed the aggregate work
    # budget. Resource rejection is not hidden behind an ill-typed extra step.
    c = copy.deepcopy(certificates['application-infer'])
    leaf = next(i for i, n in enumerate(c['graph']) if n[0] == 1)
    for _ in range(13):
        c['graph'].append((16, leaf, leaf))
        leaf = len(c['graph']) - 1
    c['steps'] += [dict(rule=30, context=[], subject=leaf, target=leaf, premises=[])
                   for _ in range(100)]
    rejected('aggregate-expansion-budget', encode_certificate(c))

    # Reusing one premise repeats equality of its entire context. These unused
    # open steps are valid model claims; the selected conclusion remains closed.
    # Merely budgeting each step's decoded roots misses this repeated work.
    def repeated_premise_work(width, doublings):
        graph = [(4,), (2, 0, 0), (1, width), (5, 2),
                 (11, *([1] * width)), (1, 0)]
        root = 5
        for _ in range(doublings):
            graph.append((16, root, root))
            root = len(graph) - 1
        context = [root] * 7
        return dict(graph=graph, termRoot=1, typeRoot=0, typingStep=1, formationStep=0,
                    steps=[
                        dict(rule=1, context=[], subject=0, target=0, premises=[]),
                        dict(rule=12, context=[], subject=1, target=0, premises=[]),
                        dict(rule=12, context=context, subject=1, target=0, premises=[]),
                        dict(rule=15, context=context, subject=4, target=3,
                             premises=[2] * width),
                    ])

    success(lean(encode_certificate(repeated_premise_work(1, 15))))
    rejected('repeated-premise-work-budget',
             encode_certificate(repeated_premise_work(256, 16)))

    good = encode_certificate(certificates['application-infer'])
    for name, payload in (
        ('empty', b''), ('truncated', good[:-1]), ('trailing', good + b';'),
        ('whitespace', good + b'\n'), ('invalid-byte', b'\xff' + good),
        ('wrong-schema', encode_numbers([3]) + good.split(b';', 1)[1]),
        ('noncanonical', b'010;' + good.split(b';', 1)[1]),
        ('number-limit', b'1' * 65 + b';' + good.split(b';', 1)[1]),
        ('file-limit', good + b';' * (8 * 1024 * 1024)),
    ):
        rejected(name, payload)
    for name, graph in (
        ('graph-depth', [(3,)] + [(5, i) for i in range(129)]),
        ('graph-expansion', [(3,)] + [(10, i, i) for i in range(19)]),
        ('child-vector-limit', [(3,), (11, *([0] * 4097))]),
        ('forward-child', [(5, 1), (3,)]),
        ('self-child', [(5, 0)]),
        ('unsupported-graph-tag', [(99,)]),
        ('integer-range', [(2, 0, 2**63)]),
        ('negative-zero', [(2, 1, 0)]),
        ('bad-binder-flag', [(3,), (9, 2, 0, 0)]),
        ('variable-range', [(0, 2**32)]),
        ('universe-range', [(19, 33)]),
    ):
        rejected(name, encode_certificate(changed(certificates['application-infer'], graph=graph)))

    # A successful actual Core check is deliberately INSUFFICIENT. These real
    # accepted inputs use rules beyond the model. The producer fails closed;
    # a direct fabricated natural-typing derivation cannot bypass the checker.
    for name, (source, explanation) in OUTSIDE.items():
        raw = success(command([driver, 'require'], source.encode()))
        s = Snapshot.read(raw)
        (output / f'outside-{name}.snapshot').write_bytes(raw)
        try:
            produce(raw)
        except Unsupported as error:
            assert explanation in str(error), (name, error)
        else:
            raise AssertionError(f'produced unsupported actual typing: {name}')
        counts['unsupported_actual'] += 1
        forged = dict(graph=s.graph, termRoot=s.term, typeRoot=s.type,
                      typingStep=0, formationStep=1, steps=[
                          dict(rule=11, context=[], subject=s.term, target=s.type, premises=[]),
                          dict(rule=0, context=[], subject=s.type, target=s.type, premises=[]),
                      ])
        rejected(f'unsupported-actual-{name}', encode_certificate(forged))
    for name, source in (
        ('wrong-result', '(def value I64 7)'),
        ('unbound', '(def value U64 missing)'),
        ('false-decide', '(def value (Lt 2 1) (decide-lt 2 1))'),
        ('invalid-mode', FIXTURES['lambda']),
    ):
        result = command([driver, 'unexpected' if name == 'invalid-mode' else 'require'], source.encode())
        assert result.returncode == 1 and not result.stdout, (name, result)
        counts['core_rejected'] += 1
    manifest = dict(
        boundary='Source hashes are provenance only, not proof of execution/export fidelity.',
        build=build, checker=checker, results=counts, fixtures=records,
        sources={name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in (
            'compiler/core.jh', 'compiler/core_parse.jh', 'tests/core_typing_snapshots.jh',
            'tests/core_typing_producer.py', 'tests/core_typing_certificates.py')})
    (output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print('actual Core typing: ' + ', '.join(f'{value} {name}' for name, value in counts.items()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default=os.environ.get('JIHOO_COMPILER', 'jihoo'))
    parser.add_argument('--checker', default='lake env lean --run CheckTyping.lean')
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    compiler, checker = shlex.split(args.compiler), shlex.split(args.checker)
    if '/' in compiler[0]:
        compiler[0] = str((ROOT / compiler[0]).resolve())
    if args.output_dir:
        test(compiler, checker, args.output_dir.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='jihoo-typing-certificates-') as folder:
            test(compiler, checker, Path(folder))


if __name__ == '__main__':
    main()
