#!/usr/bin/env python3
"""Actual Core snapshots independently admitted to mixed proof semantics."""
import argparse
from pathlib import Path
import tempfile
from core_certificate_process import command, success, ROOT
from core_typing_producer import Snapshot, encode_numbers, graph_tokens, require
from core_proof_functions import VALID


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--compiler', required=True)
    args = p.parse_args()
    with tempfile.TemporaryDirectory(prefix='mixed-proof-admission-') as tmp:
        driver = Path(tmp) / 'snapshots'
        success(command([args.compiler, 'build', '-O0', '-I', 'compiler',
                         'tests/core_typing_snapshots.jh', '-o', driver]))
        counts = {'accepted': 0, 'rejected': 0}
        def check(data, expected, name):
            r = command(['lake', 'env', 'lean', '--run', 'CheckMixedProof.lean'],
                        data, cwd=ROOT / 'proofs')
            require((r.returncode == 0) == expected, f'{name}: {r.returncode}: {r.stderr!r}')
            require((b'accepted' in r.stdout) if expected else
                    (not r.stdout and b'rejected' in r.stderr), f'{name}: fail-open output')
            counts['accepted' if expected else 'rejected'] += 1
        fixture = (ROOT / 'tests/core_preserves/lean-mixed-proof-translation.jhc').read_text()
        declarations = [s for s in fixture.splitlines() if s.startswith('(def ')]
        require(len(declarations) == 6, 'expected six proved translations')
        sources = {**VALID, **{f'generated-{i}': s for i, s in enumerate(declarations)},
                   'literal': '(def literal (Eq 7 7) (refl 7))'}
        retained = {}
        for name, source in sources.items():
            for mode in ('infer', 'require'):
                # The retained byte value is shared by all consumers. No proof
                # producer or source derivation is supplied to the Lean checker.
                data = success(command([driver, mode], source.encode()))
                parsed = Snapshot.read(data)
                require(any(n[0] in (18, 19) for n in parsed.graph), 'sort nodes filtered')
                check(data, True, name + '-' + mode)
                retained[name] = data
        excluded = {
            'non-atomic-index': '(def excluded (Eq 2 2) (app (lam n U64 (refl n)) (uadd 1 1)))',
            'erased-natural': '(def excluded (pi0 n U64 (Eq n n)) (lam0 n U64 (refl n)))',
            'conversion': '(def excluded (Eq (uadd 1 1) 2) (refl 2))',
        }
        for name, source in excluded.items():
            check(success(command([driver, 'require'], source.encode())), False, name)
        original = Snapshot.read(retained['literal'])
        def wire(graph=None, term=None, ty=None):
            return encode_numbers([3, original.term if term is None else term,
                original.type if ty is None else ty,
                *graph_tokens(original.graph if graph is None else graph)])
        check(wire(ty=original.term), False, 'proof-as-type')
        check(wire(term=len(original.graph)), False, 'out-of-range-root')
        check(wire(graph=original.graph + [(5, len(original.graph))]), False, 'unreachable-cycle')
        check(wire(graph=original.graph + [(1, 2**64)]), False, 'unreachable-overflow')
        seven = next(i for i, node in enumerate(original.graph) if node == (1, 7))
        graph = original.graph + [(1, 8), (7, seven, len(original.graph))]
        check(wire(graph=graph, ty=len(graph)-1), False, 'false-type-substitution')
        proof = Snapshot.read(retained['retain'])
        graph = list(proof.graph)
        erased = next(i for i, node in enumerate(graph) if node[0:2] == (9, 1))
        graph[erased] = (9, 0, *graph[erased][2:])
        check(encode_numbers([3, proof.term, proof.type, *graph_tokens(graph)]), False, 'erasure-tamper')
        check(encode_numbers([3, 2, 3, *graph_tokens([(1, 0), (1, 1), (13, 0), (7, 0, 1)])]), False, 'false-equality')
        check(encode_numbers([3, 1, 2, *graph_tokens([(1, 0), (15, 0, 0), (6, 0, 0)])]), False, 'false-bound')
        check(retained['literal'] + b';', False, 'trailing-data')
        check(retained['literal'][:-1], False, 'truncation')
        graph = [(3,), (0, 0), (13, 1), (7, 1, 1)]
        term, ty = 2, 3
        for _ in range(35):
            graph.append((9, 0, 0, term)); term = len(graph)-1
            graph.append((8, 0, 0, ty)); ty = len(graph)-1
        check(encode_numbers([3, term, ty, *graph_tokens(graph)]), False, 'depth-budget')
        graph = [(1, 1)]
        root = 0
        for _ in range(20):
            graph.append((16, root, root)); root = len(graph)-1
        graph.extend([(13, root), (7, root, root)])
        check(encode_numbers([3, len(graph)-2, len(graph)-1, *graph_tokens(graph)]), False, 'shared-tree-budget')
        check(retained['higher'], True, 'independent-valid-input')
    print(f'mixed proof admission: {counts}; no input program executed')


if __name__ == '__main__':
    main()
