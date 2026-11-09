#!/usr/bin/env python3
"""Read-once actual-Core snapshots checked independently by Lean inference."""
import argparse
from pathlib import Path
import tempfile
from core_certificate_process import command, success, ROOT
from core_typing_producer import Snapshot, encode_numbers, graph_tokens, require


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--compiler', required=True)
    args = p.parse_args()
    with tempfile.TemporaryDirectory(prefix='mixed-raw-') as tmp:
        driver = Path(tmp) / 'snapshots'
        success(command([args.compiler, 'build', '-O0', '-I', 'compiler',
                         'tests/core_typing_snapshots.jh', '-o', driver]))
        def check(data, expected, name):
            r = command(['lake', 'env', 'lean', '--run', 'CheckMixedRaw.lean'],
                        data, cwd=ROOT / 'proofs')
            require((r.returncode == 0) == expected, f'{name}: {r.returncode}: {r.stderr!r}')
            require((b'accepted' in r.stdout) if expected else
                    (not r.stdout and b'rejected' in r.stderr), f'{name}: fail-open output')
        accepted = {'natural', 'integer', 'elements', 'decide', 'reflexivity',
                    'array-index', 'lambda', 'application', 'proof-let'}
        rows = [line.split('\t') for line in (ROOT / 'tests/core_mixed_inference.tsv').read_text().splitlines()
                if not line.startswith('#')]
        retained = {}
        for name, _, core, _, source in rows:
            if core != 'true':
                continue
            for mode in ('infer', 'require'):
                data = success(command([driver, mode], source.encode()))
                # Retain the exact bytes once; all validation uses this value.
                snapshot = Snapshot.read(data)
                require(any(n[0] in (18, 19) for n in snapshot.graph), 'sort nodes removed')
                check(data, name in accepted, name + '-' + mode)
                retained[name] = data
        original = Snapshot.read(retained['reflexivity'])
        def changed(graph=None, term=None, ty=None):
            return encode_numbers([3, original.term if term is None else term,
                original.type if ty is None else ty,
                *graph_tokens(original.graph if graph is None else graph)])
        check(changed(ty=original.term), False, 'proof-as-type-root')
        check(changed(term=len(original.graph)), False, 'root-outside-graph')
        check(changed(graph=original.graph + [(5, len(original.graph))]), False, 'unreachable-self-edge')
        check(changed(graph=original.graph + [(1, 2**64)]), False, 'unreachable-overflow')
        check(retained['reflexivity'] + b';', False, 'trailing-data')
        check(retained['reflexivity'][:-1], False, 'truncation')
        # Different valid snapshots are rechecked, not incorrectly bound to an
        # unrelated previous request. No separate certificate is accepted here.
        check(retained['natural'], True, 'independent-valid-snapshot')
        # A valid graph containing a shared tree whose expansion exceeds bounds.
        graph = [(1, 1), (3,)]
        root = 0
        for _ in range(20):
            graph.append((16, root, root)); root = len(graph) - 1
        check(encode_numbers([3, root, 1, *graph_tokens(graph)]), False, 'repeated-reference-work')
        # The result type is correct: failure isolates the smaller admission
        # depth limit rather than an unrelated type mismatch.
        graph = [(3,), (0, 0), (13, 1), (7, 1, 1)]
        root, ty = 2, 3
        for _ in range(35):
            graph.append((9, 0, 0, root)); root = len(graph) - 1
            graph.append((8, 0, 0, ty)); ty = len(graph) - 1
        check(encode_numbers([3, root, ty, *graph_tokens(graph)]), False, 'admission-depth')
        graph = [(2, 0, 0), (11, *([0] * 512)), (1, 512), (5, 2)]
        check(encode_numbers([3, 1, 3, *graph_tokens(graph)]), False, 'admission-tree-budget')
    print('mixed raw admission: 26 actual snapshots, 10 defensive/independent checks; no input executed')


if __name__ == '__main__':
    main()
