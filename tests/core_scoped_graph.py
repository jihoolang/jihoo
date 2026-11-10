#!/usr/bin/env python3
"""Original checked Core snapshots against the bounded scoped-Lend translator.
The exporter/JSON association is tested and trusted, not formally refined.
"""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
READ = '(index r 0 (decide-lt 0 1))'
OWNER_READ = '(index (borrow xs) 0 (decide-lt 0 1))'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def source(reader, continuation='(free y a)', length=1):
    return f'''(def f (pi xs (Buffer {length}) I64)
 (lam xs (Buffer {length})
  (lend xs (lam r (Ref (Buffer {length})) {reader})
   (lam a I64 (lam y (Buffer {length}) {continuation})))))'''


def run(argv, payload='', cwd=ROOT):
    return subprocess.run(list(map(str, argv)), input=payload, capture_output=True,
                          text=True, cwd=cwd, timeout=180)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    args = parser.parse_args()
    accepted = rejected = 0
    with tempfile.TemporaryDirectory(prefix='scoped-graph-') as directory:
        probe = Path(directory) / 'probe'
        build = run([args.compiler, 'build', '-O0', '-I', 'compiler',
                     'tests/core_scoped_graph_probe.jh', '-o', probe])
        require(build.returncode == 0, build.stderr)

        def export(text):
            output = run([probe], text)
            require(output.returncode == 0, output.stderr)
            snapshot = json.loads(output.stdout)
            require(snapshot[0] == 1 and len(snapshot) == 4, 'export schema')
            return snapshot

        def check(snapshot, want=True, raw=False):
            nonlocal accepted, rejected
            payload = snapshot if raw else json.dumps(snapshot, separators=(',', ':'))
            result = run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run',
                          'CheckScopedLend.lean'], payload, ROOT / 'proofs')
            require((result.returncode == 0) == want,
                    f'expected {want}: {result.stdout}\n{result.stderr}')
            if want:
                require(result.stdout == 'scoped-lend-graph accepted\n', 'unexpected response')
                accepted += 1
            else:
                require('scoped-lend-graph rejected:' in result.stderr, 'unexpected failure path')
                rejected += 1

        readers = [READ, OWNER_READ, '(int 42)',
                   f'(app (lam ignored I64 {READ}) (int 3))',
                   f'(app (lam ignored I64 {OWNER_READ}) (int 3))',
                   f'(if-lt 0 1 q {READ} (int 7))',
                   f'(if-lt 1 0 q (int 7) {OWNER_READ})',
                   f'(app (lam ignored I64 (if-lt 0 1 q {OWNER_READ} {READ})) {READ})']
        for reader in readers:
            for cont in ('(free y a)', '(free xs a)',
                         '(free (store y 0 a (decide-lt 0 1)) a)'):
                check(export(source(reader, cont)))
        original = export(source(READ))
        nodes = original[3]
        root = original[1]
        lend = nodes[root][3]
        reader_lam = nodes[lend][2]
        reader_root = nodes[reader_lam][3]
        result_lam = nodes[lend][3]
        owner_lam = nodes[result_lam][3]
        rest = nodes[owner_lam][3]
        var = nodes[reader_root][1]
        proof = nodes[reader_root][3]

        def mutation(edit):
            data = copy.deepcopy(original)
            edit(data)
            check(data, False)

        mutation(lambda s: s.__setitem__(1, s[2]))  # type is not a term root
        mutation(lambda s: s.__setitem__(2, s[1]))
        mutation(lambda s: s.__setitem__(1, len(s[3])))
        mutation(lambda s: s[3][root].__setitem__(1, 1))
        mutation(lambda s: s[3][reader_lam].__setitem__(1, 1))
        mutation(lambda s: s[3][reader_lam].__setitem__(2, s[3][result_lam][2]))
        mutation(lambda s: s[3][result_lam].__setitem__(2, s[3][root][2]))
        mutation(lambda s: s[3][owner_lam].__setitem__(1, 1))
        mutation(lambda s: s[3][var].__setitem__(1, 99))
        mutation(lambda s: s[3][reader_root].__setitem__(1, reader_root))
        mutation(lambda s: s[3][proof].__setitem__(2, s[3][proof][1]))
        mutation(lambda s: s[3][rest].__setitem__(2, s[3][rest][1]))
        mutation(lambda s: s[3].append(['integer', 1 << 63]))
        mutation(lambda s: s[3].append(['natural', 1 << 64]))
        mutation(lambda s: s[3].append(['index', len(s[3]), 0, 0]))
        mutation(lambda s: s.__setitem__(0, 2))
        mutation(lambda s: s[3][root].__setitem__(1, 2))
        check(original + [0], False)
        check(json.dumps(original) + ' garbage', False, raw=True)
        check('[' * 9 + ']' * 9, False, raw=True)
        check(' ' * (8 * 1024 * 1024 + 1), False, raw=True)

        # Native checking is insufficient for this deliberately bounded subset.
        for text in (source('(int -1)'), source('(app (lam n I64 n) (int 3))'),
                     source('(int 7)', length=2),
                     source('(if-lt 0 1 q (int 7) (int -1))')):
            check(export(text), False)

        # Well-formed shared DAG: expansion budget counts occurrences, not IDs.
        def dag(levels):
            s = copy.deepcopy(original)
            node = reader_root
            for _ in range(levels):
                s[3].append(['strict', node, node])
                node = len(s[3]) - 1
            s[3].append(['lam', 0, s[3][reader_lam][2], node])
            reader = len(s[3]) - 1
            s[3].append(['lend', s[3][lend][1], reader, result_lam])
            body = len(s[3]) - 1
            s[3].append(['lam', 0, s[3][root][2], body])
            s[1] = len(s[3]) - 1
            return s
        check(dag(8))  # 511 reader nodes
        check(dag(9), False)  # 1023 occurrences exceed budget
        check(dag(33), False)  # depth rejection before expansion
        print(f'scoped graph: {accepted} accepted, {rejected} rejected snapshots')


if __name__ == '__main__':
    main()
