#!/usr/bin/env python3
"""Checked original Core caller snapshots against finite linear translation.
Exporter/JSON association remains trusted, not implementation-refinement proof.
"""
import argparse
import copy
import json
from pathlib import Path
import tempfile
from core_scoped_graph import run, require, ROOT

CALLEE = '''(lam xs (Buffer 1) (lend xs
 (lam r (Ref (Buffer 1)) (index r 0 (decide-lt 0 1)))
 (lam a I64 (lam y (Buffer 1) (free y a)))))'''


def bind(name, ty, value, body):
    return f'(app (lam {name} {ty} {body}) {value})'


def source(order=(0, 1), interleave=False):
    body = '(int 17)'
    names = ['x', 'y', 'z'] if interleave else ['x', 'y']
    for i in reversed(order):
        body = bind(f'result{i}', 'I64', f'(app {CALLEE} {names[i]})', body)
        if interleave and i == order[1]:
            body = bind('z', '(Buffer 1)', '(alloc 1 (int 42))', body)
    body = bind('y', '(Buffer 1)', '(alloc 1 (int 42))', body)
    body = bind('x', '(Buffer 1)', '(alloc 1 (int 42))', body)
    return f'(def run I64 {body})'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    args = parser.parse_args()
    accepted = rejected = 0
    with tempfile.TemporaryDirectory(prefix='linear-graph-') as directory:
        probe = Path(directory) / 'probe'
        build = run([args.compiler, 'build', '-O0', '-I', 'compiler',
                     'tests/core_linear_graph_probe.jh', '-o', probe])
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
                          'CheckLinearCaller.lean'], payload, ROOT / 'proofs')
            require((result.returncode == 0) == want,
                    f'expected {want}: {result.stdout}\n{result.stderr}')
            if want:
                require(result.stdout == 'linear-caller-graph accepted\n', 'unexpected response')
                accepted += 1
            else:
                require('linear-caller-graph rejected:' in result.stderr,
                        f'unexpected failure path: {result.stdout}\n{result.stderr}')
                rejected += 1

        for text in (source(), source((1, 0)), source((0, 1, 2), True),
                     source((1, 2, 0), True), '(def run I64 (int 0))'):
            check(export(text))
        original = export(source())
        nodes = original[3]
        root = original[1]
        first_lam = nodes[root][1]
        first_alloc = nodes[root][2]
        body = nodes[first_lam][3]
        second_lam = nodes[body][1]
        call_bind = nodes[second_lam][3]
        call = nodes[call_bind][2]
        owner_var = nodes[call][2]
        callee = nodes[call][1]
        next_bind = nodes[nodes[call_bind][1]][3]
        next_call = nodes[next_bind][2]
        next_owner_var = nodes[next_call][2]
        integer = nodes[first_alloc][2]
        length = nodes[first_alloc][1]

        def mutation(edit):
            data = copy.deepcopy(original)
            edit(data)
            check(data, False)

        mutation(lambda s: s.__setitem__(1, s[2]))
        mutation(lambda s: s.__setitem__(2, s[1]))
        mutation(lambda s: s.__setitem__(1, len(s[3])))
        mutation(lambda s: s[3][first_lam].__setitem__(1, 1))
        mutation(lambda s: s[3][first_lam].__setitem__(2, s[2]))
        mutation(lambda s: s[3][second_lam].__setitem__(1, 1))
        mutation(lambda s: s[3][owner_var].__setitem__(1, 99))
        mutation(lambda s: s[3][callee].__setitem__(1, 1))
        mutation(lambda s: s[3][length].__setitem__(1, 2))
        mutation(lambda s: s[3][integer].__setitem__(1, 1 << 63))
        mutation(lambda s: s[3][first_alloc].__setitem__(2, first_alloc))
        mutation(lambda s: s[3].__setitem__(first_alloc, ['opaque']))
        mutation(lambda s: s[3][first_lam].__setitem__(3, integer))  # leaked owner
        mutation(lambda s: s[3][owner_var].__setitem__(1, 0))  # consumes y twice
        mutation(lambda s: s[3][next_owner_var].__setitem__(1, 2))  # x tombstone, not live y
        mutation(lambda s: s[3][next_owner_var].__setitem__(1, 0))  # scalar result is not owner
        padded = copy.deepcopy(original)
        padded[3].extend([['opaque']] * (4096 - len(padded[3])))
        check(padded)
        padded[3][callee][1] = 1
        check(padded, False)  # bounded rejection even with many candidate IDs
        mutation(lambda s: s.__setitem__(0, 2))
        mutation(lambda s: s[3].extend([['opaque']] * (4097 - len(s[3]))))
        mutation(lambda s: s[3].append(['natural', 1 << 64]))
        mutation(lambda s: s[3].append(['alloc', len(s[3]), 0]))
        check(original + [0], False)
        check(json.dumps(original) + ' garbage', False, raw=True)
        check('[' * 9 + ']' * 9, False, raw=True)
        check(' ' * (8 * 1024 * 1024 + 1), False, raw=True)
        # Native acceptance does not imply support by this bounded fragment.
        check(export(source().replace('(int 42)', '(int -1)')), False)
        check(export(source().replace('(int 17)', '(add (int 8) (int 9))')), False)
        print(f'linear caller graph: {accepted} accepted, {rejected} rejected snapshots')


if __name__ == '__main__':
    main()
