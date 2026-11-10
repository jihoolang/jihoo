#!/usr/bin/env python3
"""Checked original Core callers retaining scalar results across ownership binders.
Exporter/JSON association remains trusted, not implementation-refinement proof.
"""
import argparse
import copy
import json
from pathlib import Path
import tempfile
from core_scoped_graph import run, require, ROOT

from core_scalar_callers import source


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    args = parser.parse_args()
    accepted = rejected = 0
    with tempfile.TemporaryDirectory(prefix='scalar-graph-') as directory:
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
                          'CheckScalarCaller.lean'], payload, ROOT / 'proofs')
            require((result.returncode == 0) == want,
                    f'expected {want}: {result.stdout}\n{result.stderr}')
            if want:
                require(result.stdout == 'scalar-caller-graph accepted\n', 'unexpected response')
                accepted += 1
            else:
                require('scalar-caller-graph rejected:' in result.stderr,
                        f'unexpected failure path: {result.stdout}\n{result.stderr}')
                rejected += 1

        for text in (source('first', changed=True), source('first'), source('second'), source('third'), source('(int 17)'),
                     '(def run I64 (int 0))'):
            check(export(text))
        original = export(source())
        nodes = original[3]
        root = original[1]
        # Six App/Lam binders: x,y,first,z,second,third.
        bindings = []
        node = root
        for _ in range(6):
            lam, arg = nodes[node][1:]
            bindings.append((node, lam, arg))
            node = nodes[lam][3]
        terminal = node
        second_call = bindings[4][2]
        second_owner = nodes[second_call][2]
        callee = nodes[second_call][1]
        def mutation(edit):
            data = copy.deepcopy(original)
            edit(data)
            check(data, False)
        # Terminal context: third,second,z(dead),first,y(dead),x(dead).
        for slot in (2, 4, 5, 99):
            mutation(lambda s, slot=slot: s[3][terminal].__setitem__(1, slot))
        # Before second call: z,first,y,x(dead). Scalar first is not an owner.
        mutation(lambda s: s[3][second_owner].__setitem__(1, 1))
        mutation(lambda s: s[3][second_owner].__setitem__(1, 3))
        mutation(lambda s: s[3][bindings[4][1]].__setitem__(1, 1))
        mutation(lambda s: s[3][callee].__setitem__(1, 1))
        mutation(lambda s: s.__setitem__(1, s[2]))
        mutation(lambda s: s.__setitem__(2, s[1]))
        mutation(lambda s: s.__setitem__(1, len(s[3])))
        mutation(lambda s: s[3][bindings[0][1]].__setitem__(3, terminal))
        mutation(lambda s: s[3].extend([['opaque']] * (4097-len(s[3]))))
        mutation(lambda s: s.__setitem__(0, 2))
        check(original + [0], False)
        check(json.dumps(original)+' garbage', False, raw=True)
        check(' ' * (8*1024*1024+1), False, raw=True)
        print(f'scalar caller graph: {accepted} accepted, {rejected} rejected snapshots')


if __name__ == '__main__':
    main()
