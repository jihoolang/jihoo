#!/usr/bin/env python3
"""Actual structured MIR CFGs compared with admitted original Core callers.
Both native exports are trusted associations, not a compiler-refinement proof.
"""
import argparse
import copy
import json
from pathlib import Path
import tempfile
from core_scoped_graph import run, require, ROOT
from core_scalar_callers import source, bind, CALLEE


def single():
    return '(export run I64 ' + bind('x', '(Buffer 1)', '(alloc 1 (int 11))',
        bind('first', 'I64', f'(app {CALLEE} x)', 'first')) + ')'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    args = parser.parse_args()
    accepted = rejected = 0
    with tempfile.TemporaryDirectory(prefix='mir-callers-') as directory:
        tmp = Path(directory)
        probes = []
        for name in ('linear_graph', 'mir'):
            probe = tmp / name
            build = run([args.compiler, 'build', '-O0', '-I', 'compiler',
                         f'tests/core_{name}_probe.jh', '-o', probe])
            require(build.returncode == 0, build.stderr)
            probes.append(probe)

        def export(text):
            pair = []
            for probe in probes:
                output = run([probe], text)
                require(output.returncode == 0, output.stderr)
                pair.append(json.loads(output.stdout))
            return [1, pair[0], pair[1], 10000]

        def check(snapshot, want=True, raw=False):
            nonlocal accepted, rejected
            payload = snapshot if raw else json.dumps(snapshot, separators=(',', ':'))
            result = run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run',
                          'CheckMirCaller.lean'], payload, ROOT / 'proofs')
            require((result.returncode == 0) == want,
                    f'expected {want}: {result.stdout}\n{result.stderr}')
            if want:
                require(result.stdout == 'mir-caller accepted\n', 'unexpected response')
                accepted += 1
            else:
                require('mir-caller rejected:' in result.stderr,
                        f'unexpected failure path: {result.stdout}\n{result.stderr}')
                rejected += 1

        for text in (single(), *(source(result).replace('(def run', '(export run')
                     for result in ('first', 'second', 'third', '(int 77)')),
                     source('first', changed=True).replace('(def run', '(export run'),
                     '(export run I64 (int 7))'):
            check(export(text))
        original = export(single())
        fixture = json.loads((ROOT / 'tests/core_mir_single.json').read_text())
        require(original[2] == fixture,
                'actual MIR differs from complete Lean-linked canonical fixture')

        def mutation(edit):
            data = copy.deepcopy(original)
            edit(data)
            check(data, False)

        # Unsupported bounds/operations/types and invalid control edges.
        mutation(lambda s: s[2][2][2].__setitem__(1, ['goto', 999]))
        mutation(lambda s: s[2][2][2].__setitem__(1, ['goto', 2]))
        mutation(lambda s: s[2][2][0][0][0].__setitem__(0, [999, 0]))
        mutation(lambda s: s[2][1].__setitem__(3, 'i64'))
        mutation(lambda s: s[2][2][0][0][0][1].__setitem__(0, 'unsupported'))
        mutation(lambda s: s[2][2][0][0][0][1][1].__setitem__(2, 1 << 64))
        mutation(lambda s: s[2][2][0][1].__setitem__(0, 'fakeMalloc'))
        mutation(lambda s: s[2][2][0][1].__setitem__(1, ['int', 'u64', 1 << 63]))
        mutation(lambda s: s[2][2][3][1][2].append([0, 5]))
        mutation(lambda s: s[2][2][3][1][2].append([2, 999]))
        mutation(lambda s: s[2][2][1][1].__setitem__(1, ['bool', 0]))
        # An eight-byte allocation could be memory-safe here, but is not native Core's extent16.
        mutation(lambda s: s[2][2][0][1].__setitem__(1, ['int', 'u64', 8]))
        # Skip allocation initialization: the read must not invent a payload.
        mutation(lambda s: s[2][2][2].__setitem__(1, ['goto', 5]))
        # Offset1 is inside malloc16 but uninitialized; offset2 is out of bounds.
        for offset in (1, 2):
            mutation(lambda s, offset=offset: s[2][2][5][0][1][1][2].__setitem__(2, offset))
        mutation(lambda s: s[2][2][5][1].__setitem__(1, ['copy', [11, 0]]))
        mutation(lambda s: s[2][2][5][1].__setitem__(3, 5))  # use-after-free/double free
        mutation(lambda s: s[2][2][6][0][0][1].__setitem__(1, ['copy', [12, 0]]))
        # Memory-safe but wrong scalar: comparison must reject, not just validate safety.
        mutation(lambda s: s[2][2][4][0][1][1].__setitem__(1, ['int', 'i64', 44]))
        mutation(lambda s: s[2][2][6][0][0].__setitem__(1, ['use', ['int', 'i64', 77]]))
        mutation(lambda s: s.__setitem__(3, 1))
        mutation(lambda s: s.__setitem__(3, 10001))
        mutation(lambda s: s.__setitem__(0, 2))
        wrong_older = export(source('first').replace('(def run', '(export run'))
        wrong_older[2][2][-1][0][0][1] = ['use', ['copy', [35, 0]]]
        check(wrong_older, False)
        check(original + [0], False)
        check(json.dumps(original) + ' garbage', False, raw=True)
        check(' ' * (8*1024*1024+1), False, raw=True)
        print(f'MIR callers: {accepted} accepted, {rejected} rejected snapshots')


if __name__ == '__main__':
    main()
