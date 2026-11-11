#!/usr/bin/env python3
"""Checked native Core -> exact constructor view -> Lean fixture association.
Closed native applications test lifecycle behavior empirically; they do not
verify an external Data ABI or refine abstract empty/cells.
"""
import argparse
import ctypes
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

from core_owned_call import COUNTER
from core_scoped_lend import command, require

ROOT = Path(__file__).resolve().parents[1]
FAMILY = '(data Tree (Nil Tree) (Node (pi left Tree (pi right Tree Tree))))\n'
FUNCTION = ('(lam tree Tree (app (lam result Tree (drop Tree result (int 99))) '
            '(case Tree (lam value Tree Tree) Nil '
            '(lam left Tree (lam right Tree (Node left right))) tree)))')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    compiler = str(Path(parser.parse_args().compiler).resolve())
    fixture = ROOT / 'tests/core_data_source.jhc'
    text = fixture.read_text()
    with tempfile.TemporaryDirectory(prefix='core-data-source-') as directory:
        tmp = Path(directory)
        probe = tmp / 'probe'
        command([compiler, 'build', '-O0', '-I', ROOT/'compiler',
                 ROOT/'tests/core_data_source_probe.jh', '-o', probe])

        def export(source):
            result = subprocess.run([str(probe)], input=source, text=True,
                                    capture_output=True, timeout=180)
            require(result.returncode == 0, result.stderr)
            return json.loads(result.stdout)

        expected = json.loads((ROOT/'tests/core_data_source.json').read_text())
        require(export(text) == expected, 'complete checked Data source view differs from Lean fixture')
        # The executable variants use the very same function, modulo formatting.
        canonical = FAMILY + f'(export consume (pi tree Tree I64) {FUNCTION})\n'
        require(export(canonical) == expected, 'native fixture function differs from checked graph')
        command([compiler, 'core', 'check', fixture])
        command([compiler, 'core', 'preserves', fixture])
        negative = export(text.replace('(int 99)', '(int -1)'))
        require(negative[4][12] == ['opaque'], 'negative integer was projected as an unsigned literal')

        trees = ['Nil', '(Node Nil Nil)', '(Node (Node Nil Nil) Nil)',
                 '(Node (Node Nil Nil) (Node (Node Nil Nil) Nil))']
        native_source = FAMILY + ''.join(
            f'(export case{i} I64 (app {FUNCTION} {tree}))\n'
            for i, tree in enumerate(trees))
        source = tmp/'native.jhc'
        source.write_text(native_source)
        command([compiler, 'core', 'check', source])
        command([compiler, 'core', 'preserves', source])
        counter = tmp/'counter.c'
        counter.write_text(COUNTER)
        cc = shlex.split(os.environ.get('JIHOO_CC', 'clang'))
        cases = 0
        for level in ('-O0', '-O2'):
            obj, library = tmp/f'{level}.o', tmp/f'{level}.so'
            command([compiler, 'core', 'emit-obj', source, level, '-o', obj])
            command([*cc, '-shared', '-fPIC', obj, counter, '-o', library,
                     '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
            native = ctypes.CDLL(str(library))
            stats = {k: ctypes.c_long.in_dll(native, k) for k in
                     ('allocations', 'frees', 'active_count', 'bad', 'free_count')}
            for i, nodes in enumerate((1, 3, 5, 9)):
                fn = getattr(native, f'case{i}')
                fn.argtypes, fn.restype = [], ctypes.c_int64
                before = stats['allocations'].value, stats['frees'].value
                stats['free_count'].value = 0
                require(fn() == 99, f'{level} case{i}: wrong result')
                allocated = stats['allocations'].value-before[0]
                freed = stats['frees'].value-before[1]
                require(allocated == freed and 0 <= allocated <= nodes+1,
                        f'{level} case{i}: lifecycle imbalance {allocated}/{freed}')
                if level == '-O0':
                    require(allocated >= nodes, f'case{i}: expected boxed input constructors')
                require(stats['active_count'].value == stats['bad'].value == 0,
                        f'{level} case{i}: leaked or invalid ownership')
                cases += 1

        bad = {
            'oversized-integer': text.replace('(int 99)', '(int 9223372036854775808)'),
            'duplicate-child': text.replace('(Node left right)', '(Node left left)'),
            'wrong-motive': text.replace('(lam value Tree Tree)', '(lam value Tree I64)'),
            'wrong-branch-domain': text.replace('(lam right Tree', '(lam right I64'),
            'wrong-consumer-domain': text.replace('(lam result Tree', '(lam result I64'),
        }
        for name, source_text in bad.items():
            path = tmp/f'{name}.jhc'
            path.write_text(source_text)
            command([compiler, 'core', 'check', path], success=False)
            result = subprocess.run([str(probe)], input=source_text, text=True,
                                    capture_output=True, timeout=180)
            require(result.returncode != 0 and not result.stdout,
                    f'{name}: unchecked graph escaped probe')
            # Use a scalar export so emission failure is not caused by the
            # unsupported external Data ABI of the inspected source fixture.
            wrapped = source_text.replace(
                '(export consume (pi tree Tree I64)',
                '(export invalid I64 (app', 1).rstrip()
            require(wrapped.endswith(')'), 'malformed test wrapper')
            scalar = tmp/f'{name}-scalar.jhc'
            scalar.write_text(wrapped[:-1] + ' Nil))\n')
            command([compiler, 'core', 'check', scalar], success=False)
            obj = tmp/f'{name}.o'
            command([compiler, 'core', 'emit-obj', scalar, '-o', obj], success=False)
            require(not obj.exists(), f'{name}: invalid source emitted code')
        print(f'core-data-source: {len(expected[4])} exact nodes, {cases} native lifecycles, {len(bad)} rejects')


if __name__ == '__main__':
    main()
