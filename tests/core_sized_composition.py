#!/usr/bin/env python3
"""Dynamic sized owned calls with retained captures; native regressions only."""
import argparse
import ctypes
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

from core_dependent_buffer import SIZED_COUNTER
from core_linear_heap import bind
from core_scoped_lend import command, require

ROOT = Path(__file__).resolve().parent.parent


def source(name, copied):
    # A direct owned-producing application moves the result while the original
    # buffer remains captured by its consumer. Lengths n and m are independent.
    observed = ('(if-lt 0 m readBound '
                '(lend moved (lam check (Ref (Buffer m)) (index check 0 readBound)) '
                '(lam observed I64 (lam returned (Buffer m) '
                '(free original (free returned observed))))) '
                '(free original (free moved value)))')
    moved = bind('moved', '(Buffer m)',
                 bind('transfer', '(Buffer m)', 'copy', 'transfer'),
                 observed)
    if copied:
        yes = ('(lend original (lam ref (Ref (Buffer n)) '
               '(alloc m (index ref i bound))) '
               f'(lam copy (Buffer m) (lam original (Buffer n) {moved})))')
    else:
        yes = bind('copy', '(Buffer m)', '(alloc m value)', moved)
    body = f'(if-lt i n bound {yes} (free original (int 99)))'
    body = bind('original', '(Buffer n)', '(alloc n value)', body)
    return (f'(export {name} (pi n U64 (pi m U64 (pi i U64 (pi value I64 I64)))) '
            f'(lam n U64 (lam m U64 (lam i U64 (lam value I64 {body})))))\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    compiler = str(Path(parser.parse_args().compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='sized-composition-') as directory:
        tmp = Path(directory)
        fixture = ROOT / 'tests/core_sized_composition.jhc'
        require(fixture.read_text() == source('copied', True), 'checked source fixture drift')
        probe = tmp / 'probe'
        command([compiler, 'build', '-O0', '-I', ROOT / 'compiler',
                 ROOT / 'tests/core_linear_graph_probe.jh', '-o', probe])
        exported = subprocess.run([str(probe)], input=fixture.read_text(),
                                  capture_output=True, text=True, timeout=180)
        require(exported.returncode == 0, exported.stderr)
        require(json.loads(exported.stdout) ==
                json.loads((ROOT / 'tests/core_sized_composition.json').read_text()),
                'complete checked graph differs from formal fixture')
        core = tmp / 'composed.jhc'
        core.write_text(source('framed', False) + source('copied', True))
        command([compiler, 'core', 'check', core])
        command([compiler, 'core', 'preserves', core])
        counter = tmp / 'counter.c'
        counter.write_text(SIZED_COUNTER)
        cc = shlex.split(os.environ.get('JIHOO_CC', 'clang'))
        cases = 0
        inputs = ((0, 0, 0), (0, 7, 1), (1, 0, 0), (1, 7, 0),
                  (4, 2, 3), (7, 1, 6), (4, 9, 4), (2, 3, (1 << 64)-1))
        for level in ('-O0', '-O2'):
            obj, library = tmp / f'{level}.o', tmp / f'{level}.so'
            command([compiler, 'core', 'emit-obj', core, level, '-o', obj])
            command([*cc, '-shared', '-fPIC', obj, counter, '-o', library,
                     '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
            native = ctypes.CDLL(str(library))
            stats = {k: ctypes.c_long.in_dll(native, k) for k in
                     ('allocations', 'frees', 'active_count', 'peak', 'bad',
                      'free_count', 'request_count')}
            frees = (ctypes.c_long*64).in_dll(native, 'freed_ids')
            sizes = (ctypes.c_size_t*64).in_dll(native, 'request_sizes')
            for name in ('framed', 'copied'):
                fn = getattr(native, name)
                fn.argtypes = [ctypes.c_uint64, ctypes.c_uint64,
                               ctypes.c_uint64, ctypes.c_int64]
                fn.restype = ctypes.c_int64
                for n, m, i in inputs:
                    for value in (-13, 0, 42):
                        before = stats['allocations'].value, stats['frees'].value
                        stats['peak'].value = stats['free_count'].value = stats['request_count'].value = 0
                        require(fn(n, m, i, value) == (value if i < n else 99),
                                f'{name}: wrong result for n={n}, m={m}, i={i}')
                        count = 2 if i < n else 1
                        delta = stats['allocations'].value-before[0], stats['frees'].value-before[1]
                        require(delta[0] == delta[1] and 0 <= delta[0] <= count,
                                f'{name}: lifecycle imbalance {delta}')
                        if level == '-O0':
                            require(delta == (count, count), f'{name}: missing allocation')
                            require(stats['peak'].value == count, f'{name}: captured owner lifetime')
                            require([sizes[j] for j in range(stats['request_count'].value)] ==
                                    ([8*(n+1), 8*(m+1)] if i < n else [8*(n+1)]),
                                    f'{name}: dependent allocation sizes confused')
                            require([frees[j]-before[0] for j in range(stats['free_count'].value)] ==
                                    list(range(count)), f'{name}: wrong owner released')
                        require(stats['active_count'].value == stats['bad'].value == 0,
                                f'{name}: leaked or invalid ownership')
                        cases += 1
        bad = {
            'unconsumed-moved': ('an owned value must be used',
                source('bad', False).replace('(lend moved', '(lend copy').replace(
                    '(free moved value)', '(free copy value)')),
            'double-consume': ('an owned value is used more than once',
                source('bad', False).replace('(free returned observed)',
                    '(free returned (free copy observed))').replace(
                    '(free moved value)', '(free moved (free copy value))')),
            'wrong-domain': ('type mismatch',
                source('bad', False).replace('(lam transfer (Buffer m)', '(lam transfer (Buffer n)')),
            'wrong-result-length': ('a lend continues with the result and the owner',
                source('bad', True).replace('(lam copy (Buffer m)', '(lam copy (Buffer n)')),
            'wrong-index-proof': ('type mismatch',
                source('bad', True).replace('(index ref i bound)', '(index ref n bound)')),
        }
        for name, (diagnostic, text) in bad.items():
            path = tmp / f'{name}.jhc'
            path.write_text(text)
            failed = command([compiler, 'core', 'check', path], success=False)
            require(diagnostic in failed.stderr, f'{name}: wrong failure: {failed.stderr}')
            obj = tmp / f'{name}.o'
            command([compiler, 'core', 'emit-obj', path, '-o', obj], success=False)
            require(not obj.exists(), f'{name}: invalid source emitted an object')
        print(f'sized-composition: 2 variants, {cases} native lifecycles, {len(bad)} rejects')


if __name__ == '__main__':
    main()
