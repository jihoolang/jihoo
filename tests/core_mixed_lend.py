#!/usr/bin/env python3
"""Native mixed scalar/owned-result Lend continuation regressions.
These are implementation tests, not a compiler refinement or nested-reader claim.
"""
import argparse
import ctypes
import os
from pathlib import Path
import shlex
import tempfile
from core_linear_heap import COUNTER, bind
from core_scoped_lend import command, require

BOUND = '(decide-lt 0 1)'


def lend(owner, result, alias, body, owned=False, constant=False):
    reader = f'r_{result}'
    payload = '(int 37)' if constant else f'(index {reader} 0 {BOUND})'
    result_type = '(Buffer 1)' if owned else 'I64'
    read = f'(alloc 1 {payload})' if owned else payload
    return (f'(lend {owner} (lam {reader} (Ref (Buffer 1)) {read}) '
            f'(lam {result} {result_type} (lam {alias} (Buffer 1) {body})))')


def free_all(owners, result):
    for owner in reversed(owners):
        result = f'(free {owner} {result})'
    return result


def source(name='run', result='early', original=False, churn=False, constant=False):
    xs, side, made = ('xs', 'side', 'made') if original else ('x2', 's2', 'a1')
    owners = [side, made, 'last', 'd1'] if churn else [xs, side, made, 'last']
    # Alternate consumption order without adding another dimension.
    if original:
        owners.reverse()
    final = free_all(owners, result)
    if churn:
        final = lend('d', 'recent', 'd1', final)
        final = f'(free {xs} {bind("d", "(Buffer 1)", "(alloc 1 (int 99))", final)})'
    else:
        final = bind('recent', 'I64', '(int 99)', final)
    final = lend('side' if original else 's1', 'middle', 's2', final)
    final = lend('xs' if original else 'x1', 'last', 'x2', final, owned=True, constant=constant)
    final = lend('made', 'latest', 'a1', final)
    final = lend('side', 'made', 's1', final, owned=True, constant=constant)
    final = lend('xs', 'early', 'x1', final)
    final = bind('side', '(Buffer 1)', '(alloc 1 other)', final)
    final = bind('xs', '(Buffer 1)', '(alloc 1 value)', final)
    return f'(export {name} (pi value I64 (pi other I64 I64)) (lam value I64 (lam other I64 {final})))\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    compiler = str(Path(parser.parse_args().compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='mixed-lend-') as directory:
        tmp = Path(directory)
        specs, texts = [], []
        for result in ('early', 'latest', 'middle', 'recent'):
            for original in (False, True):
                for churn in (False, True):
                    for constant in (False, True):
                        name = f'f{len(specs)}'
                        specs.append((name, result, churn, constant))
                        texts.append(source(name, result, original, churn, constant))
        core = tmp / 'mixed.jhc'; core.write_text(''.join(texts))
        command([compiler, 'core', 'check', core]); command([compiler, 'core', 'preserves', core])
        counter = tmp / 'counter.c'; counter.write_text(COUNTER)
        cc = shlex.split(os.environ.get('JIHOO_CC', 'clang'))
        cases = 0
        for level in ('-O0', '-O2'):
            obj, library = tmp / f'{level}.o', tmp / f'{level}.so'
            command([compiler, 'core', 'emit-obj', core, level, '-o', obj])
            command([*cc, '-shared', '-fPIC', obj, counter, '-o', library,
                     '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
            native = ctypes.CDLL(str(library))
            stats = {n: ctypes.c_long.in_dll(native, n) for n in
                     ('allocations', 'frees', 'active_count', 'peak', 'bad')}
            for name, result, churn, constant in specs:
                fn = getattr(native, name); fn.argtypes = [ctypes.c_int64]*2; fn.restype = ctypes.c_int64
                for value, other in ((11, 22), (-7, 42), (7, 7), (0, 0)):
                    expected = {'early': value, 'latest': 37 if constant else other,
                                'middle': other, 'recent': 99}[result]
                    before = stats['allocations'].value, stats['frees'].value
                    stats['peak'].value = 0
                    require(fn(value, other) == expected, f'{name}: wrong scalar binding/result')
                    delta = stats['allocations'].value-before[0], stats['frees'].value-before[1]
                    total = 5 if churn else 4
                    require(delta[0] == delta[1] and 0 <= delta[0] <= total, 'unbalanced lifecycle')
                    if level == '-O0':
                        require(delta == (total, total) and stats['peak'].value == 4,
                                'O0 ownership/liveness mismatch')
                    require(stats['active_count'].value == 0 and stats['bad'].value == 0,
                            'aliasing allocations, duplicate free or leak')
                    cases += 1
        base = source(churn=True)
        invalid = {
            'scalar-as-owned-annotation': ('a lend continues with the result and the owner',
                base.replace('(lam early I64', '(lam early (Buffer 1)')),
            'owned-as-scalar-annotation': ('a lend continues with the result and the owner',
                base.replace('(lam made (Buffer 1)', '(lam made I64')),
            'scalar-as-owner': ('only an owned value is lent',
                base.replace('(lend made ', '(lend early ', 1)),
            'revive-freed-owner': ('a lent owner is used exactly once after its lend',
                base.replace('(alloc 1 (int 99))', 'x2')),
            'duplicate-free': ('an owned value is used more than once',
                base.replace('(free d1 ', '(free (app (lam tmp (Buffer 1) (free tmp tmp)) d1) ', 1)),
        }
        for name, (diagnostic, text) in invalid.items():
            path = tmp / f'{name}.jhc'; path.write_text(text)
            failure = command([compiler, 'core', 'check', path], success=False)
            require(diagnostic in failure.stderr, f'{name}: wrong diagnostic: {failure.stderr}')
            obj = tmp / f'{name}.o'
            command([compiler, 'core', 'emit-obj', path, '-o', obj], success=False)
            require(not obj.exists(), 'invalid mixed Lend emitted object')
        print(f'mixed Lend: {len(specs)} variants, {cases} native lifecycles, {len(invalid)} rejects')


if __name__ == '__main__':
    main()
