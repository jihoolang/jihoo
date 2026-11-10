#!/usr/bin/env python3
"""Native continuation-nested owned Lends; not nested-reader Lends/refinement.
Load/add observations are native test scaffolding, not the formal continuation grammar.
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


def lend(owner, result, alias, body):
    reader = f'r_{result}'
    return (f'(lend {owner} (lam {reader} (Ref (Buffer 1)) '
            f'(alloc 1 (index {reader} 0 {BOUND}))) '
            f'(lam {result} (Buffer 1) (lam {alias} (Buffer 1) {body})))')


def consume(owners, extra='(int 0)'):
    if not owners:
        return extra
    owner, *rest = owners
    scalar, back = 'v_'+owner, 'o_'+owner
    return (f'(load {owner} 0 {BOUND} (lam {scalar} I64 (lam {back} (Buffer 1) '
            f'(free {back} {consume(rest, f"(add {extra} {scalar})")}))))')


def body(other=False, original=False, reverse=False, churn=False):
    # The oldest owner is lent while the newer unrelated side remains live.
    xs = 'xs' if original else ('x1' if other else 'x2')
    side = 'side' if original or not other else 's1'
    a = 'a' if original else 'a1'
    owners = [xs, side, a, 'c', 'd' if churn else 'b']
    if reverse:
        owners.reverse()
    final = consume(owners, 'bv' if churn else '(int 0)')
    final = lend('a', 'c', 'a1', final)
    if churn:
        final = bind('d', '(Buffer 1)', '(alloc 1 (int 5))', final)
        final = f'(load b 0 {BOUND} (lam bv I64 (lam bb (Buffer 1) (free bb {final}))))'
    final = lend('side' if other else ('xs' if original else 'x1'),
                 'b', 's1' if other else 'x2', final)
    final = lend('xs', 'a', 'x1', final)
    final = bind('side', '(Buffer 1)', '(alloc 1 other)', final)
    return bind('xs', '(Buffer 1)', '(alloc 1 value)', final)


def source(name='run', **options):
    return f'(export {name} (pi value I64 (pi other I64 I64)) (lam value I64 (lam other I64 {body(**options)})))\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    compiler = str(Path(parser.parse_args().compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='compositional-lend-') as directory:
        tmp = Path(directory)
        specs, texts = [], []
        for other in (False, True):
            for original in (False, True):
                for reverse in (False, True):
                    for churn in (False, True):
                        name = f'f{len(specs)}'
                        specs.append((name, other, churn))
                        texts.append(source(name, other=other, original=original, reverse=reverse, churn=churn))
        core = tmp / 'all.jhc'; core.write_text(''.join(texts))
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
            for name, other, churn in specs:
                fn = getattr(native, name); fn.argtypes = [ctypes.c_int64]*2; fn.restype = ctypes.c_int64
                for value, unrelated in ((11, 37), (-7, 19), (0, 0), (42, -3)):
                    expected = (3*value+2*unrelated if other else 4*value+unrelated) + (5 if churn else 0)
                    before = stats['allocations'].value, stats['frees'].value
                    stats['peak'].value = 0
                    require(fn(value, unrelated) == expected, 'wrong selected/unrelated owner payload')
                    delta = stats['allocations'].value-before[0], stats['frees'].value-before[1]
                    total = 6 if churn else 5
                    require(delta[0] == delta[1] and 0 <= delta[0] <= total, 'unbalanced lifecycle')
                    if level == '-O0':
                        require(delta == (total, total) and stats['peak'].value == 5,
                                'O0 owner allocation/liveness mismatch')
                    require(stats['active_count'].value == 0 and stats['bad'].value == 0,
                            'aliasing allocation, invalid free or leak')
                    cases += 1
        base = source(original=True)
        invalid = {
            'unrelated-borrow': ('a borrow of a value is evidence only',
                base.replace('(index r_a 0', '(index (borrow side) 0')),
            'duplicate-alias': ('a lent owner is used exactly once after its lend',
                base.replace('(free o_xs ', '(free (app (lam taken (Buffer 1) (free x1 taken)) o_xs) ', 1)),
            'missing-owner': ('an owned value must be used',
                base.replace('(free o_xs ', '(app (lam ignored I64 ignored) ', 1)),
        }
        for name, (diagnostic, text) in invalid.items():
            path = tmp / f'{name}.jhc'; path.write_text(text)
            result = command([compiler, 'core', 'check', path], success=False)
            require(diagnostic in result.stderr, f'{name}: wrong diagnostic: {result.stderr}')
            obj = tmp / f'{name}.o'
            command([compiler, 'core', 'emit-obj', path, '-o', obj], success=False)
            require(not obj.exists(), 'invalid composition emitted object')
        print(f'compositional Lend: {len(specs)} variants, {cases} native lifecycles, {len(invalid)} rejects')


if __name__ == '__main__':
    main()
