#!/usr/bin/env python3
"""Native scalar-result preservation across linear caller binders.
These regressions are not a refinement proof of the native compiler.
"""
import argparse
import ctypes
import os
from pathlib import Path
import shlex
import tempfile
from core_linear_heap import COUNTER
from core_linear_graph import CALLEE, bind
from core_scoped_lend import command, require


def body(result='first', values=('(int 11)', '(int 22)', '(int 33)'), changed=False):
    result = bind('third', 'I64', f'(app {CALLEE} z)', result)
    result = bind('second', 'I64', f'(app {CALLEE} y)', result)
    result = bind('z', '(Buffer 1)', f'(alloc 1 {values[2]})', result)
    callee = CALLEE.replace('(index r 0 (decide-lt 0 1))', '(int 99)') if changed else CALLEE
    result = bind('first', 'I64', f'(app {callee} x)', result)
    result = bind('y', '(Buffer 1)', f'(alloc 1 {values[1]})', result)
    return bind('x', '(Buffer 1)', f'(alloc 1 {values[0]})', result)


def source(result='first', changed=False):
    return f'(def run I64 {body(result, changed=changed)})'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    compiler = str(Path(parser.parse_args().compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='scalar-callers-') as directory:
        tmp = Path(directory)
        core = tmp / 'callers.jhc'
        core.write_text('\n'.join(f'(export {name} (pi a I64 (pi b I64 (pi c I64 I64))) '
            f'(lam a I64 (lam b I64 (lam c I64 {body(result, ("a", "b", "c"), name == "changed")}))))'
            for name, result in (('older', 'first'), ('middle', 'second'),
                                 ('newer', 'third'), ('literal', '(int 77)'), ('changed', 'first'))))
        command([compiler, 'core', 'check', core])
        command([compiler, 'core', 'preserves', core])
        counter = tmp / 'counter.c'; counter.write_text(COUNTER)
        cc = shlex.split(os.environ.get('JIHOO_CC', 'clang'))
        cases = 0
        for level in ('-O0', '-O2'):
            obj = tmp / f'{level}.o'; library = tmp / f'{level}.so'
            command([compiler, 'core', 'emit-obj', core, level, '-o', obj])
            command([*cc, '-shared', '-fPIC', obj, counter, '-o', library,
                     '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
            native = ctypes.CDLL(str(library))
            stats = {n: ctypes.c_long.in_dll(native, n) for n in
                     ('allocations', 'frees', 'active_count', 'bad')}
            for name, slot in (('older', 0), ('middle', 1), ('newer', 2), ('literal', 3), ('changed', 4)):
                fn = getattr(native, name); fn.argtypes = [ctypes.c_int64] * 3; fn.restype = ctypes.c_int64
                for values in ((11, 22, 33), (-7, 42, 0), (0, 0, 0),
                               (-(1 << 63), (1 << 63)-1, 19)):
                    before = stats['allocations'].value, stats['frees'].value
                    require(fn(*values) == (*values, 77, 99)[slot], 'wrong scalar binding/result')
                    delta = stats['allocations'].value-before[0], stats['frees'].value-before[1]
                    require(delta[0] == delta[1] and 0 <= delta[0] <= 3, 'unbalanced allocation')
                    require(level != '-O0' or delta == (3, 3), 'O0 allocation mismatch')
                    require(stats['active_count'].value == 0 and stats['bad'].value == 0, 'invalid lifecycle')
                    cases += 1
        invalid = {
            'live-owner-result': '(def run I64 (app (lam x (Buffer 1) x) (alloc 1 (int 11))))',
            'dead-owner-result': source('x'),
            'scalar-owner': source().replace(f'(app {CALLEE} y)', f'(app {CALLEE} first)'),
        }
        for name, text in invalid.items():
            path = tmp / f'{name}.jhc'; path.write_text(text)
            result = command([compiler, 'core', 'check', path], success=False)
            expected = ('an owned value is used more than once' if name == 'dead-owner-result'
                        else 'type mismatch')
            require(expected in result.stderr, f'wrong diagnostic: {result.stderr}')
            obj = tmp / f'{name}.o'
            command([compiler, 'core', 'emit-obj', path, '-o', obj], success=False)
            require(not obj.exists(), 'invalid scalar caller emitted object')
        print(f'scalar callers: {cases} native results/lifecycles, {len(invalid)} rejected callers')


if __name__ == '__main__':
    main()
