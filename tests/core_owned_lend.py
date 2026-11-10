#!/usr/bin/env python3
"""Native owned-result Lend tests, not a compiler refinement proof.
A returned Buffer is a new owner, not the reader's borrowed original pointer.
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


def source(name='run', mode='read', original=False, reverse=False, nested=False):
    payload = '(int 37)' if mode == 'constant' else f'(index {"(borrow xs)" if mode == "owner-read" else "r"} 0 {BOUND})'
    reader = f'(alloc 1 {payload})'
    if nested:
        reader = bind('tmp', '(Buffer 1)', '(alloc 1 (int 9))',
                      bind('made', '(Buffer 1)', reader, '(free tmp made)'))
    result = '(add rv ov)'
    result = f'(free oo (free rr {result}))' if reverse else f'(free rr (free oo {result}))'
    result = f'(load {"xs" if original else "y"} 0 {BOUND} (lam ov I64 (lam oo (Buffer 1) {result})))'
    result = f'(load a 0 {BOUND} (lam rv I64 (lam rr (Buffer 1) {result})))'
    continuation = f'(lam a (Buffer 1) (lam y (Buffer 1) {result}))'
    body = f'(lend xs (lam r (Ref (Buffer 1)) {reader}) {continuation})'
    body = bind('xs', '(Buffer 1)', '(alloc 1 value)', body)
    return f'(export {name} (pi value I64 I64) (lam value I64 {body}))\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    compiler = str(Path(parser.parse_args().compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='owned-lend-') as directory:
        tmp = Path(directory)
        specs, texts = [], []
        for mode in ('read', 'owner-read', 'constant'):
            for original in (False, True):
                for reverse in (False, True):
                    for nested in (False, True):
                        name = f'f{len(specs)}'
                        specs.append((name, mode, nested))
                        texts.append(source(name, mode, original, reverse, nested))
        core = tmp / 'owned.jhc'; core.write_text(''.join(texts))
        command([compiler, 'core', 'check', core])
        command([compiler, 'core', 'preserves', core])
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
            for name, mode, nested in specs:
                fn = getattr(native, name); fn.argtypes = [ctypes.c_int64]; fn.restype = ctypes.c_int64
                for value in (-11, 0, 7, 42):
                    before = stats['allocations'].value, stats['frees'].value
                    stats['peak'].value = 0
                    require(fn(value) == value + (37 if mode == 'constant' else value), 'wrong owned-result payload')
                    delta = stats['allocations'].value-before[0], stats['frees'].value-before[1]
                    total = 3 if nested else 2
                    require(delta[0] == delta[1] and 0 <= delta[0] <= total, 'unbalanced lifecycle')
                    if level == '-O0':
                        require(delta == (total, total), 'O0 allocation count mismatch')
                        require(stats['peak'].value == total, 'owners not simultaneously live/disjoint')
                    require(stats['active_count'].value == 0 and stats['bad'].value == 0,
                            'aliasing allocations, invalid/double free, or leak')
                    cases += 1
        base = source()
        invalid = {
            'duplicate-result': ('an owned value is used more than once', base.replace('(free rr (free oo (add rv ov)))', '(free rr (free rr (free oo (add rv ov))))')),
            'omit-result': ('an owned value must be used', base.replace('(free rr (free oo (add rv ov)))', '(free oo (add rv ov))')),
            'duplicate-original': ('an owned value is used more than once', base.replace('(free rr (free oo (add rv ov)))', '(free rr (free oo (free oo (add rv ov))))')),
            'omit-original': ('an owned value must be used', base.replace('(free rr (free oo (add rv ov)))', '(free rr (add rv ov))')),
            'scalar-result': ('a lend continues with the result and the owner', base.replace('(lam a (Buffer 1)', '(lam a I64')),
            'borrow-escape': ('a borrow cannot outlive its lend',
                '(def bad (pi xs (Buffer 1) (Ref (Buffer 1))) '
                '(lam xs (Buffer 1) (lend xs (lam r (Ref (Buffer 1)) r) '
                '(lam a (Ref (Buffer 1)) (lam y (Buffer 1) (free y a))))))'),
        }
        for name, (diagnostic, text) in invalid.items():
            path = tmp / f'{name}.jhc'; path.write_text(text)
            result = command([compiler, 'core', 'check', path], success=False)
            require(diagnostic in result.stderr, f'{name}: wrong diagnostic: {result.stderr}')
            obj = tmp / f'{name}.o'
            command([compiler, 'core', 'emit-obj', path, '-o', obj], success=False)
            require(not obj.exists(), 'invalid owned Lend emitted object')
        print(f'owned Lend: {len(specs)} variants, {cases} native lifecycles, {len(invalid)} rejected programs')


if __name__ == '__main__':
    main()
