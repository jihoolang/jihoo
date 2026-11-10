#!/usr/bin/env python3
"""Owned results survive a producer and are consumed by its caller.
Native integration evidence, not a proof of general Core App/lowering refinement.
"""
import argparse
import ctypes
import os
from pathlib import Path
import shlex
import tempfile
from core_linear_heap import COUNTER, bind
from core_mixed_lend import lend
from core_scoped_lend import command, require


def source(name, fresh, depth, borrowed):
    # Both allocations deliberately coexist: equal payloads must not collapse IDs.
    tail = '(free input made)' if fresh else '(free made input)'
    if borrowed:
        # Returned original owner remains owned, not the temporary borrowed ref.
        chosen = 'made' if fresh else 'input'
        other = 'input' if fresh else 'made'
        tail = lend(chosen, 'ignored', 'restored', f'(free {other} restored)')
    producer = bind('input', '(Buffer 1)', '(alloc 1 a)',
                    bind('made', '(Buffer 1)', '(alloc 1 b)', tail))
    for i in range(depth):
        producer = bind(f'move{i}', '(Buffer 1)', producer, f'move{i}')
    body = bind('result', '(Buffer 1)', producer,
                lend('result', 'value', 'last', '(free last value)'))
    return f'(export {name} (pi a I64 (pi b I64 I64)) (lam a I64 (lam b I64 {body})))\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    compiler = str(Path(parser.parse_args().compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='owned-result-') as directory:
        tmp = Path(directory)
        specs, texts = [], []
        for fresh in (False, True):
            for depth in (0, 1, 3):
                for borrowed in (False, True):
                    name = f'f{len(specs)}'
                    specs.append((name, fresh))
                    texts.append(source(name, fresh, depth, borrowed))
        core = tmp / 'all.jhc'; core.write_text(''.join(texts))
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
            for name, fresh in specs:
                fn = getattr(native, name); fn.argtypes = [ctypes.c_int64]*2; fn.restype = ctypes.c_int64
                for a, b in ((11, 37), (37, 11), (7, 7), (-7, 42), (0, 0)):
                    before = stats['allocations'].value, stats['frees'].value
                    stats['peak'].value = 0
                    require(fn(a, b) == (b if fresh else a), f'{name}: wrong returned identity/value')
                    delta = stats['allocations'].value-before[0], stats['frees'].value-before[1]
                    require(delta[0] == delta[1] and 0 <= delta[0] <= 2, 'unbalanced result lifecycle')
                    if level == '-O0':
                        require(delta == (2, 2) and stats['peak'].value == 2, 'O0 return freed too soon or leaked')
                    require(stats['active_count'].value == 0 and stats['bad'].value == 0,
                            'result double-free or leak')
                    cases += 1
        invalid = {
            'freed-result': ('an owned value is used more than once',
                '(free x x)'),
            'lost-other': ('an owned value must be used',
                '(app (lam y (Buffer 1) x) (alloc 1 (int 9)))'),
            'returned-twice': ('an owned value is used more than once',
                '(app (lam y (Buffer 1) (free y x)) x)'),
            'wrong-result': ('type mismatch', '(free x (int 9))'),
        }
        for name, (diagnostic, body) in invalid.items():
            text = f'(def bad (pi x (Buffer 1) (Buffer 1)) (lam x (Buffer 1) {body}))'
            path = tmp / f'{name}.jhc'; path.write_text(text)
            failed = command([compiler, 'core', 'check', path], success=False)
            require(diagnostic in failed.stderr, f'{name}: unexpected diagnostic: {failed.stderr}')
            obj = tmp / f'{name}.o'
            command([compiler, 'core', 'emit-obj', path, '-o', obj], success=False)
            require(not obj.exists(), f'{name}: invalid owned result emitted object')
        print(f'owned-result: {len(specs)} variants, {cases} native lifecycles, {len(invalid)} rejects')


if __name__ == '__main__':
    main()
