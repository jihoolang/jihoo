#!/usr/bin/env python3
"""Native pure I64 bindings inside owned/scalar Lend continuations.
Direct scalar lets only: no higher-order or native compiler refinement claim.
"""
import argparse
import ctypes
import os
from pathlib import Path
import shlex
import tempfile
from core_linear_heap import COUNTER, bind
from core_mixed_lend import lend, free_all
from core_scoped_lend import command, require


def pure(atom, depth):
    for _ in range(depth):
        # Shadow the same names repeatedly; retain the earlier scalar argument.
        atom = bind('p', 'I64', atom, bind('q', 'I64', '(int 66)', 'p'))
    return atom


def source(name='run', result='saved', depth=1, original=False, constant=False):
    owners = ['xs', 'side', 'made'] if original else ['x1', 's1', 'a1']
    body = bind('chosen', 'I64', pure(result, depth), free_all(owners, 'chosen'))
    body = bind('latest', 'I64', pure('saved', depth), body)  # shadows the latest Lend result
    body = bind('after', 'I64', pure('latest', depth), body)
    body = lend('made', 'latest', 'a1', body)
    body = bind('early', 'I64', '(int 99)', body)  # shadows first Lend result
    body = lend('side', 'made', 's1', body, owned=True, constant=constant)
    body = bind('saved', 'I64', pure('early', depth), body)
    body = lend('xs', 'early', 'x1', body)
    body = bind('side', '(Buffer 1)', '(alloc 1 other)', body)
    body = bind('xs', '(Buffer 1)', '(alloc 1 value)', body)
    return f'(export {name} (pi value I64 (pi other I64 I64)) (lam value I64 (lam other I64 {body})))\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    compiler = str(Path(parser.parse_args().compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='pure-owned-') as directory:
        tmp = Path(directory)
        specs, texts = [], []
        for result in ('saved', 'early', 'after', 'latest', '(int 55)'):
            for depth in (1, 3):
                for original in (False, True):
                    for constant in (False, True):
                        name = f'f{len(specs)}'
                        specs.append((name, result, constant))
                        texts.append(source(name, result, depth, original, constant))
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
            for name, result, constant in specs:
                fn = getattr(native, name); fn.argtypes = [ctypes.c_int64]*2; fn.restype = ctypes.c_int64
                for value, other in ((11, 22), (-7, 42), (7, 7), (0, 0)):
                    expected = {'saved': value, 'early': 99, 'after': 37 if constant else other,
                                'latest': value, '(int 55)': 55}[result]
                    before = stats['allocations'].value, stats['frees'].value
                    stats['peak'].value = 0
                    require(fn(value, other) == expected, f'{name}: wrong capture/shadowed result')
                    delta = stats['allocations'].value-before[0], stats['frees'].value-before[1]
                    require(delta[0] == delta[1] and 0 <= delta[0] <= 3, 'unbalanced lifecycle')
                    if level == '-O0':
                        require(delta == (3, 3) and stats['peak'].value == 3, 'O0 owner identity/liveness mismatch')
                    require(stats['active_count'].value == 0 and stats['bad'].value == 0, 'invalid ownership lifecycle')
                    cases += 1
        base = source()
        invalid = {
            'owner-scalar': ('type mismatch', base.replace(pure('early', 1), pure('x1', 1), 1)),
            'consumed-scalar': ('type mismatch',
                '(export bad I64 (app (lam x (Buffer 1) (free x (app (lam p I64 p) x))) (alloc 1 (int 7))))'),
            'erased-runtime': ('erased value used at runtime', '(export bad U64 (app (lam0 n U64 n) 0))'),
            'annotation': ('type mismatch', base.replace('(lam saved I64', '(lam saved U64', 1)),
            'duplicate-owner': ('an owned value is used more than once',
                base.replace('(free x1 ', '(free (app (lam t (Buffer 1) (free t t)) x1) ', 1)),
        }
        for name, (diagnostic, text) in invalid.items():
            path = tmp / f'{name}.jhc'; path.write_text(text)
            failed = command([compiler, 'core', 'check', path], success=False)
            require(diagnostic in failed.stderr, f'{name}: wrong diagnostic: {failed.stderr}')
            obj = tmp / f'{name}.o'
            command([compiler, 'core', 'emit-obj', path, '-o', obj], success=False)
            require(not obj.exists(), 'invalid pure/owned program emitted object')
        print(f'pure/owned: {len(specs)} variants, {cases} native lifecycles, {len(invalid)} rejects')


if __name__ == '__main__':
    main()
