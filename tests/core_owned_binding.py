#!/usr/bin/env python3
"""Native ownership transfer through direct Buffer lambda applications.
Old names cannot replace the required linear formal. No compiler refinement claim.
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


def transfer(owner, names, body):
    for i in reversed(range(len(names))):
        body = bind(names[i], '(Buffer 1)', owner if i == 0 else names[i-1], body)
    return body


def source(name='run', result='early', depth=1, reverse=False, constant=False):
    names = [f'x{i}' for i in range(depth)]
    owners = ['returned', 'other', 'fresh']
    if reverse:
        owners.reverse()
    body = free_all(owners, result)
    body = lend('fresh0', 'latest', 'fresh', body)
    body = transfer('made', ['fresh0'], body)
    body = transfer('s1', ['other'], body)
    body = transfer('xret', ['returned'], body)
    body = lend('side', 'made', 's1', body, owned=True, constant=constant)
    body = lend(names[-1], 'early', 'xret', body)
    body = transfer('xs', names, body)
    body = bind('side', '(Buffer 1)', '(alloc 1 otherValue)', body)
    body = bind('xs', '(Buffer 1)', '(alloc 1 value)', body)
    return f'(export {name} (pi value I64 (pi otherValue I64 I64)) (lam value I64 (lam otherValue I64 {body})))\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    compiler = str(Path(parser.parse_args().compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='owned-binding-') as directory:
        tmp = Path(directory)
        specs, texts = [], []
        for result in ('early', 'latest', '(int 55)'):
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
                    expected = {'early': value, 'latest': 37 if constant else other, '(int 55)': 55}[result]
                    before = stats['allocations'].value, stats['frees'].value
                    stats['peak'].value = 0
                    require(fn(value, other) == expected, f'{name}: wrong transferred owner/captured scalar result')
                    delta = stats['allocations'].value-before[0], stats['frees'].value-before[1]
                    require(delta[0] == delta[1] and 0 <= delta[0] <= 3, 'unbalanced lifecycle')
                    if level == '-O0':
                        require(delta == (3, 3) and stats['peak'].value == 3, 'O0 owner identity/liveness mismatch')
                    require(stats['active_count'].value == 0 and stats['bad'].value == 0, 'invalid ownership lifecycle')
                    cases += 1
        def bad(body, argument='x', ty='(Buffer 1)', erased=False):
            lam = 'lam0' if erased else 'lam'
            return f'(export bad I64 (app (lam x (Buffer 1) (app ({lam} alias {ty} {body}) {argument})) (alloc 1 (int 11))))'
        invalid = {
            'original-instead': ('an owned value must be used', bad('(free x (int 7))')),
            'original-and-alias': ('an owned value is used more than once', bad('(free alias (free x (int 7)))')),
            'ignored': ('an owned value must be used', bad('(int 7)')),
            'duplicate': ('an owned value is used more than once', bad('(free alias (free alias (int 7)))')),
            'wrong-type': ('type mismatch', bad('(free x alias)', ty='I64')),
            'scalar-argument': ('type mismatch', bad('(free alias (int 7))', argument='(int 11)')),
            'erased-owner': ('erased binders must be propositions', bad('(free alias (int 7))', erased=True)),
            'revive-after-free': ('an owned value is used more than once',
                '(export bad I64 (app (lam x (Buffer 1) (free x (app (lam alias (Buffer 1) (free alias (int 7))) x))) (alloc 1 (int 11))))'),
        }
        for name, (diagnostic, text) in invalid.items():
            path = tmp / f'{name}.jhc'; path.write_text(text)
            failed = command([compiler, 'core', 'check', path], success=False)
            require(diagnostic in failed.stderr, f'{name}: wrong diagnostic: {failed.stderr}')
            obj = tmp / f'{name}.o'
            command([compiler, 'core', 'emit-obj', path, '-o', obj], success=False)
            require(not obj.exists(), 'invalid owned-binding program emitted object')
        print(f'owned-binding: {len(specs)} variants, {cases} native lifecycles, {len(invalid)} rejects')


if __name__ == '__main__':
    main()
