#!/usr/bin/env python3
"""Native regression for finite linear allocation/call sequencing.
This tests implementation behavior, not a proof of caller-graph translation.
"""
import argparse
import ctypes
import os
from pathlib import Path
import platform
import shlex
import tempfile
from core_scoped_lend import command, require

CALLEE = '''(def consume (pi xs (Buffer 1) I64)
 (lam xs (Buffer 1) (lend xs
  (lam r (Ref (Buffer 1)) (index r 0 (decide-lt 0 1)))
  (lam a I64 (lam y (Buffer 1) (free y a))))))\n'''

COUNTER = r'''
#include <stddef.h>
void *__real_malloc(size_t);
void __real_free(void *);
long allocations, frees, active_count, peak, bad;
static void *active[64];
void *__wrap_malloc(size_t n) {
    void *p = __real_malloc(n);
    allocations++;
    if (!p) return p;
    for (int i=0;i<64;i++) if (active[i] == p) bad++;
    for (int i=0;i<64;i++) if (!active[i]) {
        active[i] = p; active_count++;
        if (active_count > peak) peak = active_count;
        return p;
    }
    bad++; return p;
}
void __wrap_free(void *p) {
    frees++;
    int found = 0;
    for (int i=0;i<64;i++) if (active[i] == p) {
        active[i] = 0; active_count--; found++;
    }
    if (found != 1) bad++;
    __real_free(p);
}
'''


def bind(name, ty, value, body):
    return f'(app (lam {name} {ty} {body}) {value})'


def source():
    body = '(add (add first second) third)'
    body = bind('third', 'I64', '(app consume z)', body)
    body = bind('second', 'I64', '(app consume y)', body)
    body = bind('z', '(Buffer 1)', '(alloc 1 c)', body)
    body = bind('first', 'I64', '(app consume x)', body)
    body = bind('y', '(Buffer 1)', '(alloc 1 b)', body)
    body = bind('x', '(Buffer 1)', '(alloc 1 a)', body)
    return CALLEE + f'''(export run (pi a I64 (pi b I64 (pi c I64 I64)))
 (lam a I64 (lam b I64 (lam c I64 {body}))))\n'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    compiler = str(Path(parser.parse_args().compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='linear-heap-') as directory:
        tmp = Path(directory)
        core = tmp / 'linear.jhc'
        text = source()
        core.write_text(text)
        command([compiler, 'core', 'check', core])
        command([compiler, 'core', 'preserves', core])
        counter = tmp / 'counter.c'
        counter.write_text(COUNTER)
        cc = shlex.split(os.environ.get('JIHOO_CC', 'clang'))
        cases = 0
        for level in ('-O0', '-O2'):
            obj = tmp / f'linear{level}.o'
            command([compiler, 'core', 'emit-obj', core, level, '-o', obj])
            library = tmp / f'linear{level}.so'
            command([*cc, '-shared', '-fPIC', obj, counter, '-o', library,
                     '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
            native = ctypes.CDLL(str(library))
            stats = {name: ctypes.c_long.in_dll(native, name) for name in
                     ('allocations', 'frees', 'active_count', 'peak', 'bad')}
            function = native.run
            function.argtypes = [ctypes.c_int64] * 3
            function.restype = ctypes.c_int64
            for a in (-42, 0, 7, 42):
                for b in (-7, 0, 7, 42):
                    for c in (-42, 0, 7, 42):
                        before = (stats['allocations'].value, stats['frees'].value)
                        require(function(a, b, c) == a + b + c, 'wrong returned scalar')
                        allocated = stats['allocations'].value - before[0]
                        freed = stats['frees'].value - before[1]
                        require(allocated == freed and 0 <= allocated <= 3, 'allocation imbalance')
                        require(level != '-O0' or allocated == 3, 'O0 lost required allocations')
                        require(stats['active_count'].value == 0 and stats['bad'].value == 0,
                                'leak, duplicate allocation identity or invalid free')
                        cases += 1
            other = 'aarch64-linux' if platform.machine() == 'x86_64' else 'x86_64-linux'
            command([compiler, 'core', 'emit-obj', core, level, '--target', other,
                     '-o', tmp / f'other{level}.o'])
        mutations = {
            'reuse-consumed': text.replace('(app consume y)', '(add (app consume x) (app consume y))'),
            'leaked-owner': text.replace('(app consume z)', '(int 0)'),
            'duplicate-later': text.replace('(app consume z)', '(add (app consume y) (app consume z))'),
        }
        for name, bad in mutations.items():
            path = tmp / f'{name}.jhc'
            path.write_text(bad)
            result = command([compiler, 'core', 'check', path], success=False)
            expected = ('an owned value must be used: freed, moved or returned'
                        if name == 'leaked-owner' else 'an owned value is used more than once')
            require(expected in result.stderr, f'{name}: wrong diagnostic: {result.stderr}')
            obj = tmp / f'{name}.o'
            command([compiler, 'core', 'emit-obj', path, '-o', obj], success=False)
            require(not obj.exists(), 'invalid caller emitted object')
        print(f'linear heap: {cases} native comparisons, 4 target objects, 3 rejected callers')


if __name__ == '__main__':
    main()
