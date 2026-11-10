#!/usr/bin/env python3
"""Actual owned-producing App arguments preserve identities across caller binding.
Constant-payload chains exercise the formal capture-free consumer boundary.
Producers may read their original context; cases whose nested consumers capture
outer scalars add native evidence beyond the singleton-consumer rule.
This is not a general lowering proof.
"""
import argparse
import ctypes
import os
from pathlib import Path
import shlex
import tempfile
from core_linear_heap import bind
from core_mixed_lend import lend
from core_scoped_lend import command, require

COUNTER = r'''
#include <stddef.h>
void *__real_malloc(size_t);
void __real_free(void *);
long allocations, frees, active_count, peak, bad, free_count;
long freed_ids[64];
static void *active[64];
static long ids[64];
void *__wrap_malloc(size_t n) {
    void *p = __real_malloc(n);
    long id = allocations++;
    if (!p) { bad++; return p; }
    for (int i=0; i<64; i++) if (active[i] == p) bad++;
    for (int i=0; i<64; i++) if (!active[i]) {
        active[i] = p; ids[i] = id; active_count++;
        if (active_count > peak) peak = active_count;
        return p;
    }
    bad++; return p;
}
void __wrap_free(void *p) {
    frees++;
    int found = 0;
    for (int i=0; i<64; i++) if (active[i] == p) {
        if (free_count < 64) freed_ids[free_count++] = ids[i]; else bad++;
        active[i] = 0; active_count--; found++;
    }
    if (found != 1) bad++;
    /* Do not let an invalid free hide the diagnostic behind an allocator abort. */
    if (found == 1) __real_free(p);
}
'''


def source(name, second, depth, replace, captured):
    a, b = ('a', 'b') if captured else ('(int 11)', '(int 37)')
    tail = '(free left right)' if second else '(free right left)'
    expr = bind('left', '(Buffer 1)', f'(alloc 1 {a})',
                bind('right', '(Buffer 1)', f'(alloc 1 {b})', tail))
    selected = 1 if second else 0
    freed = [0 if second else 1]
    for i in range(depth):
        # The argument is an owned-producing application, not a variable.
        new = i + 2
        tail = '(free prior scratch)' if replace else '(free scratch prior)'
        expr = bind('prior', '(Buffer 1)', expr,
                    bind('scratch', '(Buffer 1)', f'(alloc 1 {b})', tail))
        freed.append(selected if replace else new)
        if replace:
            selected = new
    freed.append(selected)
    body = bind('received', '(Buffer 1)', expr,
                lend('received', 'answer', 'returned', '(free returned answer)'))
    text = f'(export {name} (pi a I64 (pi b I64 I64)) (lam a I64 (lam b I64 {body})))\n'
    return text, freed, second or (replace and depth > 0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    compiler = str(Path(parser.parse_args().compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='owned-call-') as directory:
        tmp = Path(directory)
        specs, texts = [], []
        for second in (False, True):
            for depth in (0, 1, 3):
                for replace in (False, True):
                    for captured in (False, True):
                        name = f'f{len(specs)}'
                        text, free_order, from_b = source(name, second, depth, replace, captured)
                        texts.append(text)
                        specs.append((name, depth, captured, from_b, free_order))
        core = tmp / 'calls.jhc'; core.write_text(''.join(texts))
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
                     ('allocations', 'frees', 'active_count', 'peak', 'bad', 'free_count')}
            freed_ids = (ctypes.c_long * 64).in_dll(native, 'freed_ids')
            for name, depth, captured, from_b, free_order in specs:
                fn = getattr(native, name); fn.argtypes = [ctypes.c_int64]*2; fn.restype = ctypes.c_int64
                for a, b in ((11, 37), (37, 11), (7, 7), (-7, 42), (0, 0)):
                    before = stats['allocations'].value, stats['frees'].value
                    stats['peak'].value = stats['free_count'].value = 0
                    left, right = (a, b) if captured else (11, 37)
                    require(fn(a, b) == (right if from_b else left), f'{name}: wrong result')
                    delta = stats['allocations'].value-before[0], stats['frees'].value-before[1]
                    require(delta[0] == delta[1] and 0 <= delta[0] <= depth+2,
                            f'{name}: unbalanced lifecycle {delta}')
                    if level == '-O0':
                        require(delta == (depth+2, depth+2) and stats['peak'].value == 2,
                                f'{name}: producer/caller allocation boundary lost')
                        actual = [freed_ids[i]-before[0] for i in range(stats['free_count'].value)]
                        require(actual == free_order,
                                f'{name}: wrong owner identities/order {actual} != {free_order}')
                    require(stats['active_count'].value == 0 and stats['bad'].value == 0,
                            f'{name}: invalid free or leak')
                    cases += 1
        invalid = {
            'stale-producer-owner': ('an owned value is used more than once',
                bind('result', '(Buffer 1)', bind('moved', '(Buffer 1)', 'x', 'moved'),
                     '(free x (free result (int 9)))')),
            'argument-leaks': ('an owned value must be used',
                bind('result', '(Buffer 1)', bind('lost', '(Buffer 1)', '(alloc 1 (int 9))', 'x'),
                     '(free result (int 9))')),
            'body-leaks-result': ('an owned value must be used',
                bind('result', '(Buffer 1)', bind('moved', '(Buffer 1)', 'x', 'moved'), '(int 9)')),
            'body-double-free': ('an owned value is used more than once',
                bind('result', '(Buffer 1)', bind('moved', '(Buffer 1)', 'x', 'moved'),
                     '(free result (free result (int 9)))')),
            'wrong-argument-kind': ('type mismatch',
                bind('result', '(Buffer 1)', '(free x (int 9))', '(free result (int 9))')),
        }
        for name, (diagnostic, body) in invalid.items():
            path = tmp / f'{name}.jhc'
            path.write_text(f'(def bad (pi x (Buffer 1) I64) (lam x (Buffer 1) {body}))')
            failed = command([compiler, 'core', 'check', path], success=False)
            require(diagnostic in failed.stderr, f'{name}: unexpected diagnostic: {failed.stderr}')
            obj = tmp / f'{name}.o'
            command([compiler, 'core', 'emit-obj', path, '-o', obj], success=False)
            require(not obj.exists(), f'{name}: invalid program emitted object')
        print(f'owned-call: {len(specs)} variants, {cases} native lifecycles, {len(invalid)} rejects')


if __name__ == '__main__':
    main()
