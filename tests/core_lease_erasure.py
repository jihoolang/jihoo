#!/usr/bin/env python3
"""Native lease erasure regressions. MIR observations are not a simulation proof."""
import argparse
import ctypes
import os
from pathlib import Path
import re
import shlex
import tempfile
from core_scoped_lend import command, require

READ = '(index r 0 (decide-lt 0 1))'
OWNER_READ = '(index (borrow xs) 0 (decide-lt 0 1))'
COUNTER = r'''
#include <stddef.h>
#include <stdint.h>
void *__real_malloc(size_t);
void __real_free(void *);
long allocations, frees;
int64_t at_free;
void *__wrap_malloc(size_t n) { allocations++; return __real_malloc(n); }
void __wrap_free(void *p) { frees++; at_free = *(int64_t *)p; __real_free(p); }
'''


def source(name='run', reader=READ, continuation='(free y a)'):
    return f'''(export {name} (pi value I64 I64)
 (lam value I64 (app (lam xs (Buffer 1)
  (lend xs (lam r (Ref (Buffer 1)) {reader})
   (lam a I64 (lam y (Buffer 1) {continuation})))) (alloc 1 value))))'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    compiler = str(Path(parser.parse_args().compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='lease-erasure-') as directory:
        tmp = Path(directory)
        def mir(text, name):
            path = tmp / f'{name}.jhc'
            path.write_text(text)
            command([compiler, 'core', 'check', path])
            command([compiler, 'core', 'preserves', path])
            return command([compiler, 'core', 'emit-mir', path, '-O0']).stdout
        ordinary = mir(source(), 'reader-ref')
        require(ordinary == mir(source(reader=OWNER_READ), 'owner-borrow'),
                'Borrow introduced runtime structure')
        require(ordinary == mir(source(continuation='(free xs a)'), 'owner-original'),
                'returned-owner alias changed lowered pointer identity')
        identity_store = mir(source(continuation='(free (store y 0 a (decide-lt 0 1)) a)'),
                             'stored-identity')
        # This changed result is also expressible by formal Reader.seq/read/scalar.
        changed_reader = f'(app (lam ignored I64 (int 99)) {READ})'
        changed = mir(source(reader=changed_reader,
                             continuation='(free (store y 0 a (decide-lt 0 1)) a)'), 'changed')
        # Extra native arithmetic case is broader than the formal Reader subset.
        stored_reader = f'(add {READ} (int 1))'
        stored = mir(source(reader=stored_reader,
                            continuation='(free (store y 0 a (decide-lt 0 1)) a)'), 'stored')
        for text in (ordinary, identity_store, changed, stored):
            require(re.findall(r'call ([A-Za-z_][A-Za-z_0-9]*)\(', text) == ['malloc', 'free'],
                    'unexpected runtime calls (possibly lease management)')
            # Normalization may discard the changed fixture's unused pure read.
            if text != changed:
                require(re.search(r'_\d+ = \(\*_\d+\)', text), 'missing pointer payload read')
            require('offset ' in text and '*i64' in text, 'missing ordinary pointer representation')
            require(not any(word in text for word in ('Ref(', 'decide-lt', 'lease', 'borrow', 'lend')),
                    'source lease/evidence marker in MIR')
        require(len(re.findall(r'\(\*_\d+\) =', ordinary)) == 1, 'expected allocation initialization')
        for text in (identity_store, changed, stored):
            require(len(re.findall(r'\(\*_\d+\) =', text)) == 2,
                    'expected initialization then storeResult')
        core = tmp / 'native.jhc'
        core.write_text(source('read_result') + '\n' +
                        source('stored_identity', continuation='(free (store y 0 a (decide-lt 0 1)) a)') + '\n' +
                        source('stored_changed', changed_reader, '(free (store y 0 a (decide-lt 0 1)) a)') + '\n' +
                        source('stored_result', stored_reader,
                        '(free (store y 0 a (decide-lt 0 1)) a)'))
        counter = tmp / 'counter.c'
        counter.write_text(COUNTER)
        cc = shlex.split(os.environ.get('JIHOO_CC', 'clang'))
        cases = 0
        for level in ('-O0', '-O2'):
            obj = tmp / f'{level}.o'
            library = tmp / f'{level}.so'
            command([compiler, 'core', 'emit-obj', core, level, '-o', obj])
            command([*cc, '-shared', '-fPIC', obj, counter, '-o', library,
                     '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
            native = ctypes.CDLL(str(library))
            allocs = ctypes.c_long.in_dll(native, 'allocations')
            frees = ctypes.c_long.in_dll(native, 'frees')
            last = ctypes.c_int64.in_dll(native, 'at_free')
            for name in ('read_result', 'stored_identity', 'stored_changed', 'stored_result'):
                function = getattr(native, name)
                function.argtypes = [ctypes.c_int64]
                function.restype = ctypes.c_int64
                for value in (-(1 << 63), -7, 0, 42, (1 << 63)-2):
                    expected = (99 if name == 'stored_changed' else
                                value + 1 if name == 'stored_result' else value)
                    before = (allocs.value, frees.value)
                    require(function(value) == expected, 'wrong returned scalar')
                    delta = (allocs.value-before[0], frees.value-before[1])
                    require(delta in (((1, 1),) if level == '-O0' else ((0, 0), (1, 1))),
                            'unbalanced allocation/free')
                    # O2 may remove a dead store before free or the whole allocation.
                    # The unoptimized path witnesses the lowering order directly.
                    if level == '-O0':
                        require(last.value == expected, 'store/read payload incorrect at free')
                    cases += 1
        print(f'lease erasure: 6 MIR fixtures, {cases} native results/lifecycles')


if __name__ == '__main__':
    main()
