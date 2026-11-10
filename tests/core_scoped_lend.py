#!/usr/bin/env python3
"""Native scalar-Lend regressions, not a Lean implementation-refinement proof.
Runtime Index observes Ref(Buffer(1)); ghost-only Deref is not executed.
"""
import argparse
import ctypes
import os
from pathlib import Path
import platform
import shlex
import subprocess
import tempfile
from core_buffer import COUNTER

READ = '(index r 0 (decide-lt 0 1))'
BODY = f'(app (lam ignored I64 (if-lt flag 1 q {READ} (int 7))) {READ})'


def source():
    declarations = []
    for name, continuation in (
        ('returned', '(free y a)'), ('original', '(free xs a)'),
        ('stored', '(free (store y 0 a (decide-lt 0 1)) a)'),
    ):
        declarations.append(f'''(export {name} (pi flag U64 (pi value I64 I64))
 (lam flag U64 (lam value I64
  (app (lam xs (Buffer 1)
   (lend xs (lam r (Ref (Buffer 1)) {BODY})
    (lam a I64 (lam y (Buffer 1) {continuation}))))
   (alloc 1 value)))))''')
    return '\n'.join(declarations) + '\n'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def command(argv, *, success=True):
    result = subprocess.run(list(map(str, argv)), capture_output=True, text=True, timeout=180)
    require((result.returncode == 0) == success,
            f'{argv}: {result.returncode}\n{result.stdout}\n{result.stderr}')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    args = parser.parse_args()
    compiler = str(Path(args.compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='jihoo-scoped-lend-') as directory:
        tmp = Path(directory)
        core = tmp / 'scoped.jhc'
        core.write_text(source())
        command([compiler, 'core', 'check', core])
        command([compiler, 'core', 'preserves', core])
        counter = tmp / 'counter.c'
        counter.write_text(COUNTER)
        cc = shlex.split(os.environ.get('JIHOO_CC', 'clang'))
        cases = 0
        for level in ('-O0', '-O2'):
            obj = tmp / f'scoped{level}.o'
            command([compiler, 'core', 'emit-obj', core, level, '-o', obj])
            library = tmp / f'scoped{level}.so'
            command([*cc, '-shared', '-fPIC', obj, counter, '-o', library,
                     '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
            native = ctypes.CDLL(str(library))
            allocations = ctypes.c_long.in_dll(native, 'allocations')
            frees = ctypes.c_long.in_dll(native, 'frees')
            for name in ('returned', 'original', 'stored'):
                function = getattr(native, name)
                function.argtypes = [ctypes.c_uint64, ctypes.c_int64]
                function.restype = ctypes.c_int64
                for flag in (0, 1, 2, (1 << 64) - 1):
                    for value in (-9223372036854775808, -7, 0, 42, 9223372036854775807):
                        before = (allocations.value, frees.value)
                        require(function(flag, value) == (value if flag == 0 else 7),
                                f'{level} {name} returned wrong scalar')
                        delta = (allocations.value - before[0], frees.value - before[1])
                        require(delta in (((1, 1),) if level == '-O0' else ((0, 0), (1, 1))),
                                f'{level} {name} allocation imbalance: {delta}')
                        cases += 1
            other = 'aarch64-linux' if platform.machine() == 'x86_64' else 'x86_64-linux'
            command([compiler, 'core', 'emit-obj', core, level, '--target', other,
                     '-o', tmp / f'other{level}.o'])
        bad = {
            'reader-free': source().replace(BODY, '(free xs (int 0))'),
            'both-owner-names': source().replace('(free y a)', '(free y (free xs a))'),
            'borrow-escape': '''(def bad (pi xs (Buffer 1) (Ref (Buffer 1)))
 (lam xs (Buffer 1) (lend xs (lam r (Ref (Buffer 1)) r)
 (lam a (Ref (Buffer 1)) (lam y (Buffer 1) (free y a))))))''',
        }
        for name, text in bad.items():
            path = tmp / f'{name}.jhc'
            path.write_text(text)
            result = command([compiler, 'core', 'check', path], success=False)
            expected = {
                'reader-free': 'an owned value is used more than once',
                'both-owner-names': 'a lent owner is used exactly once after its lend',
                'borrow-escape': 'a borrow cannot outlive its lend',
            }[name]
            require(expected in result.stderr, f'{name}: wrong rejection: {result.stderr}')
            output = tmp / f'{name}.o'
            command([compiler, 'core', 'emit-obj', path, '-o', output], success=False)
            require(not output.exists(), f'{name}: invalid program emitted object')
        print(f'scoped Lend: {cases} native comparisons, 4 target objects, 3 rejected mutations')


if __name__ == '__main__':
    main()
