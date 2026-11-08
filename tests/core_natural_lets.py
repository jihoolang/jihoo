"""Immutable natural let definitions retain typing and initializer traps."""
import json
import ctypes
import os
import platform
import shlex
from core_buffer import COUNTER

PREFIX = '#![dependent_core]\n'
PROGRAM = PREFIX + '''
import dependent.range
fn bound(n: u64, offset: u64, count: u64, start: erased(Lt(offset, n + 1))) -> i64 {
    let remaining = sub(n, offset, start)
    if_lt(count, remaining + 1, fn(fits) {
        let p: Lt(offset + count, n + 1) = lt_add(count, remaining + 1, offset, fits)
        1
    }, 0)
}
fn shifted(n: u64) -> Eq(n + 2, 2 + n) {
    let next = n + 1
    let next = next + 1
    refl(next)
}
fn shadow(n: u64) -> Eq(n, n) {
    let x = n + 1
    let f = fn(x: u64) -> Eq(x, x) { refl(x) }
    f(n)
}
export fn stable(n: u64) -> u64 {
    let observed = free(alloc(1, 7), n)
    let alias = observed + 1
    alias + alias
}
export fn test(n: u64, offset: u64, count: u64) -> i64 {
    if_lt(offset, n + 1, fn(start) { bound(n, offset, count, start) }, -1)
}
fn sum(n: u64, selected: ref buffer(n)) -> i64 {
    fold(n, 0, fn(i, p, total) { total + index(selected, i, p) })
}
export fn copied(n: u64, offset: u64, count: u64) -> i64 {
    let source = alloc(n, 7)
    if_lt(offset, n + 1, fn(start) {
        let remaining = sub(n, offset, start)
        if_lt(count, remaining + 1, fn(fits) {
            let selected = range.copy(n, source, offset, count,
                lt_add(count, remaining + 1, offset, fits))
            sum(count, selected)
        }, -2)
    }, -1)
}
fn main() -> i64 {
    let p = shifted(5)
    let q = shadow(6)
    test(10, 3, 7) + test(10, 3, 8) + test(10, 11, 0)
}
'''
INVALID = {
    'wrong-definition': 'fn bad(n: u64) -> Eq(n, n + 1) { let x = n + 1; refl(x) }',
    'shadowed-definition': 'fn bad(n: u64) -> Eq(n, n) { let x = n; let x = n + 1; refl(x) }',
    'bad-subtraction': 'fn bad(n: u64) -> u64 { let x = sub(n, 1, decide_lt(0, 1)); x }',
    'bad-unused-subtraction': 'fn bad(n: u64) -> u64 { let x = sub(n, 1, decide_lt(0, 1)); 0 }',
    'false-range': '''fn bad(n: u64, offset: u64, count: u64, start: erased(Lt(offset, n + 1))) -> i64 {
        let remaining = sub(n, offset, start)
        if_lt(count, remaining + 1, fn(fits) {
            let p: Lt(offset + count + 1, n + 1) = lt_add(count, remaining + 1, offset, fits)
            1
        }, 0)
    }''',
    'effectful-alias': 'fn bad(n: u64) -> i64 { let x = free(alloc(1, 7), n); let p: Eq(x, n) = refl(n); 0 }',
    'call-alias': 'fn identity(n: u64) -> u64 { n } fn bad(n: u64) -> i64 { let x = identity(n); let p: Eq(x, n) = refl(n); 0 }',
}


def validate_natural_lets(compiler, root, temporary, environment, run):
    def command(action, path, *args, success=True):
        return run([compiler, action, str(path), *args], success=success, env={**environment, 'JIHOO_NO_ELAB': '1'})
    source = temporary / 'natural-lets.jh'
    source.write_text(PROGRAM)
    command('check', source)
    for level in ('-O0', '-O2'):
        assert command('run', source, level).returncode == 0
    formatted = temporary / 'natural-lets-formatted.jh'
    formatted.write_text(command('fmt', source).stdout)
    assert command('fmt', formatted).stdout == formatted.read_text()
    assert command('emit-mir', source).stdout == command('emit-mir', formatted).stdout
    runtime = temporary / 'natural-lets-runtime.jh'
    runtime.write_text(PROGRAM.split('fn main()')[0])
    counter = temporary / 'natural-let-counter.c'
    counter.write_text(COUNTER)
    for target, machine in (('x86_64', 62), ('aarch64', 183)):
        for level in ('-O0', '-O2'):
            obj = temporary / f'natural-lets-{target}{level}.o'
            command('emit-obj', runtime, '--lib', '--target', target, level, '-o', str(obj))
            data = obj.read_bytes()
            assert data[:4] == b'\x7fELF' and int.from_bytes(data[18:20], 'little') == machine
            if target == {'AMD64': 'x86_64', 'arm64': 'aarch64'}.get(platform.machine(), platform.machine()):
                shared = temporary / f'natural-lets-{target}{level}.so'
                run([*shlex.split(os.environ.get('JIHOO_CC', 'clang')), '-shared', '-fPIC', str(obj), str(counter), '-o', str(shared), '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
                native = ctypes.CDLL(str(shared))
                allocations = ctypes.c_long.in_dll(native, 'allocations')
                frees = ctypes.c_long.in_dll(native, 'frees')
                native.stable.argtypes = [ctypes.c_uint64]
                native.stable.restype = ctypes.c_uint64
                for n in (0, 1, 100):
                    allocations.value = frees.value = 0
                    assert native.stable(n) == 2 * (n + 1)
                    assert allocations.value == frees.value
                    if level == '-O0': assert allocations.value == 1
                native.test.argtypes = [ctypes.c_uint64] * 3
                native.test.restype = ctypes.c_int64
                for n in (0, 1, 2, 10, 65536, (1 << 64) - 2):
                    for offset in (0, n // 2, n, n + 1):
                        for count in (0, 1, n // 2, n):
                            expected = -1 if offset > n else int(count <= n - offset)
                            assert native.test(n, offset, count) == expected, (level, n, offset, count)
                native.copied.argtypes = [ctypes.c_uint64] * 3
                native.copied.restype = ctypes.c_int64
                for n in range(9):
                    for offset in range(n + 2):
                        for count in range(n + 2):
                            expected = -1 if offset > n else -2 if count > n - offset else 7 * count
                            allocations.value = frees.value = 0
                            assert native.copied(n, offset, count) == expected, (level, n, offset, count)
                            assert allocations.value == frees.value
                            if level == '-O0': assert allocations.value == (2 if expected >= 0 else 1)
    for name, body in {
        'unused': 'let x: u64 = 18446744073709551615 + 1; 0',
        'ghost-use': 'let x: u64 = 18446744073709551615 + 1; let p = refl(x); 0',
        'branch': 'let x: u64 = 18446744073709551615 + 1; if_eq(0, 0, fn(p) { 0 }, if_eq(x, 0, fn(q) { 1 }, 2))',
    }.items():
        trap = temporary / f'natural-let-trap-{name}.jh'
        trap.write_text(PREFIX + 'fn main() -> i64 { ' + body + ' }')
        for level in ('-O0', '-O2'):
            assert command('run', trap, level, success=False).returncode == 132
    flags = ('--lib', '--release', '--no-verify', '--error-format=json')
    control = temporary / 'natural-let-control.jh'
    control.write_text(PREFIX + 'fn good(n: u64) -> Eq(n + 1, n + 1) { let x = n + 1; refl(x) }\nexport fn anchor() -> i64 { 0 }')
    obj = temporary / 'natural-let-control.o'
    command('emit-obj', control, *flags, '-o', str(obj))
    assert obj.exists()
    for name, body in INVALID.items():
        bad = temporary / f'natural-let-{name}.jh'
        bad.write_text(PREFIX + body + '\nexport fn anchor() -> i64 { 0 }')
        obj = temporary / f'natural-let-{name}.o'
        for action, options in (('check', ()), ('emit-obj', ('-o', str(obj)))):
            result = command(action, bad, *flags, *options, success=False)
            errors = [d for d in json.loads(result.stderr)['diagnostics'] if d['severity'] == 'error']
            assert result.returncode == 1 and len(errors) == 1, (name, result.stderr)
            assert errors[0]['message'] == 'core: type mismatch', (name, result.stderr)
        assert not obj.exists()
    print('natural lets: range conversion, shadowing, both targets, O0/O2 traps and 7 exact rejections passed')
