"""Owned range snapshots: offset evidence, erasure and independent storage."""
import ctypes
import os
import platform
import re
import shlex
import struct
from core_buffer import COUNTER

PREFIX = '#![dependent_core]\nimport dependent.range\n'
# Separate scalar exports make comparison independent of exported buffer ABI.
CHECKED = PREFIX + '''
fn read(n: u64, xs: ref buffer(n)) -> i64 {
    fold(n, 0, fn(i, p, acc) { acc + index(xs, i, p) })
}
export fn copied(n: u64, offset: u64, count: u64, x: i64) -> i64 {
    let source = alloc(n, x)
    if_lt(offset, n + 1, fn(start) {
        if_lt(count, sub(n, offset, start) + 1, fn(fits) {
            let result: buffer(count) = range.copy(n, source, offset, count,
                lt_add(count, sub(n, offset, start) + 1, offset, fits))
            read(count, result)
        }, -1)
    }, -1)
}
'''
PRIMITIVE = """
fn primitive_copy(n: erased(u64), source: ref buffer(n), offset: u64, count: u64,
    fits: erased(Lt(offset + count, n + 1))) -> buffer(count) {
    fold(count, alloc(count, 0), fn(i, p, acc) {
        store(acc, i, index(source, offset + i,
            lt_le(offset + i, offset + count, n, lt_add(i, count, offset, p), fits)), p)
    })
}
"""
REFERENCE = CHECKED.replace('import dependent.range\n', PRIMITIVE).replace('range.copy(', 'primitive_copy(')
EXTRA = '''
fn digits(n: u64, xs: ref buffer(n)) -> i64 {
    fold(n, 0, fn(i, p, acc) { acc * 10 + index(xs, i, p) })
}
fn ascending(n: u64, values: [i64; n]) -> buffer(n) {
    fold(n, alloc(n, 0), fn(i, p, acc) { store(acc, i, index(values, i, p), p) })
}
export fn order(offset: u64, count: u64) -> i64 {
    let source = ascending(8, [0, 1, 2, 3, 4, 5, 6, 7])
    if_lt(offset, 9, fn(start) {
        if_lt(count, sub(8, offset, start) + 1, fn(fits) {
            let result: buffer(count) = range.copy(8, source, offset, count,
                lt_add(count, sub(8, offset, start) + 1, offset, fits))
            digits(count, result)
        }, -1)
    }, -1)
}
fn snapshot(source: ref buffer(4)) -> buffer(2) {
    range.copy(4, source, 1, 2, decide_lt(3, 5))
}
export fn independent() -> i64 {
    let source = ascending(4, [0, 1, 2, 3])
    let result = snapshot(source)
    let changed = store(source, 1, 9, decide_lt(1, 4))
    let a = digits(2, result)
    a * 10000 + digits(4, changed)
}
export fn retained() -> i64 {
    let source = ascending(4, [0, 1, 2, 3])
    let result = snapshot(source)
    let a = digits(4, source)
    a * 100 + digits(2, result)
}
fn temporary_snapshot() -> buffer(2) {
    let source = ascending(4, [0, 1, 2, 3])
    snapshot(source)
}
export fn released() -> i64 {
    let result = temporary_snapshot()
    digits(2, result)
}
export fn signed(x: i64) -> i64 {
    let source = alloc(1, x)
    let result: buffer(1) = range.copy(1, source, 0, 1, decide_lt(1, 2))
    index(result, 0, decide_lt(0, 1))
}
// A symbolic endpoint is ghost even when n is maximal at runtime.
export fn ghost_endpoint(n: u64) -> u64 {
    let p = range.offset_lt(n + 1, n, 1, 0,
        lt_add(0, 1, n + 1, decide_lt(0, 1)), decide_lt(0, 1))
    n
}
'''
INVALID = {
    'past-end': ('fn bad(xs: ref buffer(3)) -> buffer(2) { range.copy(3, xs, 2, 2, decide_lt(4, 4)) }', 'decide-lt needs a true closed inequality'),
    'wrong-result': ('fn bad(xs: ref buffer(3)) -> buffer(3) { range.copy(3, xs, 0, 2, decide_lt(2, 4)) }', 'type mismatch'),
    'wrong-source': ('fn bad(xs: ref buffer(3)) -> buffer(2) { range.copy(4, xs, 0, 2, decide_lt(2, 5)) }', 'type mismatch'),
    'missing-proof': ('fn bad(xs: ref buffer(3)) -> buffer(2) { range.copy(3, xs, 0, 2, refl(0)) }', 'type mismatch'),
    'duplicate-owner': ('fn bad(xs: ref buffer(3)) -> i64 { let ys: buffer(2) = range.copy(3, xs, 0, 2, decide_lt(2, 4)); free(ys, free(ys, 0)) }', 'an owned value is used more than once'),
    'borrowed-result': ('fn bad(xs: ref buffer(3)) -> buffer(3) { xs }', 'type mismatch'),
    'relative-end': ('fn bad(n: u64, o: u64, k: u64, fits: erased(Lt(o + k, n + 1))) -> Lt(o + k, n) { range.offset_lt(n, o, k, k, fits, decide_lt(k, k)) }', 'decide-lt needs a true closed inequality'),
    'wrong-offset': ('fn bad(n: u64, o: u64, k: u64, i: u64, fits: erased(Lt(o + k, n + 1)), p: erased(Lt(i, k))) -> Lt(o + i + 1, n) { range.offset_lt(n, o, k, i, fits, p) }', 'type mismatch'),
}


def validate_range(compiler, root, temporary, environment, run):
    def command(action, path, *args, success=True, env=environment):
        return run([compiler, action, str(path), *args], success=success, env=env)

    checked, reference = temporary/'range-checked.jh', temporary/'range-reference.jh'
    checked.write_text(CHECKED); reference.write_text(REFERENCE)
    mir = command('emit-mir', checked, '--lib').stdout
    assert mir == command('emit-mir', reference, '--lib').stdout
    # An imported proof theorem alone is exactly erased.
    ghost = temporary/'range-ghost.jh'
    ghost.write_text(CHECKED + EXTRA[EXTRA.index('// A symbolic endpoint'):])
    ghost_reference = temporary/'range-ghost-reference.jh'
    ghost_reference.write_text(CHECKED + '\nexport fn ghost_endpoint(n: u64) -> u64 { n }\n')
    assert command('emit-mir', ghost, '--lib').stdout == command('emit-mir', ghost_reference, '--lib').stdout
    source = temporary/'range.jh'; source.write_text(CHECKED + EXTRA)
    command('check', source, '--lib', env={**environment, 'JIHOO_LLVM':'/unavailable', 'JIHOO_CC':'/unavailable'})
    formatted = temporary/'range-formatted.jh'; formatted.write_text(command('fmt', source).stdout)
    assert command('fmt', formatted).stdout == formatted.read_text()
    assert command('emit-mir', formatted, '--lib').stdout == command('emit-mir', source, '--lib').stdout
    guide = temporary/'range-guide.jh'
    guide.write_text(re.search(r'```jihoo\n(.*?)```', (root/'docs/language/buffer-ranges.md').read_text(), re.S).group(1))
    for level in ('-O0', '-O2'):
        assert command('run', guide, level, success=False).returncode == 17
    counter = temporary/'range-counter.c'; counter.write_text(COUNTER)
    host = 'aarch64' if platform.machine() in ('aarch64', 'arm64') else 'x86_64'
    for target, machine in (('x86_64', 62), ('aarch64', 183)):
        for level in ('-O0', '-O2'):
            obj = temporary/f'range-{target}{level}.o'
            command('emit-obj', source, '--lib', '--target', target, level, '-o', str(obj))
            assert struct.unpack_from('<H', obj.read_bytes(), 18)[0] == machine
            if target != host:
                continue
            shared = temporary/f'range{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC', 'clang')), '-shared', '-fPIC', str(obj), str(counter), '-o', str(shared), '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
            native = ctypes.CDLL(str(shared))
            allocations = ctypes.c_long.in_dll(native, 'allocations')
            frees = ctypes.c_long.in_dll(native, 'frees')
            def call(name, args, expected, mallocs=None):
                fn = getattr(native, name)
                fn.argtypes = [ctypes.c_uint64] * len(args)
                if name == 'copied': fn.argtypes[-1] = ctypes.c_int64
                if name == 'signed': fn.argtypes[-1] = ctypes.c_int64
                fn.restype = ctypes.c_int64
                allocations.value = frees.value = 0
                assert fn(*args) == expected, (name, args, expected)
                assert allocations.value == frees.value, (name, args, allocations.value, frees.value)
                if level == '-O0' and mallocs is not None:
                    assert allocations.value == mallocs, (name, args, allocations.value, mallocs)
            native.ghost_endpoint.argtypes = [ctypes.c_uint64]
            native.ghost_endpoint.restype = ctypes.c_uint64
            for n in (0, 1, (1 << 64) - 1):
                assert native.ghost_endpoint(n) == n
            for n in range(9):
                for offset in range(n + 2):
                    for count in range(n + 2):
                        valid = offset <= n and count <= n - offset
                        call('copied', (n, offset, count, -3), -3 * count if valid else -1, 2 if valid else 1)
            for offset in range(10):
                for count in range(10):
                    valid = offset <= 8 and count <= 8 - offset
                    value = int(''.join(map(str, range(offset, offset + count))) or '0') if valid else -1
                    call('order', (offset, count), value, 2 if valid else 1)
            for name, expected in (('independent', 120923), ('retained', 12312), ('released', 12)):
                call(name, (), expected, 2)
            for x in (-(1 << 63), -1, 0, 1, (1 << 63) - 1):
                call('signed', (x,), x, 2)
            assert command('run', root/'examples/core_range.jh', level, success=False).returncode == 30
    anchor = '\nexport fn positive_anchor() -> i64 { 0 }\n'
    positive = temporary/'range-positive.jh'; positive.write_text(PREFIX + anchor)
    command('emit-obj', positive, '--lib', '-o', str(temporary/'range-positive.o'))
    for name, (body, expected) in INVALID.items():
        path = temporary/f'range-invalid-{name}.jh'; path.write_text(PREFIX + body + anchor)
        for action, options, env in (
            ('check', [], environment),
            ('emit-obj', ['--release', '--no-verify', '-o', str(temporary/'range-invalid.o')], {**environment, 'JIHOO_NO_ELAB':'1'}),
        ):
            result = command(action, path, '--lib', *options, success=False, env=env)
            assert expected in result.stderr, (name, result.stderr)
    # Check malformed unused library evidence, not only consumers' signatures.
    original = (root/'lib/dependent/range.jh').read_text()
    for name, old, new in (
        ('false-offset', 'lt_le(offset + i, offset + count, n, lt_add(i, count, offset, inside), fits)', 'lt_add(i, count, offset, inside)'),
        ('wrong-copy', 'index(source, offset + i, offset_lt(n, offset, count, i, fits, p))', 'index(source, offset + i + 1, offset_lt(n, offset, count, i, fits, p))'),
    ):
        assert old in original
        module = 'broken_range_' + name.replace('-', '_')
        path = temporary/f'{module}.jh'
        path.write_text(original.replace(old, new))
        importer = temporary/f'range-import-{name}.jh'
        importer.write_text(f'#![dependent_core]\nimport {module}\n' + anchor)
        for action, options in (('check', []), ('emit-obj', ['-o', str(temporary/'range-broken.o')])):
            result = command(action, importer, '--lib', '--release', '--no-verify', *options,
                success=False, env={**environment, 'JIHOO_NO_ELAB':'1'})
            assert 'type mismatch' in result.stderr and str(path) in result.stderr, (name, result.stderr)
    # Proof erasure cannot remove real arithmetic/allocation traps.
    for name, body in (
        ('allocation-overflow', 'fn main() -> i64 { let source = alloc(0, 0); let result: buffer(0) = range.copy(0, source, 0, 0, decide_lt(0, 1)); free(alloc(18446744073709551615, 0), 0) }'),
        ('runtime-overflow', 'fn main() -> i64 { let n: u64 = 18446744073709551615; if_lt(0, n + 1, fn(p) { 1 }, 0) }'),
    ):
        path = temporary/f'range-trap-{name}.jh'; path.write_text(PREFIX + body)
        for level in ('-O0', '-O2'):
            result = command('run', path, level, success=False)
            assert result.returncode == 132, (name, level, result.stderr)
