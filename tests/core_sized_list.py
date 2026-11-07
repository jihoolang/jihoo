"""Owned lists with erased exact lengths and a length-indexed runtime loop."""
import ctypes
import json
import os
import platform
import shlex
import struct

from core_buffer import COUNTER

PREFIX = '#![dependent_core]\nimport dependent.sized_list\nimport dependent.list\n'
ANCHOR = '\nexport fn harness_anchor() -> i64 { 0 }\n'
INVALID = {
    'wrong-result-index': ('fn bad(x: i64) -> sized_list.Sized(2) { sized_list.repeat(1, x) }', 'type mismatch'),
    'wrong-cons-index': ('fn bad(x: i64) -> sized_list.Sized(0) { sized_list.cons(0, x, sized_list.empty()) }', 'type mismatch'),
    'empty-head': ('fn bad() -> i64 { let xs = sized_list.empty(); sized_list.head(0, xs, decide_lt(0, 1)) }', 'type mismatch'),
    'one-past-end': ('fn bad() -> i64 { let xs = sized_list.repeat(1, 7); sized_list.nth(1, xs, 1, decide_lt(0, 1)) }', 'type mismatch'),
    'changed-map-index': ('fn id(x: i64) -> i64 { x }\nfn bad(xs: ref sized_list.Sized(1)) -> sized_list.Sized(2) { sized_list.map(1, xs, id) }', 'type mismatch'),
    'wrong-size-proof': ('fn bad(xs: ref sized_list.Sized(1)) -> Eq(witness(sized_list.size(1, xs)), 2) { proof(sized_list.size(1, xs)) }', 'type mismatch'),
    'private-construction': ('fn bad() -> sized_list.Sized(1) { sized_list.Sized { data: list.List.Nil, exact: refl(0) } }', 'private struct field: data'),
    'private-pattern': ('fn bad(xs: sized_list.Sized(1)) -> list.List { match xs { sized_list.Sized { data, .. } => data } }', 'private struct field: data'),
    'double-owner': ('fn bad(xs: sized_list.Sized(1)) -> u64 { list.into_length(sized_list.into_list(1, xs)) + list.into_length(sized_list.into_list(1, xs)) }', 'an owned value is used more than once'),
}
EXTRA = '''
export fn original(n: u64, i: u64, x: i64) -> i64 {
    let xs = sized_list.repeat(n, x)
    let ys = sized_list.map(n, xs, fn(y: i64) -> i64 { y + 2 })
    if_lt(i, n, fn(p) {
        let before = sized_list.nth(n, xs, i, p)
        before + sized_list.nth(n, ys, i, p)
    }, -1)
}
export fn count(n: u64) -> u64 {
    list.into_length(sized_list.into_list(n, sized_list.repeat(n, 7)))
}
export fn first(x: i64) -> i64 {
    let xs = sized_list.cons(0, x, sized_list.empty())
    sized_list.head(1, xs, decide_lt(0, 1))
}
export fn ordered(i: u64) -> i64 {
    let xs = sized_list.cons(2, 10,
        sized_list.cons(1, 20, sized_list.cons(0, 30, sized_list.empty())))
    let ys = sized_list.map(3, xs, increment)
    if_lt(i, 3, fn(p) { sized_list.nth(3, ys, i, p) }, -1)
}
'''

ERASURE_SOURCE = PREFIX + '''
fn inc(x: i64) -> i64 { x + 1 }
export fn total(n: u64, x: i64) -> i64 {
    let xs = sized_list.repeat(n, x)
    let ys = sized_list.map(n, xs, inc)
    let zs = sized_list.into_list(n, ys)
    list.sum(zs)
}
'''
ERASURE_REFERENCE = '''#![dependent_core]
import dependent.list
struct Sized { data: list.List }
fn empty() -> Sized { Sized { data: list.List.Nil } }
fn cons(x: i64, xs: Sized) -> Sized {
    match xs { Sized { data } => Sized { data: list.List.Cons(x, data) } }
}
fn repeat(n: u64, x: i64) -> Sized {
    fold(n, empty(), fn(i, p, acc) { cons(x, acc) })
}
fn map(xs: ref Sized, f: fn(i64) -> i64) -> Sized {
    match xs { Sized { data } => Sized { data: list.map(data, f) } }
}
fn into_list(xs: Sized) -> list.List { match xs { Sized { data } => data } }
fn inc(x: i64) -> i64 { x + 1 }
export fn total(n: u64, x: i64) -> i64 {
    let xs = repeat(n, x)
    let ys = map(xs, inc)
    let zs = into_list(ys)
    list.sum(zs)
}
'''


def validate_sized_list(compiler, root, temporary, environment, run):
    def command(action, path, *args, success=True, env=environment):
        return run([compiler, action, str(path), *args], success=success, env=env)

    checked = temporary / 'sized-list-erasure.jh'
    reference = temporary / 'sized-list-reference.jh'
    checked.write_text(ERASURE_SOURCE)
    reference.write_text(ERASURE_REFERENCE)
    assert command('emit-mir', checked, '--lib').stdout == command('emit-mir', reference, '--lib').stdout, 'indices or structural evidence changed runtime MIR'
    example = root / 'examples/core_sized_list.jh'
    source = temporary / 'sized-list-library.jh'
    source.write_text(example.read_text() + 'import dependent.list\n' + EXTRA)
    command('check', source, '--lib', env={**environment, 'JIHOO_LLVM': '/unavailable', 'JIHOO_CC': '/unavailable'})
    mir = command('emit-mir', source, '--lib').stdout
    formatted = temporary / 'sized-list-formatted.jh'
    formatted.write_text(command('fmt', source).stdout)
    assert command('fmt', formatted).stdout == formatted.read_text()
    assert command('emit-mir', formatted, '--lib').stdout == mir
    counter = temporary / 'sized-list-counter.c'
    counter.write_text(COUNTER)
    host = 'aarch64' if platform.machine() in ('aarch64', 'arm64') else 'x86_64'
    for target, machine in (('x86_64', 62), ('aarch64', 183)):
        for level in ('-O0', '-O2'):
            obj = temporary / f'sized-list-{target}{level}.o'
            command('emit-obj', source, '--lib', '--target', target, level, '-o', str(obj))
            assert struct.unpack_from('<H', obj.read_bytes(), 18)[0] == machine
            if target != host:
                continue
            shared = temporary / f'sized-list{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC', 'clang')), '-shared', '-fPIC', str(obj), str(counter), '-o', str(shared), '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
            native = ctypes.CDLL(str(shared))
            allocations = ctypes.c_long.in_dll(native, 'allocations')
            frees = ctypes.c_long.in_dll(native, 'frees')
            for name, args, result in (
                ('at', [ctypes.c_uint64, ctypes.c_uint64, ctypes.c_int64], ctypes.c_int64),
                ('original', [ctypes.c_uint64, ctypes.c_uint64, ctypes.c_int64], ctypes.c_int64),
                ('measured', [ctypes.c_uint64, ctypes.c_int64], ctypes.c_uint64),
                ('count', [ctypes.c_uint64], ctypes.c_uint64),
                ('first', [ctypes.c_int64], ctypes.c_int64),
                ('ordered', [ctypes.c_uint64], ctypes.c_int64),
            ):
                getattr(native, name).argtypes = args
                getattr(native, name).restype = result
            for n in range(11):
                before = allocations.value
                assert native.count(n) == n
                # Each iteration replaces its wrapper; n+1 wrappers and List nodes are allocated.
                assert allocations.value - before == 2 * (n + 1), (n, allocations.value - before, level)
                assert allocations.value == frees.value
                for x in (-7, 0, 19):
                    assert native.measured(n, x) == n
                    for i in (*range(12), (1 << 64) - 1):
                        before = allocations.value
                        assert native.at(n, i, x) == (x + 1 if i < n else -1)
                        # Mapping introduces n+1 nodes and a wrapper (eliminated at O2);
                        # structural proofs allocate and traverse nothing at runtime.
                        assert allocations.value - before == 3 * n + (4 if level == "-O0" else 3), (n, i, allocations.value - before, level)
                        assert allocations.value == frees.value
                        assert native.original(n, i, x) == (2 * x + 2 if i < n else -1)
                        assert allocations.value == frees.value
            for i in (0, 1, 2, 3, (1 << 64) - 1):
                assert native.ordered(i) == ([11, 21, 31][i] if i < 3 else -1)
                assert allocations.value == frees.value
            for x in (-(1 << 63), -1, 0, (1 << 63) - 1):
                assert native.first(x) == x
                assert allocations.value == frees.value
    for level in ('-O0', '-O2'):
        assert command('run', example, level, success=False).returncode == 18
        trap = temporary / 'sized-list-map-overflow.jh'
        trap.write_text(example.read_text().replace('at(3, 2, 17)', 'at(1, 0, 9223372036854775807)'))
        assert command('run', trap, level, success=False).returncode == 132
    flags = ('--lib', '--release', '--no-verify', '--error-format=json')
    env = {**environment, 'JIHOO_NO_ELAB': '1'}
    control = temporary / 'sized-list-control.jh'
    control.write_text(PREFIX + 'fn good(n: erased(u64), xs: ref sized_list.Sized(n), i: u64, p: erased(Lt(i, n))) -> i64 { sized_list.nth(n, xs, i, p) }' + ANCHOR)
    command('check', control, *flags, env=env)
    command('emit-obj', control, *flags, '-o', str(temporary / 'sized-list-control.o'), env=env)

    def rejected(path, blame, expected='type mismatch'):
        obj = temporary / 'sized-list-rejected.o'
        for action, options in (('check', ()), ('emit-obj', ('-o', str(obj)))):
            result = command(action, path, *flags, *options, success=False, env=env)
            errors = [d for d in json.loads(result.stderr)['diagnostics'] if d['severity'] == 'error']
            assert result.returncode == 1 and len(errors) == 1, result.stderr
            assert errors[0]['kind'] == 'source' and errors[0]['message'] == 'core: ' + expected, result.stderr
            assert errors[0]['span']['file'] == str(blame), result.stderr
        assert not obj.exists()

    for name, (body, expected) in INVALID.items():
        bad = temporary / f'sized-list-{name}.jh'
        bad.write_text(PREFIX + body + ANCHOR)
        rejected(bad, bad, expected)
    module = (root / 'lib/dependent/sized_list.jh').read_text()
    broken = temporary / 'broken_sized.jh'
    importer = temporary / 'sized-list-broken-import.jh'
    importer.write_text('#![dependent_core]\nimport broken_sized\n' + ANCHOR)
    broken.write_text(module)
    command('check', importer, *flags, env=env)
    command('emit-obj', importer, *flags, '-o', str(temporary / 'sized-import-control.o'), env=env)
    for old, new in (
        ('exact: refl(0)', 'exact: refl(1)'),
        ('nat.eq_add(list.length(data), n, 1, exact)', 'nat.eq_add(list.length(data), n, 2, exact)'),
        ('fn(i, p, acc) { cons(i, x, acc) }', 'fn(i, p, acc) { acc }'),
        ('list.map_borrowed_length(data, f)', 'refl(0)'),
    ):
        assert module.count(old) == 1, old
        broken.write_text(module.replace(old, new))
        rejected(importer, broken)
    list_module = (root / 'lib/dependent/list.jh').read_text()
    list_copy = temporary / 'broken_list.jh'
    broken.write_text(module.replace('import dependent.list', 'import broken_list').replace('list.', 'broken_list.'))
    list_copy.write_text(list_module)
    command('check', importer, *flags, env=env)
    command('emit-obj', importer, *flags, '-o', str(temporary / 'sized-list-import-control.o'), env=env)
    for old, new in (
        ('Eq(length(map(t, f)), length(t)) }, refl(0),', 'Eq(length(map(t, f)), length(t)) }, refl(1),'),
        ('refl(length(map(rest, f)) + 1)', 'ih'),
    ):
        assert list_module.count(old) == 1, old
        list_copy.write_text(list_module.replace(old, new))
        rejected(importer, list_copy)
    print('sized lists: indexed loop/owned proofs, both targets, native O0/O2 exact-length/order/allocation models, trap preservation and 15 intended rejections passed')
