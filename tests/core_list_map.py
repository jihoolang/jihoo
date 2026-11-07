"""Higher-order list maps and proof-bounded imported reads, called by core.py."""
import ctypes
import json
import os
import platform
import shlex
import struct

PREFIX = '#![dependent_core]\nimport dependent.list\n'
ANCHOR = '\nexport fn harness_anchor() -> i64 { 0 }\n'
INVALID = {
    'empty-head': 'fn bad() -> i64 { let xs = list.List.Nil; list.head(xs, decide_lt(0, 1)) }',
    'one-past-end': 'fn bad() -> i64 { let xs = list.List.Cons(8, list.List.Nil); list.nth(xs, 1, decide_lt(0, 1)) }',
    'other-owner': 'fn bad(xs: ref list.List, ys: ref list.List, i: u64, p: erased(Lt(i, list.length(xs)))) -> i64 { list.nth(ys, i, p) }',
    'wrong-index': 'fn bad(xs: ref list.List, i: u64, p: erased(Lt(i, list.length(xs)))) -> i64 { list.nth(xs, i + 1, p) }',
    'map-false-length': 'fn id(x: i64) -> i64 { x }\nfn bad(xs: ref list.List) -> Eq(list.into_length(list.map(xs, id)), list.length(xs) + 1) { list.map_length(xs, id) }',
    'wrong-function': 'fn id(x: u64) -> u64 { x }\nfn bad(xs: ref list.List) -> list.List { list.map(xs, id) }',
}
EXTRA = '''
fn record(n: u64, x: i64) -> i64 {
    let b = alloc(n, x)
    if_lt(0, n, fn(p) { index(b, 0, p) + 10 }, -1)
}
fn digits(xs: ref list.List) -> i64 {
    induct(fn(t) { i64 }, 0, fn(x, rest, ih) { x + 100 * ih }, xs)
}
export fn traced(cap: u64) -> i64 {
    let xs = list.List.Cons(1, list.List.Cons(2, list.List.Cons(3, list.List.Nil)))
    let ys = list.map(xs, fn(x: i64) -> i64 { record(cap, x) })
    let original = digits(xs)
    original + digits(ys)
}
fn ghost_on(xs: ref list.List) -> i64 {
    let p = list.map_length(xs, fn(x: i64) -> i64 { record(3, x) })
    7
}
export fn ghost(n: u64, x: i64) -> i64 {
    let xs = list.repeat(n, x)
    ghost_on(xs)
}
export fn mapped_index(i: u64) -> i64 {
    let xs = list.List.Cons(10, list.List.Cons(20, list.List.Cons(30, list.List.Nil)))
    let ys = list.map(xs, increment)
    let size = list.size(ys)
    if_lt(i, witness(size), fn(p) {
        list.nth(ys, i, transport(fn(k) { Lt(i, k) }, proof(size), p))
    }, -1)
}
export fn first(n: u64, x: i64) -> i64 {
    let xs = list.repeat(n, x)
    let size = list.size(xs)
    if_lt(0, witness(size), fn(p) {
        list.head(xs, transport(fn(k) { Lt(0, k) }, proof(size), p))
    }, -1)
}
export fn captured(n: u64, by: i64) -> i64 {
    let xs = list.repeat(n, 2)
    let ys = list.map(xs, fn(x: i64) -> i64 { x + by })
    list.sum(ys)
}
'''
RECORDER = r'''
#include <stddef.h>
#include <stdlib.h>
void *__real_malloc(size_t);
void __real_free(void *);
long allocations, frees, calls;
long long trace[64];
static void *live[256];
static size_t sizes[256];
void *__wrap_malloc(size_t n) {
    void *p = __real_malloc(n);
    allocations++;
    for (size_t i = 0; i < 256; i++) if (!live[i]) {
        live[i] = p; sizes[i] = n; return p;
    }
    abort();
}
void __wrap_free(void *p) {
    for (size_t i = 0; i < 256; i++) if (live[i] == p) {
        // Only record() allocates a three-element i64 buffer (32 bytes including its extra slot).
        // List Nil/Cons nodes are 8/24 bytes; read before freeing.
        if (sizes[i] == 32) {
            if (calls < 64) trace[calls] = ((long long *)p)[0];
            calls++;
        }
        live[i] = NULL; frees++; __real_free(p); return;
    }
    abort();
}
'''


def validate_list_map(compiler, root, temporary, environment, run):
    def command(action, path, *args, success=True, env=environment):
        return run([compiler, action, str(path), *args], success=success, env=env)

    example = root / 'examples/core_list_map.jh'
    source = temporary / 'list-map-library.jh'
    source.write_text(example.read_text() + EXTRA)
    command('check', source, '--lib', env={**environment, 'JIHOO_LLVM': '/unavailable', 'JIHOO_CC': '/unavailable'})
    mir = command('emit-mir', source, '--lib').stdout
    module = (root / 'lib/dependent/list.jh').read_text()
    flat = temporary / 'list-map-flat.jh'
    flat.write_text(module + source.read_text().replace('#![dependent_core]', '').replace('import dependent.list', '').replace('list.', ''))
    assert command('emit-mir', flat, '--lib').stdout == mir
    formatted = temporary / 'list-map-formatted.jh'
    formatted.write_text(command('fmt', source).stdout)
    assert command('fmt', formatted).stdout == formatted.read_text()
    assert command('emit-mir', formatted, '--lib').stdout == mir
    counter = temporary / 'list-map-counter.c'
    counter.write_text(RECORDER)
    host = 'aarch64' if platform.machine() in ('aarch64', 'arm64') else 'x86_64'
    for target, machine in (('x86_64', 62), ('aarch64', 183)):
        for level in ('-O0', '-O2'):
            obj = temporary / f'list-map-{target}{level}.o'
            command('emit-obj', source, '--lib', '--target', target, level, '-o', str(obj))
            assert struct.unpack_from('<H', obj.read_bytes(), 18)[0] == machine
            if target != host:
                continue
            shared = temporary / f'list-map{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC', 'clang')), '-shared', '-fPIC', str(obj), str(counter), '-o', str(shared), '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
            native = ctypes.CDLL(str(shared))
            allocations = ctypes.c_long.in_dll(native, 'allocations')
            frees = ctypes.c_long.in_dll(native, 'frees')
            calls = ctypes.c_long.in_dll(native, 'calls')
            trace = (ctypes.c_int64 * 64).in_dll(native, 'trace')
            for name, args in (
                ('lookup', [ctypes.c_uint64, ctypes.c_int64]),
                ('at', [ctypes.c_uint64, ctypes.c_uint64, ctypes.c_int64]),
                ('traced', [ctypes.c_uint64]),
                ('ghost', [ctypes.c_uint64, ctypes.c_int64]),
                ('mapped_index', [ctypes.c_uint64]),
                ('first', [ctypes.c_uint64, ctypes.c_int64]),
                ('captured', [ctypes.c_uint64, ctypes.c_int64]),
            ):
                getattr(native, name).argtypes = args
                getattr(native, name).restype = ctypes.c_int64
            assert native.traced(3) == 30201 + 131211
            assert calls.value == 3 and list(trace[:3]) == [3, 2, 1], (calls.value, list(trace[:10]), allocations.value, frees.value, level)
            assert allocations.value == frees.value == 11
            for i in (0, 1, 2, 3, (1 << 64) - 1):
                assert native.mapped_index(i) == ([11, 21, 31][i] if i < 3 else -1)
                assert allocations.value == frees.value
            for n in range(10):
                for x in (-7, 0, 12):
                    before = allocations.value
                    assert native.lookup(n, x) == (10 * (n + 1) if n < 5 else -1)
                    assert allocations.value - before == (2 * (n + 1) if n < 5 else n + 1)
                    assert allocations.value == frees.value
                    assert native.first(n, x) == (x if n else -1)
                    assert native.captured(n, x) == n * (2 + x)
                    assert allocations.value == frees.value
                    for i in (*range(11), (1 << 64) - 1):
                        before = allocations.value
                        assert native.at(n, i, x) == (x + 1 if i < n else -1)
                        assert allocations.value - before == 2 * (n + 1)
                        assert allocations.value == frees.value
                before, called = allocations.value, calls.value
                # The callback would allocate and overflow if invoked on this argument.
                assert native.ghost(n, (1 << 63) - 1) == 7
                assert calls.value == called
                assert allocations.value - before == n + 1
                assert allocations.value == frees.value
    for level in ('-O0', '-O2'):
        assert command('run', example, level, success=False).returncode == 40
        # Map values remain evaluated for traps even when only their length is read.
        for n, status in ((0, 10), (1, 132), (5, 255)):
            trap = temporary / f'list-map-trap-{n}.jh'
            trap.write_text(example.read_text().replace('lookup(3, 7)', f'lookup({n}, 9223372036854775807)'))
            assert command('run', trap, level, success=False).returncode == status
        underflow = temporary / 'list-map-underflow.jh'
        underflow.write_text(PREFIX + 'fn dec(x: i64) -> i64 { x - 1 }\nfn main() -> i64 { let xs = list.repeat(1, -9223372036854775808); let ys = list.map(xs, dec); 0 }')
        assert command('run', underflow, level, success=False).returncode == 132
    flags = ('--lib', '--release', '--no-verify', '--error-format=json')
    env = {**environment, 'JIHOO_NO_ELAB': '1'}
    control = temporary / 'list-map-control.jh'
    control.write_text(PREFIX + 'fn good(xs: ref list.List, i: u64, p: erased(Lt(i, list.length(xs)))) -> i64 { list.nth(xs, i, p) }' + ANCHOR)
    command('check', control, *flags, env=env)
    command('emit-obj', control, *flags, '-o', str(temporary / 'list-map-control.o'), env=env)

    def rejected(path, blame, expected="core: type mismatch"):
        obj = temporary / 'list-map-rejected.o'
        for action, options in (('check', ()), ('emit-obj', ('-o', str(obj)))):
            result = command(action, path, *flags, *options, success=False, env=env)
            errors = [d for d in json.loads(result.stderr)['diagnostics'] if d['severity'] == 'error']
            assert result.returncode == 1 and len(errors) == 1, result.stderr
            assert errors[0]['kind'] == 'source' and errors[0]['message'] == expected, result.stderr
            assert errors[0]['span']['file'] == str(blame), result.stderr
        assert not obj.exists()

    for name, body in INVALID.items():
        bad = temporary / f'list-map-{name}.jh'
        bad.write_text(PREFIX + body + ANCHOR)
        rejected(bad, bad)
    escaped = temporary / 'list-map-escaped-proof.jh'
    escaped.write_text(PREFIX + 'fn inc(x: i64) -> i64 { x + 1 }\nfn bad() -> i64 { let xs = list.repeat(3, 7); let p = list.map_length(xs, inc); 0 }' + ANCHOR)
    rejected(escaped, escaped, 'core: a borrow cannot outlive its lend')
    broken = temporary / 'broken_map.jh'
    importer = temporary / 'list-map-broken-import.jh'
    importer.write_text('#![dependent_core]\nimport broken_map\n' + ANCHOR)
    broken.write_text(module)
    command('check', importer, *flags, env=env)
    command('emit-obj', importer, *flags, '-o', str(temporary / 'list-map-import-control.o'), env=env)
    for old, new in (
        ('Eq(into_length(map(t, f)), length(t)) }, refl(0),', 'Eq(into_length(map(t, f)), length(t)) }, refl(1),'),
        ('refl(into_length(map(rest, f)) + 1)', 'ih'),
        ('lt_cancel(sub(i, 1, e), length(rest), 1, p)', 'p'),
    ):
        assert module.count(old) == 1, old
        broken.write_text(module.replace(old, new))
        rejected(importer, broken)
    print('list map: imported structural proof/bounded reads, both targets, native O0/O2 order/effects/allocation models, traps and 9 exact proof rejections and a proof-borrow escape rejection passed')
