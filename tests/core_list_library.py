"""Reusable list operations and imported structural proofs, called by core.py."""
import ctypes
import json
import os
import platform
import shlex
import struct

from core_buffer import COUNTER

PREFIX = '#![dependent_core]\nimport dependent.list\n'
ANCHOR = '\nexport fn harness_anchor() -> i64 { 0 }\n'
INVALID = {
    'false-clone-length': 'fn bad(xs: ref list.List) -> Eq(list.into_length(list.clone(xs)), list.length(xs) + 1) { list.clone_length(xs) }',
    'wrong-append-length': 'fn bad(xs: ref list.List, ys: ref list.List) -> Eq(list.into_length(list.append(xs, ys)), list.length(xs)) { list.append_length(xs, ys) }',
    'swapped-owner': 'fn bad(xs: ref list.List, ys: ref list.List) -> Eq(list.into_length(list.clone(xs)), list.length(ys)) { list.clone_length(xs) }',
    'false-base': 'fn bad() -> Eq(list.into_length(list.List.Nil), 1) { refl(0) }',
    'wrong-size': 'fn bad(xs: ref list.List) -> Eq(witness(list.size(xs)), list.length(xs) + 1) { proof(list.size(xs)) }',
}
EXTRA = '''
fn digits(xs: ref list.List) -> i64 {
    induct(fn(t) { i64 }, 0, fn(x, rest, ih) { x + 10 * ih }, xs)
}
fn ordered_with(xs: ref list.List, ys: list.List) -> i64 {
    let zs = list.append(xs, ys)
    digits(zs)
}
export fn ordered(x: i64, y: i64) -> i64 {
    let xs = list.List.Cons(x, list.List.Cons(2, list.List.Nil))
    ordered_with(xs, list.List.Cons(y, list.List.Cons(4, list.List.Nil)))
}
export fn cloned(n: u64, x: i64) -> i64 {
    let xs = list.repeat(n, x)
    let ys = list.clone(xs)
    let a = list.sum(xs)
    a + list.sum(ys)
}
export fn first(n: u64, x: i64) -> i64 {
    let xs = list.repeat(n, x)
    list.head_or(xs, -7)
}
export fn measured(n: u64) -> u64 {
    let xs = list.repeat(n, 1)
    witness(list.size(xs))
}
'''


def validate_list_library(compiler, root, temporary, environment, run):
    def command(action, path, *args, success=True, env=environment):
        return run([compiler, action, str(path), *args], success=success, env=env)

    example = root / 'examples/core_list_library.jh'
    source = temporary / 'list-library.jh'
    source.write_text(example.read_text() + EXTRA)
    command('check', source, '--lib', env={**environment, 'JIHOO_LLVM': '/unavailable', 'JIHOO_CC': '/unavailable'})
    mir = command('emit-mir', source, '--lib').stdout
    # Flatten only the module boundary, retaining independently checked terms.
    # This is an import/erasure comparison, not a separate arithmetic oracle.
    module = (root / 'lib/dependent/list.jh').read_text()
    flat = temporary / 'list-flat.jh'
    flat.write_text(module + source.read_text().replace('#![dependent_core]', '').replace('import dependent.list', '').replace('list.', ''))
    assert command('emit-mir', flat, '--lib').stdout == mir
    formatted = temporary / 'list-library-formatted.jh'
    formatted.write_text(command('fmt', source).stdout)
    assert command('fmt', formatted).stdout == formatted.read_text()
    assert command('emit-mir', formatted, '--lib').stdout == mir
    counter = temporary / 'list-library-counter.c'
    counter.write_text(COUNTER)
    host = 'aarch64' if platform.machine() in ('aarch64', 'arm64') else 'x86_64'
    for target, machine in (('x86_64', 62), ('aarch64', 183)):
        for level in ('-O0', '-O2'):
            obj = temporary / f'list-library-{target}{level}.o'
            command('emit-obj', source, '--lib', '--target', target, level, '-o', str(obj))
            assert struct.unpack_from('<H', obj.read_bytes(), 18)[0] == machine
            if target != host:
                continue
            shared = temporary / f'list-library{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC', 'clang')), '-shared', '-fPIC', str(obj), str(counter), '-o', str(shared), '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
            native = ctypes.CDLL(str(shared))
            allocations = ctypes.c_long.in_dll(native, 'allocations')
            frees = ctypes.c_long.in_dll(native, 'frees')
            for name, args, result in (
                ('joined', [ctypes.c_uint64, ctypes.c_uint64, ctypes.c_int64], ctypes.c_int64),
                ('lookup', [ctypes.c_uint64, ctypes.c_uint64], ctypes.c_int64),
                ('cloned', [ctypes.c_uint64, ctypes.c_int64], ctypes.c_int64),
                ('first', [ctypes.c_uint64, ctypes.c_int64], ctypes.c_int64),
                ('measured', [ctypes.c_uint64], ctypes.c_uint64),
                ('ordered', [ctypes.c_int64, ctypes.c_int64], ctypes.c_int64),
            ):
                getattr(native, name).argtypes = args
                getattr(native, name).restype = result
            for x in (0, 1, 7):
                for y in (0, 3, 9):
                    assert native.ordered(x, y) == x + 20 + 100 * y + 4000
                    assert frees.value == allocations.value
            for n in range(11):
                for m in range(11):
                    before = allocations.value
                    assert native.lookup(n, m) == (10 * (n + m + 1) if n + m < 9 else -1)
                    # The proof is erased: only input lists and the executed append allocate.
                    assert allocations.value - before == (2 * (n + m) + 3 if n + m < 9 else n + m + 2), (n, m, allocations.value - before, level)
                    assert frees.value == allocations.value
                    for x in (-5, 0, 7):
                        assert native.joined(n, m, x) == 2 * (n * x + m)
                        assert frees.value == allocations.value
                for x in (-9, 0, 13):
                    before = allocations.value
                    assert native.cloned(n, x) == 2 * n * x
                    assert allocations.value - before == 2 * (n + 1)
                    assert frees.value == allocations.value
                    assert native.first(n, x) == (x if n else -7)
                    assert frees.value == allocations.value
                assert native.measured(n) == n
                assert frees.value == allocations.value
    for level in ('-O0', '-O2'):
        assert command('run', example, level, success=False).returncode == 60
    trap = temporary / 'list-library-overflow.jh'
    trap.write_text(PREFIX + 'fn main() -> i64 { let xs = list.repeat(2, 9223372036854775807); list.sum(xs) }')
    for level in ('-O0', '-O2'):
        assert command('run', trap, level, success=False).returncode == 132
    flags = ('--lib', '--release', '--no-verify', '--error-format=json')
    env = {**environment, 'JIHOO_NO_ELAB': '1'}
    control = temporary / 'list-library-control.jh'
    control.write_text(PREFIX + 'fn valid(xs: ref list.List) -> Eq(list.into_length(list.clone(xs)), list.length(xs)) { list.clone_length(xs) }' + ANCHOR)
    command('check', control, *flags, env=env)
    command('emit-obj', control, *flags, '-o', str(temporary / 'list-library-control.o'), env=env)

    def rejected(path, blame, expected="core: type mismatch"):
        obj = temporary / 'list-library-rejected.o'
        for action, options in (('check', ()), ('emit-obj', ('-o', str(obj)))):
            result = command(action, path, *flags, *options, success=False, env=env)
            errors = [d for d in json.loads(result.stderr)['diagnostics'] if d['severity'] == 'error']
            assert result.returncode == 1 and len(errors) == 1, result.stderr
            assert errors[0]['kind'] == 'source' and errors[0]['message'] == expected, result.stderr
            assert errors[0]['span']['file'] == str(blame), result.stderr
        assert not obj.exists()

    for name, body in INVALID.items():
        bad = temporary / f'list-library-{name}.jh'
        bad.write_text(PREFIX + body + ANCHOR)
        rejected(bad, bad)
    used_twice = temporary / 'list-library-double-use.jh'
    used_twice.write_text(PREFIX + 'fn bad(xs: list.List) -> u64 { list.into_length(xs) + list.into_length(xs) }' + ANCHOR)
    rejected(used_twice, used_twice, 'core: an owned value is used more than once')
    # Imported lemmas must be checked even if no caller reaches their bodies.
    broken = temporary / 'broken_list.jh'
    importer = temporary / 'list-library-broken-import.jh'
    importer.write_text('#![dependent_core]\nimport broken_list\n' + ANCHOR)
    broken.write_text(module)
    command('check', importer, *flags, env=env)
    command('emit-obj', importer, *flags, '-o', str(temporary / 'list-import-control.o'), env=env)
    for old, new in (
        ('Eq(into_length(clone(t)), length(t)) }, refl(0),', 'Eq(into_length(clone(t)), length(t)) }, refl(1),'),
        ('refl(into_length(clone(rest)) + 1)', 'ih'),
        ('        clone_length(ys),', '        refl(0),'),
        ('refl(into_length(append(rest, ys)) + 1)', 'ih'),
    ):
        assert module.count(old) == 1, old
        broken.write_text(module.replace(old, new))
        rejected(importer, broken)
    print('list library: imported induction, MIR import erasure, both object targets, native O0/O2 model/allocation checks, overflow and 9 intended proof rejections and an ownership rejection passed')
