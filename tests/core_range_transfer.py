"""Proof-bounded range transfer: reuse, overlap, erasure and ownership."""
import ctypes
import json
import os
import platform
import shlex
import struct
from core_buffer import COUNTER

PREFIX = '#![dependent_core]\nimport dependent.range\n'
HELPERS = '''
fn digits(xs: ref buffer(6)) -> i64 {
    fold(6, 0, fn(i, p, acc) { acc * 10 + index(xs, i, p) })
}
fn buffer_of(values: [i64; 6]) -> buffer(6) {
    fold(6, alloc(6, 0), fn(i, p, acc) { store(acc, i, index(values, i, p), p) })
}
'''


def consumer(name, copy):
    setup = ('let source = buffer_of([1, 2, 3, 4, 5, 6]); '
             'let target = buffer_of([7, 8, 9, 0, 1, 2]);' if copy else
             'let target = buffer_of([1, 2, 3, 4, 5, 6]);')
    operation = ('range.copy_into(6, source, 6, target, from, to, count, fp, tp)' if copy else
                 'range.move_within(6, target, from, to, count, fp, tp)')
    result = 'let snapshot = digits(source); snapshot * 1000000 + digits(result)' if copy else 'digits(result)'
    return f'''
export fn {name}(from: u64, to: u64, count: u64) -> i64 {{
    {setup}
    if_lt(from, 7, fn(fs) {{ if_lt(to, 7, fn(ts) {{
        if_lt(count, sub(6, from, fs) + 1, fn(fits) {{
            if_lt(count, sub(6, to, ts) + 1, fn(room) {{
                let fp = lt_add(count, sub(6, from, fs) + 1, from, fits)
                let tp = lt_add(count, sub(6, to, ts) + 1, to, room)
                let result = {operation}
                {result}
            }}, -1)
        }}, -1)
    }}, -1) }}, -1)
}}
'''

INVALID = {
    'aliased-copy': ('fn bad(xs: buffer(3)) -> buffer(3) { range.copy_into(3, xs, 3, xs, 0, 0, 1, decide_lt(1, 4), decide_lt(1, 4)) }', 'an owned value is used more than once'),
    'bad-source': ('fn bad(xs: ref buffer(3), ys: buffer(4)) -> buffer(4) { range.copy_into(3, xs, 4, ys, 2, 0, 2, decide_lt(4, 4), decide_lt(2, 5)) }', 'decide-lt needs a true closed inequality'),
    'bad-destination': ('fn bad(xs: ref buffer(3), ys: buffer(4)) -> buffer(4) { range.copy_into(3, xs, 4, ys, 0, 3, 2, decide_lt(2, 4), decide_lt(5, 5)) }', 'decide-lt needs a true closed inequality'),
    'wrong-owner-length': ('fn bad(xs: buffer(3)) -> buffer(4) { range.move_within(4, xs, 0, 0, 0, decide_lt(0, 5), decide_lt(0, 5)) }', 'type mismatch'),
    'wrong-result-length': ('fn bad(xs: buffer(3)) -> buffer(2) { range.move_within(3, xs, 0, 0, 0, decide_lt(0, 4), decide_lt(0, 4)) }', 'type mismatch'),
    'false-subrange': ('fn bad() -> Lt(5, 5) { range.subrange_fits(4, 1, 3, 2, 2, decide_lt(4, 5), decide_lt(4, 4)) }', 'decide-lt needs a true closed inequality'),
    'borrow-as-owner': ('fn bad(xs: ref buffer(3)) -> buffer(3) { range.move_within(3, xs, 0, 1, 2, decide_lt(2, 4), decide_lt(3, 4)) }', 'type mismatch'),
    'reuse-owner': ('fn bad(xs: buffer(3)) -> i64 { let ys = range.move_within(3, xs, 0, 0, 0, decide_lt(0, 4), decide_lt(0, 4)); free(xs, free(ys, 0)) }', 'an owned value is used more than once'),
}

# These are true propositions with the wrong endpoints, so rejection must
# happen at API argument matching rather than inside decide_lt itself.
for name, original, replacement in (
    ('bad-source', 'decide_lt(4, 4)', 'decide_lt(3, 4)'),
    ('bad-destination', 'decide_lt(5, 5)', 'decide_lt(4, 5)'),
    ('false-subrange', 'decide_lt(4, 4)', 'decide_lt(3, 4)'),
):
    INVALID['wrong-evidence-' + name] = (INVALID[name][0].replace(original, replacement), 'type mismatch')


def exact_error(result, path, expected):
    report = json.loads(result.stderr)
    assert report['error_count'] == 1 and not report['truncated']
    assert len(report['diagnostics']) == 1
    diagnostic = report['diagnostics'][0]
    assert diagnostic['severity'] == 'error' and diagnostic['kind'] == 'source'
    assert diagnostic['message'] == 'core: ' + expected, result.stderr
    assert diagnostic['span']['file'] == str(path), result.stderr


def validate_range_transfer(compiler, root, temporary, environment, run):
    def command(action, path, *args, success=True, env=None):
        return run([compiler, action, str(path), *args], success=success,
                   env=environment if env is None else env)
    source = temporary / 'range-transfer.jh'
    source.write_text(PREFIX + HELPERS + consumer('moved', False) + consumer('copied', True) + """
export fn signed(x: i64) -> i64 {
    let target = alloc(2, x)
    let moved = range.move_within(2, target, 0, 1, 1, decide_lt(1, 3), decide_lt(2, 3))
    index(moved, 1, decide_lt(1, 2))
}
export fn empty() -> i64 {
    let source = alloc(0, 0)
    let target = alloc(0, 0)
    let copied = range.copy_into(0, source, 0, target, 0, 0, 0, decide_lt(0, 1), decide_lt(0, 1))
    let moved = range.move_within(0, copied, 0, 0, 0, decide_lt(0, 1), decide_lt(0, 1))
    free(moved, 0)
}
""")
    command('check', source, '--lib')
    ghost = temporary / 'range-transfer-ghost.jh'
    ghost.write_text(PREFIX + '''export fn ghost(n: u64) -> u64 {
        let p = range.subrange_fits(n + 1, n, 1, 0, 1,
            lt_add(0, 1, n + 1, decide_lt(0, 1)), decide_lt(1, 2))
        n
    }''')
    plain = temporary / 'range-transfer-plain.jh'
    plain.write_text('#![dependent_core]\nexport fn ghost(n: u64) -> u64 { n }')
    assert command('emit-mir', ghost, '--lib').stdout == command('emit-mir', plain, '--lib').stdout
    counter = temporary / 'transfer-counter.c'; counter.write_text(COUNTER)
    host = 'aarch64' if platform.machine() in ('aarch64', 'arm64') else 'x86_64'
    for target, machine in (('x86_64', 62), ('aarch64', 183)):
        for level in ('-O0', '-O2'):
            obj = temporary / f'transfer-{target}{level}.o'
            command('emit-obj', source, '--lib', '--target', target, level, '-o', str(obj))
            assert struct.unpack_from('<H', obj.read_bytes(), 18)[0] == machine
            if target != host:
                continue
            shared = temporary / f'transfer{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC', 'clang')), '-shared', '-fPIC', str(obj), str(counter),
                 '-o', str(shared), '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
            native = ctypes.CDLL(str(shared))
            allocations = ctypes.c_long.in_dll(native, 'allocations')
            frees = ctypes.c_long.in_dll(native, 'frees')
            for name in ('moved', 'copied'):
                fn = getattr(native, name); fn.argtypes = [ctypes.c_uint64] * 3; fn.restype = ctypes.c_int64
                for start in range(8):
                    for to in range(8):
                        for count in range(8):
                            valid = start <= 6 and to <= 6 and count <= 6 - start and count <= 6 - to
                            values = [1, 2, 3, 4, 5, 6] if name == 'moved' else [7, 8, 9, 0, 1, 2]
                            if valid:
                                values[to:to+count] = [1, 2, 3, 4, 5, 6][start:start+count]
                            expected = (int(''.join(map(str, values))) + (123456000000 if name == 'copied' else 0)) if valid else -1
                            allocations.value = frees.value = 0
                            assert fn(start, to, count) == expected, (name, start, to, count, expected)
                            assert allocations.value == frees.value
                            if level == '-O0':
                                assert allocations.value == (2 if name == 'copied' else 1)
            native.signed.argtypes = [ctypes.c_int64]; native.signed.restype = ctypes.c_int64
            for value in (-(1 << 63), -1, 0, 1, (1 << 63) - 1):
                allocations.value = frees.value = 0
                assert native.signed(value) == value
                assert allocations.value == frees.value
                if level == '-O0': assert allocations.value == 1
            allocations.value = frees.value = 0
            assert native.empty() == 0
            assert allocations.value == frees.value
            if level == '-O0': assert allocations.value == 2
            assert command('run', root / 'examples/core_range_transfer.jh' , level, success=False).returncode == 28
    anchor = '\nexport fn anchor() -> i64 { 0 }\n'
    positive = temporary / 'transfer-positive.jh'; positive.write_text(PREFIX + anchor)
    command('emit-obj', positive, '--lib', '-o', str(temporary / 'transfer-positive.o'))
    for name, (body, expected) in INVALID.items():
        path = temporary / f'transfer-invalid-{name}.jh'; path.write_text(PREFIX + body + anchor)
        for action in ('check', 'emit-obj'):
            obj = temporary / f'invalid-{name}.o'; obj.unlink(missing_ok=True)
            options = ['-o', str(obj)] if action == 'emit-obj' else []
            result = command(action, path, '--lib', '--error-format=json', '--release', '--no-verify', *options,
                             success=False, env={**environment, 'JIHOO_NO_ELAB': '1'})
            exact_error(result, path, expected)
            assert not obj.exists()
    original = (root / 'lib/dependent/range.jh').read_text()
    for name, old, new in (
        ('reverse-bound', 'nat.mirror_lt(i, count, p)', 'p'),
        ('composition', 'lt_add(start + length, count + 1, offset, inner)', 'inner'),
        ('source-offset', 'index(source, from + i, offset_lt(n, from, count, i, source_fits, p))',
         'index(source, from + i + 1, offset_lt(n, from, count, i, source_fits, p))'),
        ('move-write', 'store(target, to + i, value, offset_lt(n, to, count, i, destination_fits, inside))',
         'store(target, to + i + 1, value, offset_lt(n, to, count, i, destination_fits, inside))'),
    ):
        assert old in original
        module = 'transfer_broken_' + name.replace('-', '_')
        library = temporary / (module + '.jh')
        importer = temporary / (module + '_consumer.jh')
        importer.write_text('#![dependent_core]\nimport ' + module + '\n' + anchor)
        library.write_text(original)
        command('check', importer, '--lib')
        command('emit-obj', importer, '--lib', '-o', str(temporary / (module + '-positive.o')))
        library.write_text(original.replace(old, new))
        obj = temporary / (module + '.o')
        for action in ('check', 'emit-obj'):
            obj.unlink(missing_ok=True)
            options = ['-o', str(obj)] if action == 'emit-obj' else []
            result = command(action, importer, '--lib', '--error-format=json', '--release', '--no-verify',
                             *options, success=False, env={**environment, 'JIHOO_NO_ELAB': '1'})
            exact_error(result, library, 'type mismatch')
            assert not obj.exists()
    print('range transfer: both targets, overlap/reference models, storage reuse, erasure and exact rejections passed')
