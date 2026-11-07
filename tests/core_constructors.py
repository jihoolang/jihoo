"""Explicit dependent constructor indices: source elaboration, erasure and rejection."""
import ctypes
import json
import os
import platform
import shlex
import struct

from core_buffer import COUNTER

PREFIX = '''#![dependent_core]
enum Slot(n: u64) { Empty; Full(refine(fn(j) { Lt(j, n) })) }
enum Pair(n: u64, m: u64) { Empty; Values(buffer(n), buffer(m)) }
enum Nested(n: u64) { Wrap(Slot(n)) }
enum Owned(n: u64) { Empty; Data(buffer(n)) }
fn read(n: erased(u64), s: Slot(n)) -> u64 {
    match s { Empty => 7; Full(j) => witness(j) }
}
'''
PROGRAM = PREFIX + '''
export fn nested() -> u64 {
    let s = Nested(3).Wrap(Slot.Empty)
    match s { Wrap(v) => read(3, v) }
}
export fn computed() -> u64 { let s: Slot(3) = Slot(1 + 2).Empty; read(3, s) }
export fn empty(n: u64) -> u64 {
    let s = Slot(n).Empty
    read(n, s)
}
export fn full(i: u64) -> u64 {
    if_lt(i, 4, fn(p) {
        let s = Slot(4).Full(pack(i, p))
        read(4, s)
    }, 9)
}
export fn direct() -> i64 {
    match Slot(3).Empty { Empty => 5; Full(j) => 0 }
}
export fn pair(x: i64) -> i64 {
    let p = Pair(1, 2).Values(alloc(1, x), alloc(2, 3))
    match p { Empty => 0; Values(a, b) => load(a, 0, decide_lt(0, 1), fn(v, a) { load(b, 0, decide_lt(0, 2), fn(w, b) { free(a, free(b, v + w)) }) }) }
}
export fn owned(n: u64) -> i64 {
    let p = Owned(n).Data(alloc(n, 7))
    match p { Empty => -1; Data(b) => free(b, 9) }
}
fn ghost(n: erased(u64)) -> u64 { let s = Slot(n).Empty; read(n, s) }
export fn erased_index() -> u64 { ghost(18446744073709551615 + 1) }
export fn shadow(n: u64) -> u64 { let n = n + 1; let s = Slot(n).Empty; read(n, s) }
'''
REFERENCE = PROGRAM.replace('let s = Nested(3).Wrap', 'let s: Nested(3) = Nested.Wrap').replace('Slot(1 + 2).Empty', 'Slot.Empty')
REFERENCE = REFERENCE.replace('let s = Slot(n).Empty', 'let s: Slot(n) = Slot.Empty')
REFERENCE = REFERENCE.replace('let s = Slot(4).Full', 'let s: Slot(4) = Slot.Full')
REFERENCE = REFERENCE.replace('match Slot(3).Empty', 'let s: Slot(3) = Slot.Empty; match s')
REFERENCE = REFERENCE.replace('let p = Pair(1, 2).Values', 'let p: Pair(1, 2) = Pair.Values')
REFERENCE = REFERENCE.replace('let p = Owned(n).Data', 'let p: Owned(n) = Owned.Data')

INVALID = {
    'missing-index': 'fn bad() -> u64 { let s = Slot().Empty; 0 }',
    'extra-index': 'fn bad() -> u64 { let s = Slot(1, 2).Empty; 0 }',
    'wrong-index-type': 'fn bad(x: i64) -> u64 { let s = Slot(x).Empty; 0 }',
    'false-field': 'fn bad() -> u64 { let s = Slot(1).Full(pack(2, decide_lt(2, 1))); 0 }',
    'wrong-field-index': 'fn bad() -> u64 { let s = Slot(1).Full(pack(2, decide_lt(2, 3))); 0 }',
    'context-mismatch': 'fn bad() -> Slot(4) { Slot(3).Empty }',
    'discarded-context-mismatch': 'fn bad() -> u64 { let s: Slot(4) = Slot(3).Empty; 0 }',
    'missing-field': 'fn bad() -> u64 { let s = Slot(1).Full; 0 }',
    'extra-field': 'fn bad() -> u64 { let s = Slot(1).Empty(0); 0 }',
    'unknown-variant': 'fn bad() -> u64 { let s = Slot(1).Missing; 0 }',
    'unknown-family': 'fn bad() -> u64 { let s = Missing(1).Empty; 0 }',
    'partial-indices': 'fn bad() -> u64 { let s = Pair(1).Empty; 0 }',
    'dependent-buffer-length': 'fn bad() -> u64 { let s = Pair(1, 2).Values(alloc(1, 1), alloc(1, 2)); 0 }',
    'owner-length': 'fn bad() -> u64 { let s = Owned(2).Data(alloc(1, 7)); 0 }',
    'erased-runtime-field': 'fn bad(n: erased(u64)) -> u64 { let s = Slot(n + 1).Full(pack(n, lt_add(0, 1, n, decide_lt(0, 1)))); 0 }',
    # This malformed proof disappears if the index is normalized before checking.
    'invalid-index-proof': 'fn bad() -> u64 { let s = Slot(sub(2, 1, decide_lt(0, 1))).Empty; 0 }',
    'invalid-index-proof-with-context': 'fn bad() -> Slot(1) { Slot(sub(2, 1, decide_lt(0, 1))).Empty }',
    'duplicate-owner': 'fn bad() -> i64 { let b = alloc(1, 7); let s = Owned(1).Data(b); free(b, 0) }',
}


ANCHOR = '\nexport fn harness_anchor() -> i64 { 0 }\n'
EXPECTED_DIAGNOSTICS = {
    'missing-index': 'wrong number of family indices',
    'extra-index': 'wrong number of family indices',
    'wrong-index-type': 'type mismatch',
    'false-field': 'decide-lt needs a true closed inequality',
    'wrong-field-index': 'type mismatch',
    'context-mismatch': 'type mismatch',
    'discarded-context-mismatch': 'type mismatch',
    'missing-field': 'a constructor requires all of its fields',
    'extra-field': 'too many constructor arguments',
    'unknown-variant': 'unsupported expression in dependent_core',
    'unknown-family': 'unsupported expression in dependent_core',
    'partial-indices': 'wrong number of family indices',
    'dependent-buffer-length': 'type mismatch',
    'owner-length': 'type mismatch',
    'erased-runtime-field': 'erased value used at runtime',
    'invalid-index-proof': 'type mismatch',
    'invalid-index-proof-with-context': 'type mismatch',
    'duplicate-owner': 'an owned value is used more than once',
}


def validate_constructors(compiler, root, temporary, environment, run):
    def command(action, path, *args, success=True, env=environment):
        return run([compiler, action, str(path), *args], success=success, env=env)
    source, reference = temporary / 'constructors.jh', temporary / 'constructors-reference.jh'
    source.write_text(PROGRAM); reference.write_text(REFERENCE)
    command('check', source, '--lib', env={**environment, 'JIHOO_LLVM': '/unavailable', 'JIHOO_CC': '/unavailable'})
    mir = command('emit-mir', source, '--lib').stdout
    assert mir == command('emit-mir', reference, '--lib').stdout
    formatted = temporary / 'constructors-formatted.jh'
    formatted.write_text(command('fmt', source).stdout)
    assert command('fmt', formatted).stdout == formatted.read_text()
    assert command('emit-mir', formatted, '--lib').stdout == mir
    counter = temporary / 'constructors-counter.c'; counter.write_text(COUNTER)
    host = 'aarch64' if platform.machine() in ('aarch64', 'arm64') else 'x86_64'
    for target, machine in (('x86_64', 62), ('aarch64', 183)):
        for level in ('-O0', '-O2'):
            obj = temporary / f'constructors-{target}{level}.o'
            command('emit-obj', source, '--lib', '--target', target, level, '-o', str(obj))
            assert struct.unpack_from('<H', obj.read_bytes(), 18)[0] == machine
            if target != host:
                continue
            library = temporary / f'constructors{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC', 'clang')), '-shared', '-fPIC', str(obj), str(counter),
                 '-Wl,--wrap=malloc', '-Wl,--wrap=free', '-o', str(library)])
            native = ctypes.CDLL(str(library))
            for name in ('empty', 'full', 'shadow'):
                fn = getattr(native, name); fn.argtypes, fn.restype = [ctypes.c_uint64], ctypes.c_uint64
            native.pair.argtypes, native.pair.restype = [ctypes.c_int64], ctypes.c_int64
            native.owned.argtypes, native.owned.restype = [ctypes.c_uint64], ctypes.c_int64
            native.erased_index.restype = ctypes.c_uint64
            assert native.direct() == 5 and native.erased_index() == 7
            assert native.nested() == 7 and native.computed() == 7
            for n in (0, 1, 3, 4, 16):
                assert native.empty(n) == 7 and native.shadow(n) == 7
                assert native.full(n) == (n if n < 4 else 9)
                assert native.owned(n) == 9
            for x in (-19, 0, 100):
                assert native.pair(x) == x + 3
            assert ctypes.c_long.in_dll(native, 'allocations').value == ctypes.c_long.in_dll(native, 'frees').value
    # The same harness must compile a valid, unused local function. Otherwise
    # a missing runtime export could masquerade as the intended rejection.
    flags = ('--lib', '--no-verify', '--release', '--error-format=json')
    no_elab = {**environment, 'JIHOO_NO_ELAB': '1'}
    control = temporary / 'constructors-negative-control.jh'
    control.write_text(PREFIX + 'fn valid() -> u64 { let s = Slot(1).Empty; 0 }' + ANCHOR)
    command('check', control, *flags, env=no_elab)
    control_obj = temporary / 'constructors-negative-control.o'
    command('emit-obj', control, *flags, '-o', str(control_obj), env=no_elab)
    assert control_obj.read_bytes().startswith(b'\x7fELF'), 'positive rejection-harness control did not emit an object'
    assert INVALID.keys() == EXPECTED_DIAGNOSTICS.keys()
    for name, body in INVALID.items():
        bad = temporary / f'constructors-{name}.jh'; bad.write_text(PREFIX + body + ANCHOR)
        obj = temporary / f'constructors-{name}.o'
        for action, options in (('check', ()), ('emit-obj', ('-o', str(obj)))):
            result = command(action, bad, *flags, *options, success=False, env=no_elab)
            document = json.loads(result.stderr)
            errors = [d for d in document['diagnostics'] if d['severity'] == 'error']
            assert result.returncode == 1 and len(errors) == 1, (name, action, result.stderr)
            assert errors[0]['kind'] == 'source', (name, action, result.stderr)
            assert errors[0]['message'] == 'core: ' + EXPECTED_DIAGNOSTICS[name], (name, action, result.stderr)
        assert not obj.exists(), name
    directory = temporary / 'constructor-modules'; directory.mkdir()
    module = """#![dependent_core]
pub enum Slot(n: u64) { Empty; Full(refine(fn(j) { Lt(j, n) })) }
enum Hidden(n: u64) { Empty }
pub struct Secret { value: i64 }
pub fn accept(n: erased(u64), s: Slot(n)) -> i64 { 7 }
"""
    (directory / 'a.jh').write_text(module); (directory / 'b.jh').write_text(module)
    imported = directory / 'main.jh'
    imports = '#![dependent_core]\nimport a\nimport b\nimport a as alias\n'
    imported.write_text(imports + 'fn main() -> i64 { let s = alias.Slot(3).Empty; a.accept(3, s) }')
    command('check', imported)
    for level in ('-O0', '-O2'):
        assert command('run', imported, level, success=False).returncode == 7
    for name, body in {
        'cross-module': 'fn bad() -> i64 { a.accept(1, b.Slot(1).Empty) }',
        'private-family': 'fn bad() -> i64 { let s = a.Hidden(1).Empty; 0 }',
        'private-field': 'fn bad() -> i64 { let s = a.Secret().Secret(1); 0 }',
        'wrong-module-qualifier': 'fn bad() -> i64 { let s = absent.Slot(1).Empty; 0 }',
    }.items():
        imported.write_text(imports + body + '\nfn main() -> i64 { 0 }')
        result = command('check', imported, '--error-format=json', success=False)
        assert result.returncode == 1 and json.loads(result.stderr) and 'core:' in result.stderr, (name, result.stderr)
    print(f'explicit dependent constructors: identical MIR, formatter, both targets, runtime/ownership and {len(INVALID) + 4} local/module rejections passed')
