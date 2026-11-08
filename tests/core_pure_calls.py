"""Pure natural call transparency must not infer purity from a callback type."""
import ctypes
import json
import os
import platform
import shlex
from core_buffer import COUNTER

PREFIX = '#![dependent_core]\n'
HELPER = PREFIX + '''
fn private(n: u64) -> u64 { n }
pub fn next(n: u64) -> u64 { n + 1 }
pub fn plus(a: u64, b: u64) -> u64 { a + b }
pub fn shift(n: u64) -> fn(u64) -> u64 { fn(x) { n + x } }
'''
PROGRAM = PREFIX + '''
import pure_call_helper
fn twice(n: u64) -> u64 { pure_call_helper.next(pure_call_helper.next(n)) }
export fn checked(n: u64) -> u64 {
    let x = twice(n)
    let evidence: Eq(x, n + 2) = refl(n + 2)
    x
}
export fn closure(n: u64) -> u64 {
    let observed = free(alloc(1, 7), n)
    let f = fn(x: u64) -> u64 { x + observed }
    let g = f
    let y = g(2)
    let evidence: Eq(y, observed + 2) = refl(observed + 2)
    y + g(3)
}
export fn curried(n: u64) -> u64 {
    let shift = pure_call_helper.shift(n)
    let result = shift(3)
    let evidence: Eq(result, n + 3) = refl(n + 3)
    result
}
export fn partial(n: u64) -> u64 {
    let f = pure_call_helper.plus
    let g = f(n)
    let result = g(4)
    let evidence: Eq(result, n + 4) = refl(n + 4)
    result
}
export fn shadow(n: u64) -> u64 {
    let f = fn(x: u64) -> u64 { x + n }
    let f = fn(x: u64) -> u64 { x + 1 }
    let result = f(n)
    let evidence: Eq(result, n + 1) = refl(n + 1)
    result
}
fn main() -> i64 { let f = fn(n: u64) -> u64 { n + 18446744073709551615 }; 0 }
'''
INVALID = {
    'unknown-callback': 'fn bad(f: fn(u64) -> u64, n: u64) -> i64 { let y = f(n); let p: Eq(y, f(n)) = refl(f(n)); 0 }',
    'captured-callback': 'fn bad(f: fn(u64) -> u64, n: u64) -> i64 { let g = fn(x: u64) -> u64 { f(x) }; let y = g(n); let p: Eq(y, f(n)) = refl(f(n)); 0 }',
    'returned-callback': 'fn bad(f: fn(u64) -> u64, n: u64) -> i64 { let g = fn(x: u64) -> fn(u64) -> u64 { f }; let y = g(0)(n); let p: Eq(y, f(n)) = refl(f(n)); 0 }',
    'effectful-body': 'fn effect(n: u64) -> u64 { free(alloc(1, 7), n) } fn bad(n: u64) -> i64 { let y = effect(n); let p: Eq(y, n) = refl(n); 0 }',
    'discarded-effect': 'fn discard(n: u64) -> u64 { 0 } fn bad(n: u64) -> i64 { let y = discard(free(alloc(1, 7), n)); let p: Eq(y, 0) = refl(0); 0 }',
    'strict-partial': 'fn add(n: u64, x: u64) -> u64 { n + x } fn bad(n: u64) -> i64 { let f = add; let g = f(n + 1); let y = g(2); let p: Eq(y, n + 3) = refl(n + 3); 0 }',
    'wrong-equation': 'fn next(n: u64) -> u64 { n + 1 } fn bad(n: u64) -> i64 { let y = next(n); let p: Eq(y, n) = refl(n); 0 }',
    'wrong-shadow': 'fn bad(n: u64) -> i64 { let f = fn(x: u64) -> u64 { x }; let f = fn(x: u64) -> u64 { x + 1 }; let y = f(n); let p: Eq(y, n) = refl(n); 0 }',
}


def validate_pure_calls(compiler, root, temporary, environment, run):
    (temporary / 'pure_call_helper.jh').write_text(HELPER)
    def command(action, path, *args, success=True):
        return run([compiler, action, str(path), *args], success=success, env={**environment, 'JIHOO_NO_ELAB': '1'})
    source = temporary / 'pure-calls.jh'
    source.write_text(PROGRAM)
    command('check', source)
    for level in ('-O0', '-O2'):
        command('run', source, level)
    formatted = temporary / 'pure-calls-formatted.jh'
    formatted.write_text(command('fmt', source).stdout)
    assert command('fmt', formatted).stdout == formatted.read_text()
    assert command('emit-mir', source).stdout == command('emit-mir', formatted).stdout
    runtime = temporary / 'pure-calls-runtime.jh'
    runtime.write_text(PROGRAM.split('fn main()')[0])
    counter = temporary / 'pure-call-counter.c'
    counter.write_text(COUNTER)
    for target, machine in (('x86_64', 62), ('aarch64', 183)):
        for level in ('-O0', '-O2'):
            obj = temporary / f'pure-calls-{target}{level}.o'
            command('emit-obj', runtime, '--lib', '--target', target, level, '-o', str(obj))
            data = obj.read_bytes()
            assert data[:4] == b'\x7fELF' and int.from_bytes(data[18:20], 'little') == machine
            if target != {'AMD64': 'x86_64', 'arm64': 'aarch64'}.get(platform.machine(), platform.machine()):
                continue
            shared = temporary / f'pure-calls{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC', 'clang')), '-shared', '-fPIC', str(obj), str(counter), '-o', str(shared), '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
            native = ctypes.CDLL(str(shared))
            allocations = ctypes.c_long.in_dll(native, 'allocations')
            frees = ctypes.c_long.in_dll(native, 'frees')
            for name, expected in [('checked', lambda n: n + 2), ('closure', lambda n: 2*n + 5), ('curried', lambda n: n + 3), ('shadow', lambda n: n + 1), ('partial', lambda n: n + 4)]:
                fn = getattr(native, name)
                fn.argtypes = [ctypes.c_uint64]
                fn.restype = ctypes.c_uint64
                for n in (0, 1, 17, 65536, (1 << 62) - 3):
                    allocations.value = frees.value = 0
                    assert fn(n) == expected(n), (name, n, level)
                    assert allocations.value == frees.value
                    if level == '-O0': assert allocations.value == int(name == 'closure')
    for name, body in {
        'unused-call': 'let y = next(18446744073709551615); 0',
        'proof-call': 'let y = next(18446744073709551615); let p = refl(y); 0',
        'called-lambda': 'let f = fn(n: u64) -> u64 { n + 18446744073709551615 }; let y = f(1); 0',
    }.items():
        trap = temporary / f'pure-call-trap-{name}.jh'
        trap.write_text(PREFIX + 'fn next(n: u64) -> u64 { n + 1 }\nfn main() -> i64 { ' + body + ' }')
        for level in ('-O0', '-O2'):
            assert command('run', trap, level, success=False).returncode == 132
    flags = ('--lib', '--release', '--no-verify', '--error-format=json')
    control = temporary / 'pure-call-control.jh'
    control.write_text(PREFIX + 'fn next(n: u64) -> u64 { n + 1 }\nexport fn good(n: u64) -> u64 { let y = next(n); let p: Eq(y, n + 1) = refl(n + 1); y }')
    obj = temporary / 'pure-call-control.o'
    command('emit-obj', control, *flags, '-o', str(obj))
    assert obj.exists()
    for name, body in INVALID.items():
        bad = temporary / f'pure-call-{name}.jh'
        bad.write_text(PREFIX + body + '\nexport fn anchor() -> i64 { 0 }')
        obj = temporary / f'pure-call-{name}.o'
        for action, opts in (('check', ()), ('emit-obj', ('-o', str(obj)))):
            result = command(action, bad, *flags, *opts, success=False)
            errors = [d for d in json.loads(result.stderr)['diagnostics'] if d['severity'] == 'error']
            assert result.returncode == 1 and len(errors) == 1, (name, result.stderr)
            assert errors[0]['message'] == 'core: type mismatch', (name, result.stderr)
        assert not obj.exists()
    for name, body, diagnostic in (
        ('private-reference', 'import pure_call_helper\nfn bad() -> i64 { let f = pure_call_helper.private; 0 }', 'core: unknown name (or recursive/forward definition): pure_call_helper.private'),
        ('shadowed-module', 'import pure_call_helper\nfn bad(pure_call_helper: u64) -> i64 { let f = pure_call_helper.next; 0 }', 'core: unsupported expression in dependent_core'),
    ):
        bad = temporary / f'pure-call-{name}.jh'
        bad.write_text(PREFIX + body + '\nexport fn anchor() -> i64 { 0 }')
        result = command('check', bad, *flags, success=False)
        errors = [d for d in json.loads(result.stderr)['diagnostics'] if d['severity'] == 'error']
        assert result.returncode == 1 and len(errors) == 1 and errors[0]['message'] == diagnostic, (name, result.stderr)
    print('pure natural calls: imported/local/curried conversion, lexical capture, latent traps, both targets, native O0/O2 effects and 8 exact rejections plus 2 visibility rejections passed')
