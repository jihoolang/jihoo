"""Fully annotated dependent lambdas without expected types, checked against named functions."""
import ctypes
import json
import os
import platform
import shlex
import struct
from core_buffer import COUNTER

PREFIX = '''#![dependent_core]
enum Slot(n: u64) { Empty; Full(refine(fn(j) { Lt(j, n) })) }
'''
PROGRAM = PREFIX + '''
export fn nested_effect_partial(n: u64) -> i64 { let f = fn(x: i64, y: i64, z: i64) -> i64 { x + y + z }; let g = f(free(alloc(n, 7), 5)); let h = g(free(alloc(n + 1, 7), 6)); h(2) }
export fn effect_partial(n: u64) -> i64 { let f = fn(x: i64, y: i64) -> i64 { x + y }; let g = f(free(alloc(n, 7), 5)); g(2) }
export fn unused_effect_partial(n: u64) -> i64 { let f = fn(x: i64, y: i64) -> i64 { free(alloc(n + 1, 7), x + y) }; let g = f(free(alloc(n, 7), 5)); 0 }
export fn ordered_effect_partial(n: u64) -> i64 { let f = fn(x: i64, y: i64) -> i64 { free(alloc(n + 1, 7), x + y) }; let g = f(free(alloc(n, 7), 5)); g(2) + g(3) }
export fn captured_partial(n: u64) -> u64 { let f = fn(x: u64, y: u64) -> u64 { x + y }; let g = f(n + 1); g(2) }
export fn unused_partial(n: u64) -> u64 { let f = fn(x: u64, y: u64) -> u64 { x + y }; let g = f(n + 1); 0 }
export fn repeated_partial(n: u64) -> u64 { let f = fn(x: u64, y: u64) -> u64 { x + y }; let g = f(n + 1); g(2) + g(3) }
export fn unused_trap() -> i64 { let f = fn(x: u64) -> u64 { 18446744073709551615 + x }; 5 }
export fn unused_allocate() -> i64 { let f = fn(n: u64) -> buffer(n) { alloc(n, 7) }; 5 }
export fn allocate_twice() -> i64 { let f = fn(n: u64) -> buffer(n) { alloc(n, 7) }; let a = f(1); let b = f(1); free(a, free(b, 7)) }
export fn identity(n: u64) -> u64 { let id = fn(x: u64) -> u64 { x }; id(n) }
export fn immediate(n: u64) -> u64 { (fn(x: u64) -> u64 { x + 1 })(n) }
export fn captured(n: u64) -> u64 { let add = fn(x: u64) -> u64 { n + x }; add(3) + add(4) }
export fn curried(n: u64) -> u64 {
    let add = fn(x: u64, y: u64) -> u64 { x + y }
    let plus = add(n)
    plus(4)
}
export fn direct_curried(n: u64) -> u64 { (fn(x: u64, y: u64) -> u64 { x + y })(n)(4) }
export fn dependent(x: i64) -> i64 {
    let at = fn(n: erased(u64), xs: [i64; n], i: u64, p: erased(Lt(i, n))) -> i64 { index(xs, i, p) }
    at(2, [x, 8], 0, decide_lt(0, 2))
}
export fn evidence() -> i64 {
    let bound = fn(k: u64) -> Lt(0, k + 1) { zero_le(k) }
    index([7], 0, bound(0))
}
export fn family(n: u64) -> u64 {
    let make = fn(k: u64) -> Slot(k) { Slot.Empty }
    let s = make(n)
    match s { Empty => 7; Full(j) => witness(j) }
}
export fn owned(n: u64, x: i64) -> i64 {
    let make = fn(value: i64) -> buffer(n) { alloc(n, value) }
    let release = fn(k: erased(u64), b: buffer(k), result: i64) -> i64 { free(b, result) }
    release(n, make(x), x)
}
export fn unused_owner() -> i64 { let ignore = fn(b: buffer(1)) -> i64 { 9 }; ignore(alloc(1, 7)) }
export fn shadow(n: u64) -> u64 { let f = fn(n: u64, p: erased(Eq(n, n))) -> u64 { n }; f(n, refl(n)) }
'''
REFERENCE = PREFIX + '''
export fn nested_effect_partial(n: u64) -> i64 { let x = free(alloc(n, 7), 5); let y = free(alloc(n + 1, 7), 6); x + y + 2 }
export fn effect_partial(n: u64) -> i64 { let x = free(alloc(n, 7), 5); x + 2 }
export fn unused_effect_partial(n: u64) -> i64 { let x = free(alloc(n, 7), 5); 0 }
export fn ordered_effect_partial(n: u64) -> i64 { let x = free(alloc(n, 7), 5); free(alloc(n + 1, 7), x + 2) + free(alloc(n + 1, 7), x + 3) }
export fn captured_partial(n: u64) -> u64 { let x = n + 1; x + 2 }
export fn unused_partial(n: u64) -> u64 { let x = n + 1; 0 }
export fn repeated_partial(n: u64) -> u64 { let x = n + 1; (x + 2) + (x + 3) }
export fn unused_trap() -> i64 { 5 }
export fn unused_allocate() -> i64 { 5 }
export fn allocate_twice() -> i64 { let a = alloc(1, 7); let b = alloc(1, 7); free(a, free(b, 7)) }
fn id(x: u64) -> u64 { x }
fn increment(x: u64) -> u64 { x + 1 }
fn add(x: u64, y: u64) -> u64 { x + y }
fn at(n: erased(u64), xs: [i64; n], i: u64, p: erased(Lt(i, n))) -> i64 { index(xs, i, p) }
fn bound(k: u64) -> Lt(0, k + 1) { zero_le(k) }
fn make_slot(k: u64) -> Slot(k) { Slot.Empty }
fn make_buffer(n: u64, value: i64) -> buffer(n) { alloc(n, value) }
fn release(k: erased(u64), b: buffer(k), result: i64) -> i64 { free(b, result) }
fn ignore(b: buffer(1)) -> i64 { 9 }
fn keep(n: u64, p: erased(Eq(n, n))) -> u64 { n }
export fn identity(n: u64) -> u64 { id(n) }
export fn immediate(n: u64) -> u64 { increment(n) }
export fn captured(n: u64) -> u64 { add(n, 3) + add(n, 4) }
export fn curried(n: u64) -> u64 { add(n, 4) }
export fn direct_curried(n: u64) -> u64 { add(n, 4) }
export fn dependent(x: i64) -> i64 { at(2, [x, 8], 0, decide_lt(0, 2)) }
export fn evidence() -> i64 { index([7], 0, bound(0)) }
export fn family(n: u64) -> u64 { let s = make_slot(n); match s { Empty => 7; Full(j) => witness(j) } }
export fn owned(n: u64, x: i64) -> i64 { release(n, make_buffer(n, x), x) }
export fn unused_owner() -> i64 { ignore(alloc(1, 7)) }
export fn shadow(n: u64) -> u64 { keep(n, refl(n)) }
'''
WILDCARDS = '''
enum WildList { Nil; Cons(i64, WildList) }
trait Both(a: u64, b: u64) { fn both(a: u64, b: u64) -> Both(a, b) }
fn fixed(a: u64, b: u64, p: erased(Both(a, b))) -> Eq(0, 0) {
    induct(fn(_, _) { Eq(0, 0) }, fn(_, _) { refl(0) }, p)
}
export fn wildcard_proof(n: u64) -> u64 { let p = fixed(n, n, both(n, n)); n }
export fn wildcard_fold(n: u64) -> i64 { fold(n, 0, fn(_, _, acc) { acc + 1 }) }
export fn wildcard_partial(n: u64) -> u64 { (fn(_: u64, _: u64, result: u64) -> u64 { result })(n)(n)(n) }
export fn wildcard_nested(n: u64) -> u64 {
    let f: fn(u64) -> fn(u64) -> u64 = fn(_) { fn(_) { n } }
    f(1)(2)
}
export fn wildcard_dependent(n: u64) -> u64 {
    let f = fn(k: u64, _: erased(Eq(k, k)), _: u64) -> u64 { k }
    f(n, refl(n), 0)
}
export fn wildcard_effect(n: u64) -> i64 {
    let f = fn(_: i64, _: i64) -> i64 { 7 }
    let g = f(free(alloc(n, 7), 5))
    0
}
export fn wildcard_owned(n: u64) -> i64 {
    let f = fn(_: buffer(n), _: buffer(n)) -> i64 { 7 }
    f(alloc(n, 3), alloc(n, 4))
}
fn wildcard_length(xs: ref WildList) -> u64 {
    induct(fn(_, _: u64, _: u64) { u64 }, fn(_, _) { 0 },
        fn(_, _, ih, _, _) { ih(0, 0) + 1 }, xs)(0, 0)
}
export fn wildcard_motive(n: u64) -> u64 {
    let xs = fold(n, WildList.Nil, fn(_, _, acc) { WildList.Cons(1, acc) })
    wildcard_length(xs)
}
'''
NAMED_WILDCARDS = WILDCARDS.replace('fn(_, _) {', 'fn(first, second) {')
NAMED_WILDCARDS = NAMED_WILDCARDS.replace('fn(_, _, acc)', 'fn(i, bound, acc)')
NAMED_WILDCARDS = NAMED_WILDCARDS.replace('fn(_: u64, _: u64, result:', 'fn(first: u64, second: u64, result:')
NAMED_WILDCARDS = NAMED_WILDCARDS.replace('fn(_) { fn(_) {', 'fn(first) { fn(second) {')
NAMED_WILDCARDS = NAMED_WILDCARDS.replace('_: erased(Eq(k, k)), _: u64', 'evidence: erased(Eq(k, k)), ignored: u64')
NAMED_WILDCARDS = NAMED_WILDCARDS.replace('fn(_: i64, _: i64)', 'fn(first: i64, second: i64)')
NAMED_WILDCARDS = NAMED_WILDCARDS.replace('fn(_: buffer(n), _: buffer(n))', 'fn(first: buffer(n), second: buffer(n))')
NAMED_WILDCARDS = NAMED_WILDCARDS.replace('fn(_, _: u64, _: u64)', 'fn(node, first: u64, second: u64)')
NAMED_WILDCARDS = NAMED_WILDCARDS.replace('fn(_, _, ih, _, _)', 'fn(value, rest, ih, first, second)')
PROGRAM += WILDCARDS
REFERENCE += NAMED_WILDCARDS
INVALID = {
    'missing-parameter': ('fn bad() -> u64 { let f = fn(x) -> u64 { x }; 0 }', 'a lambda without context needs parameter annotations'),
    'missing-result': ('fn bad() -> u64 { let f = fn(x: u64) { x }; 0 }', 'a lambda without context needs a result annotation'),
    'zero-parameters': ('fn bad() -> u64 { let f = fn() -> u64 { 0 }; 0 }', 'a lambda without context needs at least one parameter'),
    'duplicate-parameter': ('fn bad() -> u64 { let f = fn(x: u64, x: u64) -> u64 { x }; 0 }', 'duplicate lambda parameter'),
    'reserved-parameter': ('fn bad() -> u64 { let f = fn(index: u64) -> u64 { index }; 0 }', 'a reserved name binds nothing'),
    'body-type': ('fn bad() -> u64 { let f = fn(x: i64) -> u64 { x }; 0 }', 'type mismatch'),
    'false-result': ('fn bad() -> u64 { let f = fn(n: u64) -> Eq(n, n + 1) { refl(n) }; 0 }', 'type mismatch'),
    'invalid-parameter-proof': ('fn bad() -> u64 { let f = fn(b: buffer(sub(2, 1, decide_lt(0, 1)))) -> i64 { free(b, 0) }; 0 }', 'type mismatch'),
    'invalid-result-proof': ('fn bad() -> u64 { let f = fn(x: i64) -> buffer(sub(2, 1, decide_lt(0, 1))) { alloc(1, x) }; 0 }', 'type mismatch'),
    'forward-domain': ('fn bad() -> u64 { let f = fn(xs: [i64; n], n: u64) -> i64 { 0 }; 0 }', 'unknown name (or recursive/forward definition): n'),
    'unbound-result': ('fn bad() -> u64 { let f = fn(x: i64) -> buffer(missing) { alloc(1, x) }; 0 }', 'unknown name (or recursive/forward definition): missing'),
    'relevant-proof': ('fn bad() -> u64 { let f = fn(p: Eq(0, 0)) -> u64 { 0 }; 0 }', 'proof binders must be erased'),
    'erased-i64': ('fn bad() -> u64 { let f = fn(x: erased(i64)) -> i64 { 0 }; 0 }', 'erased binders must be propositions, u64 or data'),
    'erased-runtime': ('fn bad() -> u64 { let f = fn(x: erased(u64)) -> u64 { x }; 0 }', 'erased value used at runtime'),
    'duplicate-owner': ('fn bad() -> u64 { let f = fn(b: buffer(1)) -> i64 { free(b, free(b, 0)) }; 0 }', 'an owned value is used more than once'),
    'captured-owner': ('fn bad(b: buffer(1)) -> i64 { let f = fn(x: i64) -> i64 { free(b, x) }; f(1) + f(2) }', 'a function cannot capture an owned value'),
    'direct-missing-result': ('fn bad() -> u64 { (fn(x: u64) { x })(0) }', 'a lambda without context needs a result annotation'),
}
INVALID.update({
    'wildcard-reference': ('fn bad() -> u64 { let f = fn(_: u64, _: u64) -> u64 { _ }; f(0, 0) }', 'a discarded binding is not a value'),
    'wildcard-domain': ('fn bad() -> u64 { let f = fn(_: u64, b: buffer(_)) -> i64 { free(b, 0) }; 0 }', 'a discarded binding is not a value'),
    'wildcard-evidence': ('fn bad() -> Eq(0, 0) { let f: fn(erased(Eq(0, 0)), erased(Eq(0, 0))) -> Eq(0, 0) = fn(_, _) { _ }; f(refl(0), refl(0)) }', 'a discarded binding is not a value'),
    'wildcard-invalid-evidence': ('fn bad() -> u64 { let f = fn(_: erased(Eq(0, 1)), _: u64) -> u64 { 0 }; f(refl(0), 0) }', 'type mismatch'),
    'wildcard-owner-reuse': ('fn bad(b: buffer(1)) -> i64 { let f = fn(_: buffer(1), _: buffer(1)) -> i64 { 0 }; f(b, b) }', 'an owned value is used more than once'),
    'wildcard-named-duplicate': ('fn bad() -> u64 { let f: fn(u64, u64, u64) -> u64 = fn(_, x, x) { x }; 0 }', 'duplicate lambda parameter'),
})
ANCHOR = '\nexport fn harness_anchor() -> i64 { 0 }\n'


def validate_lambdas(compiler, root, temporary, environment, run):
    def command(action, path, *args, success=True, env=environment):
        return run([compiler, action, str(path), *args], success=success, env=env)
    source, reference = temporary / 'lambdas.jh', temporary / 'lambdas-reference.jh'
    source.write_text(PROGRAM); reference.write_text(REFERENCE)
    command('check', source, '--lib', env={**environment, 'JIHOO_LLVM': '/unavailable', 'JIHOO_CC': '/unavailable'})
    mir = command('emit-mir', source, '--lib').stdout
    expected = command('emit-mir', reference, '--lib').stdout
    assert mir == expected, 'local and named dependent functions differ in MIR'
    formatted = temporary / 'lambdas-formatted.jh'; formatted.write_text(command('fmt', source).stdout)
    assert command('fmt', formatted).stdout == formatted.read_text()
    assert command('emit-mir', formatted, '--lib').stdout == mir
    counter = temporary / 'lambdas-counter.c'; counter.write_text(COUNTER.replace('long allocations, frees;', 'long allocations, frees; long events[64], event_count;')
        .replace('allocations++;', 'allocations++; if (event_count < 64) events[event_count++] = (long)n;')
        .replace('frees++;', 'frees++; if (event_count < 64) events[event_count++] = -1;'))
    host = 'aarch64' if platform.machine() in ('aarch64', 'arm64') else 'x86_64'
    for target, machine in (('x86_64', 62), ('aarch64', 183)):
        for level in ('-O0', '-O2'):
            obj = temporary / f'lambdas-{target}{level}.o'
            command('emit-obj', source, '--lib', '--target', target, level, '-o', str(obj))
            assert struct.unpack_from('<H', obj.read_bytes(), 18)[0] == machine
            if target != host:
                continue
            library = temporary / f'lambdas{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC', 'clang')), '-shared', '-fPIC', str(obj), str(counter),
                 '-Wl,--wrap=malloc', '-Wl,--wrap=free', '-o', str(library)])
            native = ctypes.CDLL(str(library))
            for name in ('identity', 'immediate', 'captured', 'curried', 'direct_curried', 'family', 'shadow', 'captured_partial', 'unused_partial', 'repeated_partial', 'wildcard_partial', 'wildcard_nested', 'wildcard_dependent', 'wildcard_proof'):
                fn = getattr(native, name); fn.argtypes, fn.restype = [ctypes.c_uint64], ctypes.c_uint64
            native.dependent.argtypes, native.dependent.restype = [ctypes.c_int64], ctypes.c_int64
            native.owned.argtypes, native.owned.restype = [ctypes.c_uint64, ctypes.c_int64], ctypes.c_int64
            for name in ('wildcard_fold', 'wildcard_motive', 'wildcard_owned'):
                fn = getattr(native, name); fn.argtypes, fn.restype = [ctypes.c_uint64], ctypes.c_uint64
            for n in (0, 1, 8):
                assert native.wildcard_fold(n) == n and native.wildcard_motive(n) == n
                before = ctypes.c_long.in_dll(native, 'allocations').value
                assert native.wildcard_owned(n) == 7
                if level == '-O0': assert ctypes.c_long.in_dll(native, 'allocations').value == before + 2
            for n in (0, 1, 3, 16, 1 << 62):
                assert native.identity(n) == n and native.shadow(n) == n
                assert native.wildcard_partial(n) == n and native.wildcard_nested(n) == n
                assert native.wildcard_dependent(n) == n and native.wildcard_proof(n) == n
                assert native.immediate(n) == n + 1 and native.captured(n) == 2*n + 7
                assert native.curried(n) == n + 4 and native.direct_curried(n) == n + 4
                assert native.family(n) == 7
                assert native.captured_partial(n) == n + 3 and native.unused_partial(n) == 0
                assert native.repeated_partial(n) == 2*n + 7
            for name, expected, events in (
                ('effect_partial', 7, [32, -1]),
                ('nested_effect_partial', 13, [32, -1, 40, -1]),
                ('unused_effect_partial', 0, [32, -1]),
                ('wildcard_effect', 0, [32, -1]),
                ('ordered_effect_partial', 15, [32, -1, 40, -1, 40, -1]),
            ):
                fn = getattr(native, name); fn.argtypes, fn.restype = [ctypes.c_uint64], ctypes.c_int64
                ctypes.c_long.in_dll(native, 'event_count').value = 0
                assert fn(3) == expected
                if level == '-O0':
                    count = ctypes.c_long.in_dll(native, 'event_count').value
                    observed = list((ctypes.c_long * 64).in_dll(native, 'events'))[:count]
                    assert observed == events, (name, observed)
            assert native.unused_partial((1 << 64) - 2) == 0
            for x in (-19, 0, 100):
                assert native.dependent(x) == x
                for n in (0, 1, 8):
                    assert native.owned(n, x) == x
            assert native.evidence() == 7 and native.unused_owner() == 9
            count = ctypes.c_long.in_dll(native, 'allocations').value
            assert native.unused_trap() == 5 and native.unused_allocate() == 5
            assert ctypes.c_long.in_dll(native, 'allocations').value == count
            assert native.allocate_twice() == 7
            # LLVM can eliminate these unused buffers at -O2. Before optimization,
            # each call must allocate once; both levels must balance frees.
            if level == '-O0':
                assert ctypes.c_long.in_dll(native, 'allocations').value == count + 2
            assert ctypes.c_long.in_dll(native, 'allocations').value == ctypes.c_long.in_dll(native, 'frees').value
    # Calling a latent body must retain traps even if its result is unused.
    trap = temporary / 'lambda-called-trap.jh'
    trap.write_text(PREFIX + 'fn main() -> i64 { let f = fn(x: u64) -> u64 { 18446744073709551615 + x }; let unused = f(1); 0 }')
    for level in ('-O0', '-O2'):
        assert command('run', trap, level, success=False).returncode == 132
    # A partial application's argument evaluates at capture time, even if
    # the resulting function is discarded or its body would ignore that value.
    for name, result in (('called', 'g(2)'), ('unused', '0')):
        capture = temporary / f'lambda-capture-trap-{name}.jh'
        capture.write_text(PREFIX + 'fn main() -> i64 { let f = fn(_: u64, _: i64) -> i64 { 7 }; '
                           'let g = f(18446744073709551615 + 1); ' + result + ' }')
        for level in ('-O0', '-O2'):
            assert command('run', capture, level, success=False).returncode == 132
    # An effectful capture whose scalar result traps must still trap, even
    # when the partially applied function is unused.
    for name, result in (('called', 'g(2)'), ('unused', '0')):
        capture = temporary / f'lambda-effect-capture-trap-{name}.jh'
        capture.write_text(PREFIX + 'fn main() -> i64 { let f = fn(x: i64, y: i64) -> i64 { y }; '
                           'let g = f(free(alloc(1, 7), 9223372036854775807 + 1)); ' + result + ' }')
        for level in ('-O0', '-O2'):
            assert command('run', capture, level, success=False).returncode == 132
    flags = ('--lib', '--no-verify', '--release', '--error-format=json')
    no_elab = {**environment, 'JIHOO_NO_ELAB': '1'}
    control = temporary / 'lambdas-negative-control.jh'
    control.write_text(PREFIX + 'fn valid() -> u64 { let f = fn(x: u64) -> u64 { x }; f(0) }' + ANCHOR)
    command('check', control, *flags, env=no_elab)
    control_obj = temporary / 'lambdas-negative-control.o'
    command('emit-obj', control, *flags, '-o', str(control_obj), env=no_elab)
    assert control_obj.read_bytes().startswith(b'\x7fELF')
    for name, (body, diagnostic) in INVALID.items():
        bad = temporary / f'lambdas-{name}.jh'; bad.write_text(PREFIX + body + ANCHOR)
        obj = temporary / f'lambdas-{name}.o'
        for action, options in (('check', ()), ('emit-obj', ('-o', str(obj)))):
            result = command(action, bad, *flags, *options, success=False, env=no_elab)
            errors = [d for d in json.loads(result.stderr)['diagnostics'] if d['severity'] == 'error']
            assert result.returncode == 1 and len(errors) == 1, (name, action, result.stderr)
            assert errors[0]['kind'] == 'source' and errors[0]['message'] == 'core: '+diagnostic, (name, action, result.stderr)
        assert not obj.exists(), name
    print(f'annotated dependent lambdas: named-function MIR, formatter, both targets, native/ownership, positive harness and {len(INVALID)} intended rejections passed')
