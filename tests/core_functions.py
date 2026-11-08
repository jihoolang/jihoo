"""Explicit function types: outer indices, higher-order specialization and evidence."""
import ctypes
import json
import os
import platform
import re
import shlex
import struct
from core_buffer import COUNTER

PREFIX = '#![dependent_core]\nimport dependent.nat\n'
HELPER = '''#![dependent_core]
pub fn answer() -> u64 { 23 }
pub fn factory() -> fn(u64) -> u64 { fn(x) { x + 1 } }
pub fn certificate() -> Eq(18446744073709551615 + 1, 18446744073709551615 + 1) { refl(18446744073709551615 + 1) }
pub fn owned() -> buffer(2) { alloc(2, 7) }
pub fn twice(f: fn(u64) -> u64, x: u64) -> u64 { f(f(x)) }
pub fn compose(f: fn(u64) -> u64, g: fn(u64) -> u64) -> fn(u64) -> u64 { fn(x) { f(g(x)) } }
'''
PROGRAM = PREFIX + '''
import function_helper
fn at(n: erased(u64), i: erased(u64), f: fn([i64; n], erased(Lt(i, n))) -> i64,
      xs: [i64; n], p: erased(Lt(i, n))) -> i64 { f(xs, p) }
fn sum(n: u64, x: i64, f: fn(i64) -> i64) -> i64 { fold(n, 0, fn(i, p, acc) { acc + f(x) }) }
fn make(n: u64) -> fn(i64) -> buffer(n) { fn(x) { alloc(n, x) } }
fn release(n: erased(u64), f: fn(buffer(n)) -> i64, b: buffer(n)) -> i64 { f(b) }
fn keep(n: u64, p: erased(Eq(n + 1, n + 1))) -> u64 { n }
fn evidence(n: u64, f: erased(fn(u64) -> Eq(n, n))) -> Eq(n, n) { f(n) }
export fn increment(n: u64) -> u64 { function_helper.twice(fn(x) { x + 1 }, n) }
export fn composed(n: u64) -> u64 { function_helper.compose(fn(x) { x + n }, fn(x) { x + 2 })(3) }
export fn annotated(n: u64) -> u64 { let f: fn(u64, u64) -> u64 = fn(x, y) { x + y }; f(n, 4) }
export fn selected(x: i64) -> i64 { at(2, 0, fn(xs, p) { index(xs, 0, p) }, [x, 8], decide_lt(0, 2)) }
export fn accumulated(n: u64, x: i64) -> i64 { sum(n, x, fn(y) { y + 1 }) }
export fn owned(n: u64) -> i64 { release(n, fn(b) { free(b, 7) }, make(n)(9)) }
fn twice_owned(f: fn(i64) -> buffer(1), x: i64) -> i64 { let a = f(x); let b = f(x + 1); free(a, free(b, 7)) }
export fn effects(x: i64) -> i64 { twice_owned(fn(y) { alloc(1, y) }, x) }
export fn congruent(n: u64) -> u64 { keep(n, nat.eq_congr(fn(k) { k + 1 }, n, n, refl(n))) }
export fn ghost(n: u64) -> u64 { let p = evidence(n, fn(k) { refl(n) }); n }
export fn unused_body(n: u64) -> u64 { let f: fn(u64) -> buffer(n) = fn(k) { alloc(n, 7) }; n }
'''
PROGRAM += '''fn answer() -> u64 { 11 }
export fn nullary(n: u64) -> u64 {
    let f = function_helper.factory()
    let p = function_helper.certificate()
    answer() + function_helper.answer() + f(n)
}
export fn nullary_owned(n: u64) -> i64 {
    let a = function_helper.owned()
    let b = function_helper.owned()
    free(a, free(b, 11))
}
'''
REFERENCE = PREFIX + '''
fn value_buffer(x: i64) -> buffer(1) { alloc(1, x) }
export fn increment(n: u64) -> u64 { let first = n + 1; first + 1 }
export fn composed(n: u64) -> u64 { 5 + n }
export fn annotated(n: u64) -> u64 { n + 4 }
export fn selected(x: i64) -> i64 { index([x, 8], 0, decide_lt(0, 2)) }
export fn accumulated(n: u64, x: i64) -> i64 { fold(n, 0, fn(i, p, acc) { acc + (x + 1) }) }
export fn owned(n: u64) -> i64 { free(alloc(n, 9), 7) }
export fn effects(x: i64) -> i64 { let a = value_buffer(x); let b = value_buffer(x + 1); free(a, free(b, 7)) }
export fn congruent(n: u64) -> u64 { n }
export fn ghost(n: u64) -> u64 { n }
export fn unused_body(n: u64) -> u64 { n }
'''
REFERENCE += '''export fn nullary(n: u64) -> u64 { 11 + 23 + (n + 1) }
export fn nullary_owned(n: u64) -> i64 { let a = alloc(2, 7); let b = alloc(2, 7); free(a, free(b, 11)) }
'''
INVALID = {
    'empty': ('fn bad(f: fn() -> u64) -> u64 { 0 }', 'a dependent function type needs at least one parameter'),
    'result': ('fn bad(f: fn(u64)) -> u64 { 0 }', 'a dependent function type needs an explicit result'),
    'inout': ('fn bad(f: fn(inout i64) -> i64) -> u64 { 0 }', 'function type parameters use plain types or erased(T)'),
    'sink': ('fn bad(f: fn(sink i64) -> i64) -> u64 { 0 }', 'function type parameters use plain types or erased(T)'),
    'erased-i64': ('fn bad(f: fn(erased(i64)) -> i64) -> u64 { 0 }', 'erased binders must be propositions, u64 or data'),
    'relevant-proof': ('fn bad(f: fn(Eq(0, 0)) -> u64) -> u64 { 0 }', 'proof binders must be erased'),
    'domain-proof': ('fn bad(f: fn(buffer(sub(2, 1, decide_lt(0, 1)))) -> i64) -> u64 { 0 }', 'type mismatch'),
    'result-proof': ('fn bad(f: fn(u64) -> buffer(sub(2, 1, decide_lt(0, 1)))) -> u64 { 0 }', 'type mismatch'),
    'wrong-body': ('fn bad() -> u64 { let f: fn(i64) -> u64 = fn(x) { x }; 0 }', 'type mismatch'),
    'wrong-domain': ('fn bad() -> u64 { let f: fn(u64) -> u64 = fn(x: i64) { 0 }; 0 }', 'lambda parameter annotation does not match its expected type'),
    'false-congruence': ('fn bad(f: fn(u64) -> u64) -> Eq(f(0), f(1)) { nat.eq_congr(f, 0, 1, refl(0)) }', 'type mismatch'),
    'wrong-outer': ('fn bad(n: u64, m: u64) -> u64 { let f: fn(buffer(n), u64) -> buffer(m) = fn(b, x) { b }; 0 }', 'type mismatch'),
    'owned-capture': ('fn bad(b: buffer(1)) -> i64 { let f: fn(i64) -> i64 = fn(x) { free(b, x) }; f(1) + f(2) }', 'a function cannot capture an owned value'),
    'duplicate-owner': ('fn bad() -> u64 { let f: fn(buffer(1)) -> i64 = fn(b) { free(b, free(b, 0)) }; 0 }', 'an owned value is used more than once'),
    'erased-runtime-function': ('fn bad(f: erased(fn(u64) -> u64)) -> u64 { 0 }', 'erased binders must be propositions, u64 or data'),
    'export-closure': ('export fn bad(f: fn(u64) -> u64, x: u64) -> u64 { f(x) }', 'exports require scalar arguments and results'),
}
nested = 'u64'
for _ in range(140): nested = f'fn({nested}) -> u64'
EMPTY_CALL = 'a function-valued call needs at least one argument'
INVALID.update({
    'empty-local': ('fn bad(f: fn(u64) -> u64) -> fn(u64) -> u64 { f() }', EMPTY_CALL),
    'empty-unused': ('fn bad(f: fn(u64) -> u64) -> u64 { let ignored = f(); 0 }', EMPTY_CALL),
    'empty-lambda': ('fn bad() -> fn(u64) -> u64 { (fn(x: u64) -> u64 { x })() }', EMPTY_CALL),
    'empty-partial': ('fn bad(f: fn(u64, u64) -> u64) -> fn(u64) -> u64 { f(1)() }', EMPTY_CALL),
    'empty-scalar-result': ('fn value() -> i64 { 17 } fn bad() -> i64 { value()() }', EMPTY_CALL),
    'empty-owned-result': ('fn value() -> buffer(1) { alloc(1, 7) } fn bad() -> buffer(1) { value()() }', EMPTY_CALL),
    'empty-proof-result': ('fn certificate() -> Eq(1, 1) { refl(1) } fn bad() -> Eq(1, 1) { certificate()() }', EMPTY_CALL),
    'empty-imported-result': ('import function_helper\nfn bad() -> u64 { function_helper.answer()() }', EMPTY_CALL),
    'empty-factory-result': ('import function_helper\nfn bad() -> fn(u64) -> u64 { function_helper.factory()() }', EMPTY_CALL),
    'empty-erased-callback': ('fn bad(f: erased(fn(u64) -> Eq(1, 1))) -> fn(u64) -> Eq(1, 1) { f() }', EMPTY_CALL),
})
INVALID['nesting-limit'] = (f'fn bad(f: {nested}) -> u64 {{ 0 }}', 'elaboration nesting limit reached')
ANCHOR = '\nexport fn positive_anchor() -> i64 { 0 }\n'


def validate_functions(compiler, root, temporary, environment, run):
    def command(action, path, *args, success=True, env=environment):
        return run([compiler, action, str(path), *args], success=success, env=env)
    (temporary/'function_helper.jh').write_text(HELPER)
    source, reference = temporary/'functions.jh', temporary/'functions-reference.jh'
    source.write_text(PROGRAM); reference.write_text(REFERENCE)
    command('check', source, '--lib', env={**environment, 'JIHOO_LLVM':'/unavailable','JIHOO_CC':'/unavailable'})
    mir = command('emit-mir', source, '--lib').stdout
    expected = command('emit-mir', reference, '--lib').stdout
    assert mir == expected, 'higher-order specialization changed runtime MIR'
    formatted = temporary/'functions-formatted.jh'
    formatted.write_text(command('fmt',source).stdout)
    assert command('fmt',formatted).stdout == formatted.read_text()
    assert command('emit-mir',formatted,'--lib').stdout == mir
    counter = temporary/'functions-counter.c'; counter.write_text(COUNTER)
    host = 'aarch64' if platform.machine() in ('aarch64','arm64') else 'x86_64'
    for target,machine in (('x86_64',62),('aarch64',183)):
        for level in ('-O0','-O2'):
            obj = temporary/f'functions-{target}{level}.o'
            command('emit-obj',source,'--lib','--target',target,level,'-o',str(obj))
            assert struct.unpack_from('<H',obj.read_bytes(),18)[0] == machine
            if target != host: continue
            library=temporary/f'functions{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC','clang')),'-shared','-fPIC',str(obj),str(counter),
                 '-Wl,--wrap=malloc','-Wl,--wrap=free','-o',str(library)])
            native=ctypes.CDLL(str(library))
            for name in ('increment','composed','annotated','congruent','ghost','unused_body','nullary'):
                f=getattr(native,name); f.argtypes,f.restype=[ctypes.c_uint64],ctypes.c_uint64
            for n in (0,1,9,1<<62):
                assert native.increment(n)==n+2 and native.composed(n)==n+5 and native.annotated(n)==n+4
                assert native.nullary(n)==n+35
            count=ctypes.c_long.in_dll(native,'allocations').value
            for n in (0,1,(1<<64)-1):
                assert native.congruent(n)==n and native.ghost(n)==n and native.unused_body(n)==n
            assert ctypes.c_long.in_dll(native,'allocations').value==count
            native.selected.argtypes,native.selected.restype=[ctypes.c_int64],ctypes.c_int64
            native.accumulated.argtypes,native.accumulated.restype=[ctypes.c_uint64,ctypes.c_int64],ctypes.c_int64
            native.owned.argtypes,native.owned.restype=[ctypes.c_uint64],ctypes.c_int64
            native.nullary_owned.argtypes,native.nullary_owned.restype=[ctypes.c_uint64],ctypes.c_int64
            for x in (-9,0,10):
                assert native.selected(x)==x
                for n in (0,1,5): assert native.accumulated(n,x)==n*(x+1)
            for n in (0,1,9):
                count=ctypes.c_long.in_dll(native,'allocations').value
                assert native.owned(n)==7
                if level=='-O0': assert ctypes.c_long.in_dll(native,'allocations').value==count+1
            native.effects.argtypes,native.effects.restype=[ctypes.c_int64],ctypes.c_int64
            count=ctypes.c_long.in_dll(native,'allocations').value
            assert native.effects(3)==7
            if level=='-O0': assert ctypes.c_long.in_dll(native,'allocations').value==count+2
            count=ctypes.c_long.in_dll(native,'allocations').value
            assert native.nullary_owned(0)==11
            if level=='-O0': assert ctypes.c_long.in_dll(native,'allocations').value==count+2
            assert ctypes.c_long.in_dll(native,'allocations').value==ctypes.c_long.in_dll(native,'frees').value
    snippets=re.findall(r'```jihoo\n(.*?)```', (root/'docs/language/dependent-functions.md').read_text(), re.S)
    assert len(snippets)==1
    documented=temporary/'functions-documented.jh';documented.write_text(snippets[0])
    assert command('run',documented,success=False).returncode==17
    example=root/'examples/core_functions.jh'
    for level in ('-O0','-O2'): assert command('run',example,level,success=False).returncode==17
    trap=temporary/'functions-trap.jh'
    trap.write_text(PREFIX+'fn apply(f: fn(u64) -> u64, x: u64) -> u64 { f(x) }\nfn main() -> i64 { let ignored=apply(fn(x) { x + 1 }, 18446744073709551615); 0 }')
    for level in ('-O0','-O2'): assert command('run',trap,level,success=False).returncode==132
    flags=('--lib','--release','--no-verify','--error-format=json')
    env={**environment,'JIHOO_NO_ELAB':'1'}
    control=temporary/'functions-control.jh'; control.write_text(PREFIX+'fn valid(f: fn(u64) -> u64) -> u64 { f(0) }'+ANCHOR)
    command('check',control,*flags,env=env)
    obj=temporary/'functions-control.o';command('emit-obj',control,*flags,'-o',str(obj),env=env)
    assert obj.read_bytes().startswith(b'\x7fELF')
    for name,(body,diagnostic) in INVALID.items():
        bad=temporary/f'functions-{name}.jh';bad.write_text(PREFIX+body+ANCHOR)
        obj=temporary/f'functions-{name}.o'
        for action,opts in (('check',()),('emit-obj',('-o',str(obj)))):
            r=command(action,bad,*flags,*opts,success=False,env=env)
            errors=[d for d in json.loads(r.stderr)['diagnostics'] if d['severity']=='error']
            assert r.returncode==1 and len(errors)==1,(name,action,r.stderr)
            assert errors[0]['kind']=='source' and errors[0]['message']=='core: '+diagnostic,(name,action,r.stderr)
        assert not obj.exists(),name
    print(f'explicit function types: higher-order MIR, outer indices, erased functions, ownership, both targets, traps, positive control and {len(INVALID)} intended rejections passed')
