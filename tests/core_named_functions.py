"""Named dependent function-type binders: scope, substitution, erasure and ownership."""
import ctypes
import json
import os
import platform
import re
import shlex
import struct
from core_buffer import COUNTER

HELPER = '''#![dependent_core]
pub fn apply(n: u64, x: i64, f: fn(k: erased(u64), buffer(k)) -> i64) -> i64 { f(n, alloc(n, x)) }
pub fn make(n: u64, x: i64, f: fn(k: u64, i64) -> buffer(k)) -> buffer(n) { f(n, x) }
pub fn read(n: erased(u64), b: ref buffer(n), i: u64, p: erased(Lt(i, n)),
    f: fn(k: erased(u64), ref buffer(k), j: u64, erased(Lt(j, k))) -> i64) -> i64 { f(n, b, i, p) }
'''
PREFIX = '#![dependent_core]\nimport named_helper\n'
PROGRAM = PREFIX + '''
fn release(k: erased(u64), b: buffer(k)) -> i64 { free(b, 9) }
export fn owned(n: u64, x: i64) -> i64 { named_helper.apply(n, x, release) }
export fn produced(n: u64, x: i64) -> i64 {
    let maker: fn(size: u64, i64) -> buffer(size) = fn(k, v) { alloc(k, v) }
    free(named_helper.make(n, x, maker), 7)
}
export fn borrowed(x: i64) -> i64 {
    let b = alloc(1, x)
    let got = named_helper.read(1, b, 0, decide_lt(0, 1), fn(k, data, i, p) { index(data, i, p) })
    free(b, got)
}
fn reflexive(f: erased(fn(n: u64) -> Eq(n, n)), k: u64) -> Eq(k, k) { f(k) }
export fn evidence(n: u64) -> u64 { let p = reflexive(fn(k) { refl(k) }, n); n }
fn vanish(f: erased(fn(n: u64) -> Eq(n + 1, n + 1))) -> u64 { let p = f(18446744073709551615); 3 }
export fn erased_call() -> u64 { vanish(fn(n) { refl(n + 1) }) }
export fn nested(n: u64) -> u64 {
    let f: fn(k: u64) -> fn(erased(Eq(k, k))) -> u64 = fn(m) { fn(p) { m } }
    f(n)(refl(n))
}
export fn partial(x: i64) -> i64 {
    let f: fn(n: u64, i64) -> buffer(n) = fn(k, v) { alloc(k, v) }
    let g = f(1)
    free(g(x), 5)
}
export fn shadow(n: u64, x: i64) -> i64 {
    let f: fn(n: u64, m: u64) -> fn(i64) -> buffer(n + m) = fn(a, b) { fn(v) { alloc(a + b, v) } }
    free(f(1, 2)(x), 11)
}
export fn outer(n: u64, x: i64) -> i64 {
    let f: fn(u64, k: u64, _: i64) -> buffer(n + k) = fn(ignore, m, v) { alloc(n + m, v) }
    free(f(100, 2, x), 13)
}
export fn own_domain(n: u64, x: i64) -> i64 {
    let f: fn(n: buffer(n)) -> i64 = fn(b) { free(b, 17) }
    f(alloc(n, x))
}
export fn unused(n: u64) -> u64 {
    let f: fn(k: u64) -> buffer(k) = fn(m) { alloc(m, 1) }
    n
}
'''
REFERENCE = PREFIX + '''
export fn owned(n: u64, x: i64) -> i64 { free(alloc(n, x), 9) }
export fn produced(n: u64, x: i64) -> i64 { free(alloc(n, x), 7) }
export fn borrowed(x: i64) -> i64 { let b = alloc(1, x); let got = index(b, 0, decide_lt(0, 1)); free(b, got) }
export fn evidence(n: u64) -> u64 { n }
export fn erased_call() -> u64 { 3 }
export fn nested(n: u64) -> u64 { n }
export fn partial(x: i64) -> i64 { free(alloc(1, x), 5) }
export fn shadow(n: u64, x: i64) -> i64 { free(alloc(3, x), 11) }
export fn outer(n: u64, x: i64) -> i64 { free(alloc(n + 2, x), 13) }
export fn own_domain(n: u64, x: i64) -> i64 { free(alloc(n, x), 17) }
export fn unused(n: u64) -> u64 { n }
'''
INVALID = {
    'duplicate': ('fn bad(f: fn(n: u64, n: u64) -> u64) -> u64 { 0 }', 'duplicate function type parameter'),
    'reserved': ('fn bad(f: fn(buffer: u64) -> u64) -> u64 { 0 }', 'reserved dependent_core name'),
    'forward': ('fn bad(f: fn(buffer(n), n: u64) -> i64) -> u64 { 0 }', 'unknown name (or recursive/forward definition): n'),
    'self-domain': ('fn bad(f: fn(n: buffer(n)) -> i64) -> u64 { 0 }', 'unknown name (or recursive/forward definition): n'),
    'leaked-name': ('fn bad(f: fn(n: u64) -> u64, b: buffer(n)) -> u64 { 0 }', 'unknown name (or recursive/forward definition): n'),
    'wrong-index': ('fn bad() -> u64 { let f: fn(n: u64) -> buffer(n) = fn(k) { alloc(1, 0) }; 0 }', 'type mismatch'),
    'false-proof': ('fn bad(f: erased(fn(n: u64) -> Eq(n, 0))) -> Eq(1, 0) { f(1) } fn wrong() -> u64 { let f: fn(n: u64) -> Eq(n, 0) = fn(k) { refl(k) }; 0 }', 'type mismatch'),
    'runtime-erased': ('fn bad() -> u64 { let f: fn(n: erased(u64)) -> u64 = fn(k) { k }; 0 }', 'erased value used at runtime'),
    'proof-relevance': ('fn bad(f: fn(n: u64, Eq(n, n)) -> u64) -> u64 { 0 }', 'proof binders must be erased'),
    'inout': ('fn bad(f: fn(inout n: u64) -> u64) -> u64 { 0 }', 'function type parameters use plain types or erased(T)'),
    'owner-duplicate': ('fn bad() -> u64 { let f: fn(n: erased(u64), b: buffer(n)) -> i64 = fn(k, x) { free(x, free(x, 0)) }; 0 }', 'an owned value is used more than once'),
    'owned-capture': ('fn bad(b: buffer(1)) -> u64 { let f: fn(n: u64) -> i64 = fn(k) { free(b, 0) }; 0 }', 'a function cannot capture an owned value'),
    'annotation': ('fn bad() -> u64 { let f: fn(n: u64) -> buffer(n) = fn(k: i64) { alloc(1, 0) }; 0 }', 'lambda parameter annotation does not match its expected type'),
    'bound-not-type': ('fn bad(f: fn(n: u64, n) -> i64) -> u64 { 0 }', 'unsupported type in dependent_core'),
}
ANCHOR='\nexport fn positive_anchor() -> i64 { 0 }\n'


def validate_named_functions(compiler, root, temporary, environment, run):
    def command(action, path, *args, success=True, env=environment):
        return run([compiler,action,str(path),*args],success=success,env=env)
    (temporary/'named_helper.jh').write_text(HELPER)
    source=temporary/'named-functions.jh';source.write_text(PROGRAM)
    reference=temporary/'named-functions-reference.jh';reference.write_text(REFERENCE)
    command('check',source,'--lib',env={**environment,'JIHOO_LLVM':'/unavailable','JIHOO_CC':'/unavailable'})
    mir=command('emit-mir',source,'--lib').stdout
    assert mir==command('emit-mir',reference,'--lib').stdout,'dependent callback specialization changed MIR'
    formatted=temporary/'named-functions-formatted.jh';formatted.write_text(command('fmt',source).stdout)
    assert command('fmt',formatted).stdout==formatted.read_text()
    assert command('emit-mir',formatted,'--lib').stdout==mir
    syntax=lambda text: re.sub(r' \d+:\d+', '',text)
    assert syntax(command('emit-ast',source).stdout)==syntax(command('emit-ast',formatted).stdout)
    counter=temporary/'named-counter.c';counter.write_text(COUNTER)
    host='aarch64' if platform.machine() in ('aarch64','arm64') else 'x86_64'
    for target,machine in (('x86_64',62),('aarch64',183)):
        for level in ('-O0','-O2'):
            obj=temporary/f'named-{target}{level}.o'
            command('emit-obj',source,'--lib','--target',target,level,'-o',str(obj))
            assert struct.unpack_from('<H',obj.read_bytes(),18)[0]==machine
            if target!=host: continue
            library=temporary/f'named{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC','clang')),'-shared','-fPIC',str(obj),str(counter),'-Wl,--wrap=malloc','-Wl,--wrap=free','-o',str(library)])
            native=ctypes.CDLL(str(library))
            for name in ('owned','produced','shadow','outer','own_domain'):
                f=getattr(native,name);f.argtypes,f.restype=[ctypes.c_uint64,ctypes.c_int64],ctypes.c_int64
            for name in ('borrowed','partial'):
                f=getattr(native,name);f.argtypes,f.restype=[ctypes.c_int64],ctypes.c_int64
            for n in (0,1,9):
                for x in (-7,0,13):
                    assert native.owned(n,x)==9 and native.produced(n,x)==7
                    assert native.shadow(n,x)==11 and native.outer(n,x)==13 and native.own_domain(n,x)==17
                    assert native.borrowed(x)==x and native.partial(x)==5
            count=ctypes.c_long.in_dll(native,'allocations').value
            for name in ('evidence','nested','unused'):
                f=getattr(native,name);f.argtypes,f.restype=[ctypes.c_uint64],ctypes.c_uint64
                for n in (0,1,(1<<64)-1): assert f(n)==n
            native.erased_call.restype=ctypes.c_uint64
            assert native.erased_call()==3
            assert ctypes.c_long.in_dll(native,'allocations').value==count
            assert count==ctypes.c_long.in_dll(native,'frees').value
    for level in ('-O0','-O2'):
        assert command('run',root/'examples/core_named_functions.jh',level,success=False).returncode==17
    trap=temporary/'named-trap.jh'
    trap.write_text(PREFIX+'fn main() -> i64 { let f: fn(n: u64) -> fn(u64) -> u64 = fn(k) { fn(x) { k + x } }; let g = f(18446744073709551615 + 1); 0 }')
    for level in ('-O0','-O2'): assert command('run',trap,level,success=False).returncode==132
    flags=('--lib','--release','--no-verify','--error-format=json')
    env={**environment,'JIHOO_NO_ELAB':'1'}
    control=temporary/'named-control.jh';control.write_text(PREFIX+'fn good(f: fn(n: u64) -> buffer(n)) -> u64 { 0 }'+ANCHOR)
    obj=temporary/'named-control.o';command('emit-obj',control,*flags,'-o',str(obj),env=env)
    assert obj.read_bytes().startswith(b'\x7fELF')
    for name,(body,message) in INVALID.items():
        bad=temporary/f'named-{name}.jh';bad.write_text(PREFIX+body+ANCHOR)
        obj=temporary/f'named-{name}.o'
        for action,opts in (('check',()),('emit-obj',('-o',str(obj)))):
            r=command(action,bad,*flags,*opts,success=False,env=env)
            errors=[d for d in json.loads(r.stderr)['diagnostics'] if d['severity']=='error']
            assert r.returncode==1 and len(errors)==1,(name,r.stderr)
            assert errors[0]['kind']=='source' and errors[0]['message']=='core: '+message,(name,r.stderr)
        assert not obj.exists()
    legacy=temporary/'named-legacy.jh';legacy.write_text('fn bad(f: fn(n: u64) -> u64) -> u64 { 0 }\nfn main() -> i64 { 0 }')
    r=command('check',legacy,'--error-format=json',success=False)
    assert 'named function type parameters require dependent_core' in r.stderr
    print(f'named function types: exact MIR, alpha-renaming, nested scope, ownership, erasure, both targets and {len(INVALID)} intended rejections passed')
