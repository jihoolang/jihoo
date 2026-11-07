"""Parameterized records: erased indices, dependent fields and owned/borrowed cases."""
import ctypes
import json
import os
import platform
import re
import shlex
import struct
from core_buffer import COUNTER

LIBRARY = '''#![dependent_core]
pub struct Sized(n: u64) { pub data: buffer(n) }
pub fn make(n: u64, x: i64) -> Sized(n) { Sized { data: alloc(n, x) } }
pub fn read(n: erased(u64), s: ref Sized(n), p: erased(Lt(0, n))) -> i64 {
    match s { Sized { data } => index(data, 0, p) }
}
pub fn consume(n: erased(u64), s: Sized(n)) -> i64 {
    match s { Sized { data } => free(data, 7) }
}
pub fn set(n: erased(u64), inout s: Sized(n), x: i64, p: erased(Lt(0, n))) {
    match s { Sized { data } => { store(&data, 0, x, p); s = Sized { data } } }
}
pub struct Secret(n: u64) { pub tag: i64, data: buffer(n) }
pub fn secret(n: u64, x: i64) -> Secret(n) { Secret { tag: x, data: alloc(n, x) } }
pub fn inspect(n: erased(u64), s: ref Secret(n)) -> i64 { match s { Secret { tag, .. } => tag } }
'''
PREFIX = '#![dependent_core]\nimport struct_helper\nimport dependent.nat\n'
PROGRAM = PREFIX + '''
struct Pair(n: u64, m: u64) {
    len: u64,
    data: buffer(len),
    fixed: buffer(n),
    same: erased(Eq(len, m))
}
struct Empty(n: u64) {}
struct Outer(n: u64) { inner: struct_helper.Sized(n) }
fn pair(n: u64, m: u64, x: i64) -> Pair(n, m) {
    Pair { same: refl(m), fixed: alloc(n, x), len: m, data: alloc(m, x) }
}
fn sum(n: erased(u64), m: erased(u64), p: ref Pair(n, m), positive: erased(Lt(0, m))) -> i64 {
    match p { Pair { len, data, same, .. } => index(data, 0, transport(fn(k) { Lt(0, k) }, nat.eq_sym(len, m, same), positive)) }
}
fn maybe_sum(n: erased(u64), m: u64, p: ref Pair(n, m)) -> i64 { if_lt(0, m, fn(e) { sum(n, m, p, e) }, 0) }
export fn dependent(n: u64, m: u64, x: i64) -> i64 {
    let p = pair(n, m, x)
    let got = maybe_sum(n, m, p)
    match p { Pair { data, fixed, .. } => free(data, free(fixed, got)) }
}
export fn updated(x: i64) -> i64 {
    var s = struct_helper.make(1, x)
    let first = struct_helper.read(1, s, decide_lt(0, 1))
    struct_helper.set(1, &s, x + 2, decide_lt(0, 1))
    let second = struct_helper.read(1, s, decide_lt(0, 1))
    first + second + struct_helper.consume(1, s)
}
export fn nested(n: u64, x: i64) -> i64 {
    let s: Outer(n) = Outer { inner: struct_helper.Sized { data: alloc(n, x) } }
    match s { Outer { inner } => struct_helper.consume(n, inner) }
}
export fn partial(n: u64, x: i64) -> i64 {
    let s = struct_helper.secret(n, x)
    let first = struct_helper.inspect(n, s)
    match s { struct_helper.Secret { tag, .. } => first + tag }
}
fn empty(n: erased(u64)) -> u64 {
    let s: Empty(n) = Empty {}
    match s { Empty {} => 11 }
}
export fn erased_index() -> u64 { empty(18446744073709551615 + 1) }
export fn shadow(n: u64) -> u64 { let n = n + 1; let s: Empty(n) = Empty {}; match s { Empty {} => n } }
'''
ANCHOR = '\nexport fn positive_anchor() -> i64 { 0 }\n'
INVALID = {
    'missing-index': ('fn bad(s: struct_helper.Sized) -> i64 { 0 }', 'wrong number of family indices'),
    'extra-index': ('fn bad(s: struct_helper.Sized(1, 2)) -> i64 { 0 }', 'wrong number of family indices'),
    'index-type': ('fn bad(x: i64, s: struct_helper.Sized(x)) -> i64 { 0 }', 'type mismatch'),
    'wrong-family': ('struct Other(n: u64) { data: buffer(n) } fn bad() -> Other(1) { struct_helper.Sized { data: alloc(1, 0) } }', 'a value of another type was expected'),
    'missing-field': ('fn bad() -> struct_helper.Sized(1) { struct_helper.Sized {} }', 'a struct value gives every field'),
    'change-index': ('fn bad(inout s: struct_helper.Sized(1)) { s = struct_helper.make(2, 0) }', 'the result after giving back takes the owner'),
    'nonuniform-recursion': ('struct Bad(n: u64) { next: Bad(n + 1) }', "a recursive field has its type's parameters"),
    'parameter-type': ('struct Bad(n: i64) { x: i64 }', 'data types are parameterized by u64 values'),
    'parameter-mode': ('struct Bad(inout n: u64) { x: i64 }', 'generic parameters cannot use inout or sink'),
    'parameter-sink': ('struct Bad(sink n: u64) { x: i64 }', 'generic parameters cannot use inout or sink'),
    'variadic': ('struct Bad(n: u64, ...) { x: i64 }', 'generic parameters cannot be variadic'),
    'duplicate-parameter': ('struct Bad(n: u64, n: u64) { x: i64 }', 'duplicate parameter'),
    'field-shadow': ('struct Bad(n: u64) { n: u64 }', 'duplicate field'),
    'duplicate-field': ('struct Bad(n: u64) { x: u64, x: u64 }', 'duplicate field'),
    'unbound-field': ('struct Bad(n: u64) { data: buffer(m), m: u64 }', 'unknown name (or recursive/forward definition): m'),
    'missing-context': ('fn bad() -> i64 { let s = struct_helper.Sized { data: alloc(1, 0) }; 0 }', 'a value of a parameterized type needs its expected type'),
    'wrong-index': ('fn bad(n: u64) -> struct_helper.Sized(n) { struct_helper.Sized { data: alloc(1, 0) } }', 'type mismatch'),
    'false-field': ('struct Bad(n: u64) { p: erased(Eq(n, 0)) } fn bad() -> Bad(1) { Bad { p: refl(1) } }', 'type mismatch'),
    'false-later-field': ('struct Bad(n: u64) { m: u64, p: erased(Eq(n, m)) } fn bad() -> Bad(1) { Bad { m: 2, p: refl(1) } }', 'type mismatch'),
    'private-construction': ('fn bad() -> struct_helper.Secret(1) { struct_helper.Secret { tag: 0, data: alloc(1, 0) } }', 'private struct field: data'),
    'private-pattern': ('fn bad(s: struct_helper.Secret(1)) -> i64 { match s { struct_helper.Secret { data, .. } => free(data, 0) } }', 'private struct field: data'),
    'duplicate-owner': ('fn bad(s: struct_helper.Sized(1)) -> i64 { struct_helper.consume(1, s) + struct_helper.consume(1, s) }', 'an owned value is used more than once'),
    'consume-borrow': ('fn bad(s: ref struct_helper.Sized(1)) -> i64 { match s { struct_helper.Sized { data } => free(data, 0) } }', 'expected a buffer'),
    'erased-runtime': ('struct Bad(n: u64) { x: i64 } fn bad(n: erased(u64)) -> u64 { let s: Bad(n) = Bad { x: 0 }; match s { Bad { x } => n } }', 'erased value used at runtime'),
}


def validate_structs(compiler, root, temporary, environment, run):
    def command(action, path, *args, success=True, env=environment):
        return run([compiler, action, str(path), *args], success=success, env=env)
    (temporary/'struct_helper.jh').write_text(LIBRARY)
    source = temporary/'parameterized-structs.jh'; source.write_text(PROGRAM)
    command('check',source,'--lib',env={**environment,'JIHOO_LLVM':'/unavailable','JIHOO_CC':'/unavailable'})
    mir=command('emit-mir',source,'--lib').stdout
    formatted=temporary/'structs-formatted.jh'; formatted.write_text(command('fmt',source).stdout)
    assert command('fmt',formatted).stdout==formatted.read_text()
    assert command('emit-mir',formatted,'--lib').stdout==mir
    counter=temporary/'structs-counter.c'; counter.write_text(COUNTER)
    host='aarch64' if platform.machine() in ('aarch64','arm64') else 'x86_64'
    for target,machine in (('x86_64',62),('aarch64',183)):
        for level in ('-O0','-O2'):
            obj=temporary/f'structs-{target}{level}.o'
            command('emit-obj',source,'--lib','--target',target,level,'-o',str(obj))
            assert struct.unpack_from('<H',obj.read_bytes(),18)[0]==machine
            if target!=host: continue
            library=temporary/f'structs{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC','clang')),'-shared','-fPIC',str(obj),str(counter),'-Wl,--wrap=malloc','-Wl,--wrap=free','-o',str(library)])
            native=ctypes.CDLL(str(library))
            native.dependent.argtypes,native.dependent.restype=[ctypes.c_uint64,ctypes.c_uint64,ctypes.c_int64],ctypes.c_int64
            native.updated.argtypes,native.updated.restype=[ctypes.c_int64],ctypes.c_int64
            for name in ('nested','partial'):
                f=getattr(native,name); f.argtypes,f.restype=[ctypes.c_uint64,ctypes.c_int64],ctypes.c_int64
            for n in (0,1,5):
                for m in (0,1,7):
                    for x in (-4,0,13): assert native.dependent(n,m,x)==(x if m else 0)
                for x in (-4,0,13):
                    assert native.nested(n,x)==7 and native.partial(n,x)==2*x
            for x in (-4,0,13): assert native.updated(x)==2*x+9
            before=ctypes.c_long.in_dll(native,'allocations').value
            native.erased_index.restype=ctypes.c_uint64
            native.shadow.argtypes,native.shadow.restype=[ctypes.c_uint64],ctypes.c_uint64
            assert native.erased_index()==11 and native.shadow(41)==42
            assert ctypes.c_long.in_dll(native,'allocations').value==before
            assert ctypes.c_long.in_dll(native,'allocations').value==ctypes.c_long.in_dll(native,'frees').value
    snippets=re.findall(r'```jihoo\n(.*?)```', (root/'docs/language/dependent-records.md').read_text(), re.S)
    assert len(snippets)==1
    documented=temporary/'structs-documented.jh'; documented.write_text(snippets[0])
    for path in (documented, root/'examples/core_sized_record.jh'):
        for level in ('-O0','-O2'): assert command('run',path,level,success=False).returncode==17
    flags=('--lib','--release','--no-verify','--error-format=json')
    env={**environment,'JIHOO_NO_ELAB':'1'}
    control=temporary/'structs-control.jh'; control.write_text(PREFIX+'fn good() -> struct_helper.Sized(1) { struct_helper.Sized { data: alloc(1, 0) } }'+ANCHOR)
    obj=temporary/'structs-control.o'; command('emit-obj',control,*flags,'-o',str(obj),env=env)
    assert obj.read_bytes().startswith(b'\x7fELF')
    for name,(body,diagnostic) in INVALID.items():
        bad=temporary/f'structs-{name}.jh'; bad.write_text(PREFIX+body+ANCHOR)
        obj=temporary/f'structs-{name}.o'
        for action,opts in (('check',()),('emit-obj',('-o',str(obj)))):
            r=command(action,bad,*flags,*opts,success=False,env=env)
            errors=[d for d in json.loads(r.stderr)['diagnostics'] if d['severity']=='error']
            assert r.returncode==1 and len(errors)==1,(name,action,r.stderr)
            assert errors[0]['kind']=='source' and errors[0]['message']==(('' if name in ('parameter-mode','parameter-sink','variadic') else 'core: ')+diagnostic),(name,action,r.stderr)
        assert not obj.exists(),name
    print(f'parameterized structs: dependent fields, borrowed/owned matches, updates, privacy, both targets and {len(INVALID)} intended rejections passed')
