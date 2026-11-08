"""Irrefutable record lets share dependent case typing and ownership with match."""
import ctypes
import json
import os
import platform
import re
import shlex
import struct
from core_buffer import COUNTER

LIBRARY='''#![dependent_core]
pub struct Secret(n: u64) { pub tag: i64, data: buffer(n) }
pub fn make(n: u64, x: i64) -> Secret(n) { Secret { tag: x, data: alloc(n, x) } }
'''
PREFIX='''#![dependent_core]
import binding_helper
import dependent.nat
struct Packet(n: u64) { len: u64, data: buffer(len), same: erased(Eq(len, n)) }
struct Pair { a: i64, b: i64 }
struct Nest(n: u64) { packet: Packet(n), extra: buffer(n) }
fn packet(n: u64, x: i64) -> Packet(n) { Packet { len: n, data: alloc(n, x), same: refl(n) } }
'''
BODIES={
'peek': ('''fn peek(p: ref Packet(1)) -> i64 {
    let Packet { len, data, same } = p;
    index(data, 0, transport(fn(k) { Lt(0, k) }, nat.eq_sym(len, 1, same), decide_lt(0, 1)))
}''', '''fn peek(p: ref Packet(1)) -> i64 { match p { Packet { len, data, same } => {
    index(data, 0, transport(fn(k) { Lt(0, k) }, nat.eq_sym(len, 1, same), decide_lt(0, 1)))
} } }'''),
'update': ('''fn update(inout p: Packet(1), x: i64) {
    let Packet { len, data, same } = p;
    store(&data, 0, x, transport(fn(k) { Lt(0, k) }, nat.eq_sym(len, 1, same), decide_lt(0, 1)))
    p = Packet { len, data, same }
}''', '''fn update(inout p: Packet(1), x: i64) { match p { Packet { len, data, same } => {
    store(&data, 0, x, transport(fn(k) { Lt(0, k) }, nat.eq_sym(len, 1, same), decide_lt(0, 1)))
    p = Packet { len, data, same }
} } }'''),
'owned': ('''export fn owned(n: u64, x: i64) -> i64 {
    let Packet { data: b, .. } = packet(n, x);
    free(b, 7)
}''', '''export fn owned(n: u64, x: i64) -> i64 { match packet(n, x) { Packet { data: b, .. } => { free(b, 7) } } }'''),
'borrowed': ('''export fn borrowed(x: i64) -> i64 {
    var p = packet(1, x)
    let first = peek(p)
    update(&p, x + 1)
    let second = peek(p)
    let Packet { data, .. } = p;
    free(data, first + second)
}''', '''export fn borrowed(x: i64) -> i64 {
    var p = packet(1, x)
    let first = peek(p)
    update(&p, x + 1)
    let second = peek(p)
    match p { Packet { data, .. } => { free(data, first + second) } }
}'''),
'partial': ('''export fn partial(n: u64, x: i64) -> i64 {
    let binding_helper.Secret { tag, .. } = binding_helper.make(n, x);
    tag
}''', '''export fn partial(n: u64, x: i64) -> i64 { match binding_helper.make(n, x) { binding_helper.Secret { tag, .. } => { tag } } }'''),
'context': ('''export fn context(n: u64, x: i64) -> i64 {
    let Packet { data, .. }: Packet(n) = Packet { len: n, data: alloc(n, x), same: refl(n) };
    free(data, 9)
}''', '''export fn context(n: u64, x: i64) -> i64 {
    let p: Packet(n) = Packet { len: n, data: alloc(n, x), same: refl(n) }
    match p { Packet { data, .. } => { free(data, 9) } }
}'''),
'nested': ('''export fn nested(n: u64, x: i64) -> i64 {
    let Nest { packet: Packet { data, .. }, extra }: Nest(n) = Nest { packet: packet(n, x), extra: alloc(n, x) };
    free(data, free(extra, 11))
}''', '''export fn nested(n: u64, x: i64) -> i64 {
    let outer: Nest(n) = Nest { packet: packet(n, x), extra: alloc(n, x) }
    match outer { Nest { packet: p, extra } => { match p { Packet { data, .. } => { free(data, free(extra, 11)) } } } }
}'''),
'shadow': ('''export fn shadow(x: i64) -> i64 {
    let Pair { b: x, a } = Pair { a: x + 1, b: x + 2 };
    let Pair { a: y, b: _ } = Pair { a: a + x, b: 0 };
    y
}''', '''export fn shadow(x: i64) -> i64 {
    match (Pair { a: x + 1, b: x + 2 }) { Pair { b: x, a } => {
        match (Pair { a: a + x, b: 0 }) { Pair { a: y, b: _ } => { y } }
    } }
}'''),
'discard': ('''export fn discard(n: u64, x: i64) -> i64 { let Packet { .. } = packet(n, x); 13 }''', '''export fn discard(n: u64, x: i64) -> i64 { match packet(n, x) { Packet { .. } => { 13 } } }'''),
}
BODIES['nested_borrow'] = ('''fn nested_peek(p: ref Nest(1)) -> i64 {
    let Nest { packet: Packet { len, data, same }, .. } = p;
    index(data, 0, transport(fn(k) { Lt(0, k) }, nat.eq_sym(len, 1, same), decide_lt(0, 1)))
}
export fn nested_borrow(x: i64) -> i64 {
    let p: Nest(1) = Nest { packet: packet(1, x), extra: alloc(1, x) }
    nested_peek(p) + nested_peek(p)
}''', '''fn nested_peek(p: ref Nest(1)) -> i64 {
    match p { Nest { packet: inner, .. } => {
        match inner { Packet { len, data, same } => {
            index(data, 0, transport(fn(k) { Lt(0, k) }, nat.eq_sym(len, 1, same), decide_lt(0, 1)))
        } }
    } }
}
export fn nested_borrow(x: i64) -> i64 {
    let p: Nest(1) = Nest { packet: packet(1, x), extra: alloc(1, x) }
    nested_peek(p) + nested_peek(p)
}''')
BODIES['deep'] = ('''struct Deep { left: Pair, right: Pair }
struct Deeper { inner: Deep }
export fn deep(x: i64) -> i64 {
    let p = Deeper { inner: Deep { left: Pair { a: x, b: 1 }, right: Pair { a: 2, b: 3 } } }
    let Deeper { inner: Deep { right: Pair { b: z, a: y }, left: Pair { b: _, a: x } } } = p;
    x + y + z
}''', '''struct Deep { left: Pair, right: Pair }
struct Deeper { inner: Deep }
export fn deep(x: i64) -> i64 {
    let p = Deeper { inner: Deep { left: Pair { a: x, b: 1 }, right: Pair { a: 2, b: 3 } } }
    match p { Deeper { inner } => { match inner { Deep { right, left } => {
        match right { Pair { b: z, a: y } => { match left { Pair { b: _, a: x } => { x + y + z } } } }
    } } } }
}''')
BODIES['nested_update'] = ('''fn nested_update(inout p: Nest(1), x: i64) {
    let Nest { packet: Packet { len, data, same }, extra } = p;
    store(&data, 0, x, transport(fn(k) { Lt(0, k) }, nat.eq_sym(len, 1, same), decide_lt(0, 1)))
    p = Nest { packet: Packet { len, data, same }, extra }
}
export fn nested_mutate(x: i64) -> i64 {
    var p: Nest(1) = Nest { packet: packet(1, x), extra: alloc(1, x) }
    nested_update(&p, x + 1)
    nested_peek(p)
}''', '''fn nested_update(inout p: Nest(1), x: i64) {
    match p { Nest { packet: inner, extra } => { match inner { Packet { len, data, same } => {
        store(&data, 0, x, transport(fn(k) { Lt(0, k) }, nat.eq_sym(len, 1, same), decide_lt(0, 1)))
        p = Nest { packet: Packet { len, data, same }, extra }
    } } } }
}
export fn nested_mutate(x: i64) -> i64 {
    var p: Nest(1) = Nest { packet: packet(1, x), extra: alloc(1, x) }
    nested_update(&p, x + 1)
    nested_peek(p)
}''')
PROGRAM=PREFIX+'\n'.join(a for a,b in BODIES.values())
REFERENCE=PREFIX+'\n'.join(b for a,b in BODIES.values())
INVALID={
    'bad-annotation-evidence': ('fn bad(p: Packet(1)) -> i64 { let Packet { .. }: Packet(sub(2, 1, decide_lt(0, 1))) = p; 0 }', 'type mismatch'),
    'discarded-wrong-index': ('fn bad(p: Packet(1)) -> i64 { let Packet { .. }: Packet(2) = p; 0 }', 'type mismatch'),
    'borrow-escape': ('fn bad(p: Packet(1)) -> i64 { let view = { let Packet { data, .. }: ref Packet(1) = p; data }; 0 }', 'a field-dependent match result needs an expected type'),
    'let-else': ('fn bad(p: Pair) -> i64 { let Pair { a, b } = p else { 0 }; a }', 'dependent_core has plain let statements'),
    'var': ('fn bad() -> i64 { var Pair { a, b } = Pair { a: 1, b: 2 }; a }','struct destructuring uses let'),
    'duplicate-name': ('fn bad() -> i64 { let Pair { a: x, b: x } = Pair { a: 1, b: 2 }; x }','duplicate struct binding name'),
    'duplicate-field': ('fn bad() -> i64 { let Pair { a, a: x, .. } = Pair { a: 1, b: 2 }; x }','duplicate struct pattern field'),
    'unknown-field': ('fn bad() -> i64 { let Pair { c, .. } = Pair { a: 1, b: 2 }; c }','unknown struct pattern field'),
    'missing-field': ('fn bad() -> i64 { let Pair { a } = Pair { a: 1, b: 2 }; a }','missing field: b'),
    'private': ('fn bad(s: binding_helper.Secret(1)) -> i64 { let binding_helper.Secret { data, .. } = s; free(data, 0) }','private struct field: data'),
    'wrong-family': ('struct Other { a: i64, b: i64 } fn bad() -> i64 { let Other { a, b } = Pair { a: 1, b: 2 }; a }','match has no arm for Pair'),
    'wrong-index': ('fn bad(p: Packet(1)) -> i64 { let Packet { data, .. }: Packet(2) = p; free(data, 0) }','type mismatch'),
    'consume-borrow': ('fn bad(p: ref Packet(1)) -> i64 { let Packet { data, .. } = p; free(data, 0) }','expected a buffer'),
    'double-use': ('fn bad(p: Packet(1)) -> i64 { let Packet { data, .. } = p; let Packet { data: other, .. } = p; free(data, free(other, 0)) }','an owned value is used more than once'),
    'field-double-use': ('fn bad(p: Packet(1)) -> i64 { let Packet { data, .. } = p; free(data, free(data, 0)) }','an owned value is used more than once'),
    'nested-duplicate': ('fn bad(p: Nest(1)) -> i64 { let Nest { packet: Packet { data: x, .. }, extra: x } = p; 0 }','duplicate struct binding name'),
    'nested-borrow': ('fn bad(p: ref Nest(1)) -> i64 { let Nest { packet: Packet { data, .. }, .. } = p; free(data, 0) }','expected a buffer'),
    'nested-reuse': ('fn bad(p: Nest(1)) -> i64 { let Nest { packet: Packet { data, .. }, .. } = p; free(data, free(data, 0)) }','an owned value is used more than once'),
    'nested-wrong-family': ('fn bad(p: Nest(1)) -> i64 { let Nest { packet: Pair { a, b }, .. } = p; a }','match has no arm for Packet'),
    'nested-missing': ('fn bad(p: Nest(1)) -> i64 { let Nest { packet: Packet { data }, .. } = p; 0 }','missing field: len'),
    'nested-private': ('struct Wrapped { inner: binding_helper.Secret(1) } fn bad(p: Wrapped) -> i64 { let Wrapped { inner: binding_helper.Secret { data, .. } } = p; 0 }','private struct field: data'),
    'nested-refutable': ('struct Wrapped { inner: Pair } fn bad(p: Wrapped) -> i64 { let Wrapped { inner: Pair { a: 1, b } } = p; b }','variant fields bind names or _'),
    'refutable': ('enum Maybe { None; Some(i64) } fn bad(x: Maybe) -> i64 { let Maybe.Some(y) = x; y }','a let binds a name'),
    'scalar': ('fn bad() -> i64 { let Pair { a, b } = 1; a }','match requires a value of a data type'),
}
INVALID['nesting-limit']=('fn bad() -> i64 { '+('let Pair { .. } = Pair { a: 0, b: 0 }; '*140)+'0 }', 'elaboration nesting limit reached')
ANCHOR='\nexport fn positive_anchor() -> i64 { 0 }\n'


def validate_bindings(compiler,root,temporary,environment,run):
    def command(action,path,*args,success=True,env=environment):
        return run([compiler,action,str(path),*args],success=success,env=env)
    (temporary/'binding_helper.jh').write_text(LIBRARY)
    source=temporary/'bindings.jh';source.write_text(PROGRAM)
    reference=temporary/'bindings-match.jh';reference.write_text(REFERENCE)
    command('check',source,'--lib',env={**environment,'JIHOO_LLVM':'/unavailable','JIHOO_CC':'/unavailable'})
    mir=command('emit-mir',source,'--lib').stdout
    reference_mir=command('emit-mir',reference,'--lib').stdout
    functions=lambda text: dict(zip(re.findall(r'^fn (\S+)',text,re.M),re.split(r'^fn \S+',text,flags=re.M)[1:]))
    actual,expected=functions(mir),functions(reference_mir)
    # Direct contextual literals can fuse a constructor/case, whereas the
    # explicit-match reference needs an intermediate annotated owner.
    for name in actual.keys()-{'context','nested'}:
        assert actual[name]==expected[name],('record let changed match MIR',name)
    formatted=temporary/'bindings-formatted.jh';formatted.write_text(command('fmt',source).stdout)
    assert command('fmt',formatted).stdout==formatted.read_text()
    assert command('emit-mir',formatted,'--lib').stdout==mir
    syntax=lambda text:re.sub(r' \d+:\d+','',text)
    assert syntax(command('emit-ast',source).stdout)==syntax(command('emit-ast',formatted).stdout)
    counter=temporary/'bindings-counter.c';counter.write_text(COUNTER)
    host='aarch64' if platform.machine() in ('aarch64','arm64') else 'x86_64'
    for variant,program in (('let',source),('match',reference)):
        for target,machine in (('x86_64',62),('aarch64',183)):
            for level in ('-O0','-O2'):
                obj=temporary/f'bindings-{variant}-{target}{level}.o';command('emit-obj',program,'--lib','--target',target,level,'-o',str(obj))
                assert struct.unpack_from('<H',obj.read_bytes(),18)[0]==machine
                if target!=host:continue
                library=temporary/f'bindings-{variant}{level}.so'
                run([*shlex.split(os.environ.get('JIHOO_CC','clang')),'-shared','-fPIC',str(obj),str(counter),'-Wl,--wrap=malloc','-Wl,--wrap=free','-o',str(library)])
                native=ctypes.CDLL(str(library))
                for name in ('owned','partial','context','nested','discard'):
                    f=getattr(native,name);f.argtypes,f.restype=[ctypes.c_uint64,ctypes.c_int64],ctypes.c_int64
                for name in ('borrowed','shadow','nested_borrow','deep','nested_mutate'):
                    f=getattr(native,name);f.argtypes,f.restype=[ctypes.c_int64],ctypes.c_int64
                for n in (0,1,9):
                    for x in (-7,0,13):
                        before=ctypes.c_long.in_dll(native,'allocations').value
                        assert native.owned(n,x)==7
                        if level=='-O0':assert ctypes.c_long.in_dll(native,'allocations').value==before+1,'initializer was not evaluated exactly once'
                        assert native.partial(n,x)==x and native.context(n,x)==9
                        assert native.nested(n,x)==11 and native.discard(n,x)==13
                        assert native.borrowed(x)==2*x+1 and native.shadow(x)==2*x+3
                        assert native.nested_borrow(x)==2*x and native.deep(x)==x+5
                        assert native.nested_mutate(x)==x+1
                assert ctypes.c_long.in_dll(native,'allocations').value==ctypes.c_long.in_dll(native,'frees').value
    trap=temporary/'binding-trap.jh';trap.write_text(PREFIX+'struct Wrapped { inner: Pair } fn main() -> i64 { let Wrapped { inner: Pair { .. } } = Wrapped { inner: Pair { a: 9223372036854775807 + 1, b: 0 } }; 0 }')
    for level in ('-O0','-O2'):assert command('run',trap,level,success=False).returncode==132
    for level in ('-O0','-O2'):
        assert command('run',root/'examples/core_record_bindings.jh',level,success=False).returncode==17
    flags=('--lib','--release','--no-verify','--error-format=json');env={**environment,'JIHOO_NO_ELAB':'1'}
    control=temporary/'binding-control.jh';control.write_text(PREFIX+'fn good() -> i64 { let Pair { a, b } = Pair { a: 1, b: 2 }; a + b }'+ANCHOR)
    obj=temporary/'binding-control.o';command('emit-obj',control,*flags,'-o',str(obj),env=env);assert obj.read_bytes().startswith(b'\x7fELF')
    for name,(body,message) in INVALID.items():
        bad=temporary/f'binding-{name}.jh';bad.write_text(PREFIX+body+ANCHOR);obj=temporary/f'binding-{name}.o'
        for action,opts in (('check',()),('emit-obj',('-o',str(obj)))):
            r=command(action,bad,*flags,*opts,success=False,env=env)
            errors=[d for d in json.loads(r.stderr)['diagnostics'] if d['severity']=='error']
            assert r.returncode==1 and len(errors)==1,(name,r.stderr)
            assert errors[0]['kind']=='source' and errors[0]['message']=='core: '+message,(name,r.stderr)
        assert not obj.exists()
    print(f'record bindings: direct-match MIR and contextual execution equivalence, dependent fields, borrowed/owned updates, both targets, traps and {len(INVALID)} exact rejections passed')
