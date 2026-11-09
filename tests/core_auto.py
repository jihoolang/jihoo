"""Bounded proof synthesis emits checked, erased ordinary core terms."""
import ctypes
import json
import os
import platform
import re
import shlex
import struct

PREFIX='#![dependent_core]\nimport dependent.nat\n'
PROGRAM=PREFIX+'''
fn sum_equal(a: u64,b: u64) -> Eq(a+b,b+a) { auto() }
fn natural_bound(a: u64,k: u64) -> Lt(a,a+k+1) { auto() }
fn wide_bound() -> Lt(18446744073709551615,18446744073709551615+1) { auto() }
fn compose(a: u64, b: u64, c: u64, p: erased(Eq(a,b)), q: erased(Eq(b,c))) -> Eq(a,c) { auto() }
fn symmetric(a: u64, b: u64, p: erased(Eq(a,b))) -> Eq(b,a) { auto() }
fn shifted(a: u64, b: u64, k: u64, p: erased(Lt(a,b))) -> Lt(a+k,b+k) { auto() }
fn cancelled(a: u64, b: u64, k: u64, p: erased(Lt(a+k,b+k))) -> Lt(a,b) { auto() }
fn rewritten(a: u64, b: u64, n: u64, e: erased(Eq(a,b)), p: erased(Lt(a,n))) -> Lt(b,n) { auto() }
fn trans(a: u64, b: u64, c: u64, p: erased(Lt(a,b+1)), q: erased(Lt(b,c))) -> Lt(a,c) { auto() }
fn via_library(a: u64, b: u64, n: u64, p: erased(nat.Steps(a,b)), q: erased(Lt(b,n))) -> Lt(a,n) {
    auto(nat.steps_bound(a,b,p), q)
}
fn bound(i: u64, n: u64, b: ref buffer(n+1), p: erased(Lt(i,n))) -> i64 { index(b,i,auto()) }
fn imported_read(a: u64,b: u64,n: erased(u64),xs: ref buffer(n),p: erased(nat.Steps(a,b)),q: erased(Lt(b,n))) -> i64 {
    index(xs,a,auto(nat.steps_bound(a,b,p)))
}
export fn loop_read(n: u64,x: i64) -> i64 {
    let xs=alloc(n+1,x)
    let got=imported_read(0,n,n+1,xs,nat.advance(0,n),auto())
    free(xs,got)
}
export fn read(x: i64) -> i64 {
    var b = alloc(2,x)
    store(&b,0,x+1,auto())
    let got = bound(0,1,b,auto())
    free(b,got)
}
export fn array_read(x: i64) -> i64 { index([x,x+1], 1, auto()) }
export fn subtraction(n: u64) -> u64 { sub(n,0,auto()) }
fn certificate(n: erased(u64), p: erased(Eq(n,n))) -> i64 { 19 }
export fn ghost() -> i64 { certificate(18446744073709551615+1,auto()) }
export fn refinement() -> u64 { let p: refine(fn(i){Lt(i,4)}) = pack(2,auto()); witness(p) }
export fn loaded(x: i64) -> i64 { load(alloc(1,x),0,auto(),fn(v,b){free(b,v)}) }
'''
REFERENCE=PROGRAM.replace('-> Eq(a+b,b+a) { auto() }','-> Eq(a+b,b+a) { refl(a+b) }').replace('-> Lt(a,a+k+1) { auto() }','-> Lt(a,a+k+1) { nat.add_le(a,k) }').replace('-> Lt(18446744073709551615,18446744073709551615+1) { auto() }','-> Lt(18446744073709551615,18446744073709551615+1) { nat.le_refl(18446744073709551615) }').replace('index(xs,a,auto(nat.steps_bound(a,b,p)))','index(xs,a,nat.le_lt(a,b,n,nat.steps_bound(a,b,p),q))').replace('nat.advance(0,n),auto())','nat.advance(0,n),nat.le_refl(n))').replace('index(b,i,auto())','index(b,i,nat.weaken(i,n,p))').replace('store(&b,0,x+1,auto())','store(&b,0,x+1,decide_lt(0,2))').replace('bound(0,1,b,auto())','bound(0,1,b,decide_lt(0,1))').replace('index([x,x+1], 1, auto())','index([x,x+1], 1, decide_lt(1,2))').replace('sub(n,0,auto())','sub(n,0,zero_le(n))').replace('certificate(18446744073709551615+1,auto())','certificate(18446744073709551615+1,refl(18446744073709551615+1))').replace('pack(2,auto())','pack(2,decide_lt(2,4))').replace('load(alloc(1,x),0,auto(),','load(alloc(1,x),0,decide_lt(0,1),')
REFERENCE=REFERENCE.replace('-> Eq(a,c) { auto() }','-> Eq(a,c) { nat.eq_trans(a,b,c,p,q) }').replace('-> Eq(b,a) { auto() }','-> Eq(b,a) { nat.eq_sym(a,b,p) }').replace('-> Lt(a+k,b+k) { auto() }','-> Lt(a+k,b+k) { lt_add(a,b,k,p) }').replace('-> Lt(a,b) { auto() }','-> Lt(a,b) { lt_cancel(a,b,k,p) }').replace('-> Lt(b,n) { auto() }','-> Lt(b,n) { nat.rewrite_lower(a,b,n,e,p) }').replace('-> Lt(a,c) { auto() }','-> Lt(a,c) { nat.le_lt(a,b,c,p,q) }').replace('auto(nat.steps_bound(a,b,p), q)','nat.steps_lt(a,b,n,p,q)')
assert 'auto(' not in REFERENCE
INVALID={
 'unsupported-goal':('fn bad() -> nat.Steps(0,0) {auto()}','auto needs an expected Eq or Lt proposition'),
 'unsupported-hint':('fn bad() -> Eq(0,0) {auto(nat.stationary(0))}','auto hints must prove Eq or Lt'),
 'false-equality':('fn bad() -> Eq(0,1) { auto() }','auto could not synthesize the expected proof'),
 'false-bound':('fn bad() -> Lt(1,0) { auto() }','auto could not synthesize the expected proof'),
 'unknown-goal':('fn bad() -> i64 { let p = auto(); 0 }','auto needs an expected Eq or Lt proposition'),
 'runtime-goal':('fn bad() -> u64 { auto() }','auto needs an expected Eq or Lt proposition'),
 'hint-not-proof':('fn bad() -> Eq(0,0) { auto(7) }','auto hints must prove Eq or Lt'),
 'hint-forgery':('fn bad() -> Eq(0,0) { auto(lt_add(0,1,0,refl(0))) }','type mismatch'),
 'bad-goal':('fn bad() -> Eq(sub(2,1,decide_lt(0,1)),1) { auto() }','type mismatch'),
 'discarded-fact':('fn bad(i: u64,n: u64,_: erased(Lt(i,n))) -> Lt(i,n) { auto() }','auto could not synthesize the expected proof'),
 'shadowed-fact':('fn bad(i: u64,n: u64,p: erased(Lt(i,n))) -> Lt(i,n) { let p=7; auto() }','auto could not synthesize the expected proof'),
 'too-many-hints':('fn bad() -> Eq(0,0) { auto('+','.join(['refl(0)']*9)+') }','auto accepts at most 8 explicit hints'),
 'forward-constructor-name':('fn before() -> Eq(0,0) {auto()} trait P { fn auto() -> P }','unknown name (or recursive/forward definition): auto'),
 'recursive-auto-name':('fn auto() -> Eq(0,0) { auto() }','unknown name (or recursive/forward definition): auto'),
 'forward-auto-name':('fn bad() -> Eq(0,0) { auto() } fn auto() -> Eq(0,0) {refl(0)}','unknown name (or recursive/forward definition): auto'),
 'search-depth':('fn bad(a: u64,b: u64,z: u64,p: erased(Eq(a,b))) -> Lt(a,z) {auto()}','auto search limit reached'),
 'fact-limit':('fn bad('+','.join(f'p{i}: erased(Eq(0,0))' for i in range(33))+') -> Eq(0,0) {auto()}','auto accepts at most 32 facts'),
 'wrong-array-bound':('fn bad() -> i64 { index([1],1,auto()) }','auto could not synthesize the expected proof'),
}


def validate_auto(compiler,root,temporary,environment,run):
    def command(action,path,*args,success=True,env=environment):
        return run([compiler,action,str(path),*args],success=success,env=env)
    source=temporary/'auto.jh';source.write_text(PROGRAM)
    reference=temporary/'auto-reference.jh';reference.write_text(REFERENCE)
    command('check',source,'--lib')
    snippets=re.findall(r'```jihoo\n(.*?)```',(root/'docs/language/proof-automation.md').read_text(),re.S)
    documented=temporary/'auto-documented.jh';documented.write_text('\n'.join(snippets)+'\nexport fn documented_anchor() -> i64 {0}\n')
    command('check',documented,'--lib')
    command('check',root/'examples/core_auto.jh')
    for level in ('-O0','-O2'): assert command('run',root/'examples/core_auto.jh',level,success=False).returncode==17
    assert command('emit-mir',source,'--lib').stdout==command('emit-mir',reference,'--lib').stdout
    host='aarch64' if platform.machine() in ('aarch64','arm64') else 'x86_64'
    for target,machine in (('x86_64',62),('aarch64',183)):
        for level in ('-O0','-O2'):
            obj=temporary/f'auto-{target}{level}.o';command('emit-obj',source,'--lib','--target',target,level,'-o',str(obj))
            assert struct.unpack_from('<H',obj.read_bytes(),18)[0]==machine
            if target!=host:continue
            lib=temporary/f'auto{level}.so';run([*shlex.split(os.environ.get('JIHOO_CC','clang')),'-shared',str(obj),'-o',str(lib)])
            native=ctypes.CDLL(str(lib))
            for name in ('read','array_read','loaded'):
                f=getattr(native,name);f.argtypes,f.restype=[ctypes.c_int64],ctypes.c_int64
            native.loop_read.argtypes,native.loop_read.restype=[ctypes.c_uint64,ctypes.c_int64],ctypes.c_int64
            for n in (0,1,7):assert native.loop_read(n,31)==31
            native.subtraction.argtypes,native.subtraction.restype=[ctypes.c_uint64],ctypes.c_uint64
            for x in (-17,0,19):assert native.read(x)==x+1 and native.array_read(x)==x+1 and native.loaded(x)==x
            for n in (0,1,17,(1<<64)-1):assert native.subtraction(n)==n
            assert native.ghost()==19 and native.refinement()==2
    for name,body in {
      'global':'fn auto(x: i64) -> i64 { x+1 } fn main() -> i64 { auto(6) }',
      'local':'fn main() -> i64 { let auto=fn(x: i64) -> i64 {x+1}; auto(6) }',
    }.items():
        path=temporary/f'auto-compat-{name}.jh';path.write_text(PREFIX+body)
        assert command('run',path,success=False).returncode==7
    flags=('--lib','--release','--no-verify','--error-format=json');env={**environment,'JIHOO_NO_ELAB':'1'}
    control=temporary/'auto-control.o';command('emit-obj',source,*flags,'-o',str(control),env=env)
    assert control.read_bytes().startswith(b'\x7fELF')
    for name,(body,message) in INVALID.items():
        path=temporary/f'auto-invalid-{name}.jh';path.write_text(PREFIX+body+'\nexport fn anchor() -> i64 {0}\n');obj=temporary/f'auto-invalid-{name}.o'
        for action,extra in (('check',()),('emit-obj',('-o',str(obj)))):
            result=command(action,path,*flags,*extra,success=False,env=env)
            errors=[d for d in json.loads(result.stderr)['diagnostics'] if d['severity']=='error']
            assert result.returncode==1 and len(errors)==1,(name,result.stderr)
            assert errors[0]['kind']=='source' and errors[0]['message']=='core: '+message,(name,result.stderr)
        assert not obj.exists()
    command('test',root/'compiler/core_auto.jh')
    print(f'bounded automation: checked goals/hints, Eq/Lt chains/offsets/rewrites, erasure, both targets, native execution, compatibility and {len(INVALID)} exact rejections passed')
