"""Transparent dependent type aliases: checked expansion, privacy and runtime erasure."""
import ctypes
import json
import os
import platform
import re
import shlex
import struct
from core_buffer import COUNTER

HELPER='''#![dependent_core]
pub type Count = u64
pub type Mem(n: u64) = buffer(n)
pub type Same(a: u64, b: u64) = Eq(a, b)
pub type Below(n: u64) = refine(fn(i) { Lt(i, n) })
pub type Consumer = fn(n: erased(u64), Mem(n)) -> i64
pub type Mapper(n: u64, m: u64) = fn(Mem(m)) -> Mem(n)
pub type Ignore(n: u64) = u64
type Hidden = i64
struct Secret { value: i64 }
pub type Public = Secret
pub fn secret(x: i64) -> Public { Secret { value: x } }
pub fn reveal(s: Public) -> i64 { match s { Secret { value } => value } }
pub fn consume(n: Count, x: i64, f: Consumer) -> i64 { f(n, alloc(n, x)) }
pub fn read(n: erased(Count), b: ref Mem(n), i: Below(n)) -> i64 { index(b, witness(i), proof(i)) }
'''
PREFIX='#![dependent_core]\nimport alias_helper\nimport other_alias\n'
PROGRAM=PREFIX+'''
type Mem(n: u64) = alias_helper.Mem(n)
type Same(a: u64, b: u64) = alias_helper.Same(a, b)
type Again(n: u64) = Mem(n)
type View(n: u64) = ref Again(n)
type Factory = fn(n: u64, i64) -> Mem(n)
struct Holder(n: u64) { data: Again(n) }
fn keep(n: u64, p: erased(Same(n, n))) -> u64 { n }
fn borrow(n: erased(u64), b: View(n), p: erased(Lt(0, n))) -> i64 { index(b, 0, p) }
export fn proof_erased(n: u64) -> u64 { keep(n, refl(n)) }
export fn callbacks(n: u64, x: i64) -> i64 { alias_helper.consume(n, x, fn(k, b) { free(b, 7) }) }
export fn factory(n: u64, x: i64) -> i64 {
    let f: Factory = fn(k, v) { alloc(k, v) }
    let b: Mem(n) = f(n, x)
    free(b, 9)
}
export fn read(x: i64) -> i64 {
    let b: Again(1) = alloc(1, x)
    let a = alias_helper.read(1, b, pack(0, decide_lt(0, 1)))
    let c = borrow(1, b, decide_lt(0, 1))
    free(b, a + c)
}
export fn changed(x: i64) -> i64 {
    let f: alias_helper.Mapper(2, 1) = fn(b) { free(b, alloc(2, x)) }
    free(f(alloc(1, x)), 11)
}
export fn record(n: u64, x: i64) -> i64 {
    let h: Holder(n) = Holder { data: alloc(n, x) }
    match h { Holder { data } => free(data, 13) }
}
export fn opaque(x: i64) -> i64 { let s: alias_helper.Public = alias_helper.secret(x); alias_helper.reveal(s) }
fn ignored(n: erased(u64), x: alias_helper.Ignore(n)) -> u64 { x }
export fn ghost() -> u64 { ignored(18446744073709551615 + 1, 17) }
'''
REFERENCE=PROGRAM.replace('type Mem(n: u64) = alias_helper.Mem(n)','type Mem(n: u64) = buffer(n)')
# Keep checked declarations but spell runtime-facing annotations independently.
REFERENCE=REFERENCE.replace('let f: Factory', 'let f: fn(k: u64, i64) -> buffer(k)').replace('let b: Mem(n)', 'let b: buffer(n)').replace('let b: Again(1)', 'let b: buffer(1)').replace('let f: alias_helper.Mapper(2, 1)', 'let f: fn(buffer(1)) -> buffer(2)').replace('b: View(n)', 'b: ref buffer(n)').replace('p: erased(Same(n, n))', 'p: erased(Eq(n, n))').replace('data: Again(n)', 'data: buffer(n)')
INVALID={
    'nominal-identity': ('fn bad(s: alias_helper.Public) -> i64 { other_alias.reveal(s) }', 'type mismatch'),
    'import-collision': ('type alias_helper = u64', 'duplicate or reserved type alias name'),
    'scope-leak': ('type A(n: u64) = buffer(n)\nfn bad(b: buffer(n)) -> u64 { 0 }', 'unknown name (or recursive/forward definition): n'),
    'missing-body': ('type Bad(n: u64)', 'a type alias needs = type'),
    'parameter-type': ('type Bad(n: i64) = u64', 'type aliases are parameterized by u64 values'),
    'duplicate-parameter': ('type Bad(n: u64, n: u64) = u64', 'duplicate parameter'),
    'reserved': ('type buffer = i64', 'duplicate or reserved type alias name'),
    'duplicate': ('type A = u64\ntype A = i64', 'duplicate or reserved type alias name'),
    'function-collision': ('fn A() -> u64 { 0 }\ntype A = i64', 'duplicate or reserved type alias name'),
    'later-function-collision': ('type A = i64\nfn A() -> u64 { 0 }', 'duplicate definition'),
    'family-collision': ('type A = u64\nstruct A { x: i64 }', 'duplicate or reserved data type name'),
    'cycle': ('type A = A', 'unsupported type in dependent_core'),
    'forward': ('type A = B\ntype B = u64', 'unsupported type in dependent_core'),
    'private': ('fn bad(x: alias_helper.Hidden) -> i64 { x }', 'unsupported type in dependent_core'),
    'missing-index': ('fn bad(x: alias_helper.Mem) -> u64 { 0 }', 'wrong number of type alias indices'),
    'extra-index': ('fn bad(x: alias_helper.Mem(1, 2)) -> u64 { 0 }', 'wrong number of type alias indices'),
    'wrong-index-type': ('fn bad(n: i64, x: alias_helper.Mem(n)) -> u64 { 0 }', 'type mismatch'),
    'unused-index-type': ('fn bad(n: i64, x: alias_helper.Ignore(n)) -> u64 { 0 }', 'type mismatch'),
    'unused-index-proof': ('fn bad(x: alias_helper.Ignore(sub(2, 1, decide_lt(0, 1)))) -> u64 { 0 }', 'type mismatch'),
    'unused-bad-body': ('type Bad = buffer(sub(2, 1, decide_lt(0, 1)))', 'type mismatch'),
    'wrong-buffer': ('fn bad() -> alias_helper.Mem(2) { alloc(1, 0) }', 'type mismatch'),
    'false-proof': ('fn bad() -> alias_helper.Same(0, 1) { refl(0) }', 'type mismatch'),
    'relevant-proof': ('fn bad(p: alias_helper.Same(0, 0)) -> u64 { 0 }', 'proof binders must be erased'),
    'erased-i64': ('type Int = i64\nfn bad(p: erased(Int)) -> u64 { 0 }', 'erased binders must be propositions, u64 or data'),
    'duplicate-owner': ('fn bad(b: alias_helper.Mem(1)) -> i64 { free(b, free(b, 0)) }', 'an owned value is used more than once'),
    'not-constructor': ('fn bad() -> alias_helper.Public { alias_helper.Public { value: 1 } }', 'unknown struct'),
}
ANCHOR='\nexport fn positive_anchor() -> i64 { 0 }\n'


def validate_aliases(compiler,root,temporary,environment,run):
    def command(action,path,*args,success=True,env=environment):
        return run([compiler,action,str(path),*args],success=success,env=env)
    (temporary/'alias_helper.jh').write_text(HELPER)
    (temporary/'other_alias.jh').write_text(HELPER)
    source=temporary/'aliases.jh';source.write_text(PROGRAM)
    reference=temporary/'aliases-reference.jh';reference.write_text(REFERENCE)
    command('check',source,'--lib',env={**environment,'JIHOO_LLVM':'/unavailable','JIHOO_CC':'/unavailable'})
    mir=command('emit-mir',source,'--lib').stdout
    assert mir==command('emit-mir',reference,'--lib').stdout,'transparent aliases changed runtime MIR'
    formatted=temporary/'aliases-formatted.jh';formatted.write_text(command('fmt',source).stdout)
    assert command('fmt',formatted).stdout==formatted.read_text()
    assert command('emit-mir',formatted,'--lib').stdout==mir
    syntax=lambda text: re.sub(r' \d+:\d+', '',text)
    assert syntax(command('emit-ast',source).stdout)==syntax(command('emit-ast',formatted).stdout)
    counter=temporary/'aliases-counter.c';counter.write_text(COUNTER)
    host='aarch64' if platform.machine() in ('aarch64','arm64') else 'x86_64'
    for target,machine in (('x86_64',62),('aarch64',183)):
        for level in ('-O0','-O2'):
            obj=temporary/f'aliases-{target}{level}.o';command('emit-obj',source,'--lib','--target',target,level,'-o',str(obj))
            assert struct.unpack_from('<H',obj.read_bytes(),18)[0]==machine
            if target!=host:continue
            library=temporary/f'aliases{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC','clang')),'-shared','-fPIC',str(obj),str(counter),'-Wl,--wrap=malloc','-Wl,--wrap=free','-o',str(library)])
            native=ctypes.CDLL(str(library))
            for name in ('callbacks','factory','record'):
                f=getattr(native,name);f.argtypes,f.restype=[ctypes.c_uint64,ctypes.c_int64],ctypes.c_int64
            for name in ('read','changed','opaque'):
                f=getattr(native,name);f.argtypes,f.restype=[ctypes.c_int64],ctypes.c_int64
            for n in (0,1,9):
                for x in (-7,0,13):
                    assert native.callbacks(n,x)==7 and native.factory(n,x)==9 and native.record(n,x)==13
                    assert native.read(x)==2*x and native.changed(x)==11 and native.opaque(x)==x
            before=ctypes.c_long.in_dll(native,'allocations').value
            native.proof_erased.argtypes,native.proof_erased.restype=[ctypes.c_uint64],ctypes.c_uint64
            native.ghost.restype=ctypes.c_uint64
            for n in (0,1,(1<<64)-1):assert native.proof_erased(n)==n
            assert native.ghost()==17
            assert ctypes.c_long.in_dll(native,'allocations').value==before==ctypes.c_long.in_dll(native,'frees').value
    snippets=re.findall(r'```jihoo\n(.*?)```',(root/'docs/language/dependent-aliases.md').read_text(),re.S)
    assert len(snippets)==1
    documented=temporary/'aliases-documented.jh';documented.write_text(snippets[0])
    for path in (documented,root/'examples/core_aliases.jh'):
        for level in ('-O0','-O2'):assert command('run',path,level,success=False).returncode==17
    flags=('--lib','--release','--no-verify','--error-format=json');env={**environment,'JIHOO_NO_ELAB':'1'}
    control=temporary/'alias-control.jh';control.write_text(PREFIX+'type Good(n: u64) = buffer(n)\nfn good() -> Good(1) { alloc(1, 0) }'+ANCHOR)
    obj=temporary/'alias-control.o';command('emit-obj',control,*flags,'-o',str(obj),env=env);assert obj.read_bytes().startswith(b'\x7fELF')
    for name,(body,message) in INVALID.items():
        bad=temporary/f'alias-{name}.jh';bad.write_text(PREFIX+body+ANCHOR);obj=temporary/f'alias-{name}.o'
        for action,opts in (('check',()),('emit-obj',('-o',str(obj)))):
            r=command(action,bad,*flags,*opts,success=False,env=env)
            errors=[d for d in json.loads(r.stderr)['diagnostics'] if d['severity']=='error']
            assert r.returncode==1 and len(errors)==1,(name,r.stderr)
            assert errors[0]['kind']=='source' and errors[0]['message']=='core: '+message,(name,r.stderr)
        assert not obj.exists()
    legacy=temporary/'alias-legacy.jh';legacy.write_text('type Bad(n: u64) = u64\nfn main() -> i64 { 0 }')
    assert 'parameterized type aliases require dependent_core' in command('check',legacy,success=False).stderr
    print(f'dependent aliases: MIR transparency, module privacy, higher-order/indexed types, both targets, ownership and {len(INVALID)} exact rejections passed')
