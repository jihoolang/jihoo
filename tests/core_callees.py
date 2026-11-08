"""Compound callees preserve scope/effects and retain continuation boundaries."""
import ctypes
import json
import os
import platform
import re
import shlex
import struct
from core_buffer import COUNTER

HELPER='''#![dependent_core]
pub fn factory(n: u64) -> fn(i64) -> buffer(n) { fn(x) { alloc(n, x) } }
'''
PREFIX='#![dependent_core]\nimport callee_helper\nenum Pick { Left; Right }\n'
BODIES={
'plain': ('export fn plain(x: i64) -> i64 { ({ let f = fn(y: i64) -> i64 { y + 1 }; f })(x) }',
          'export fn plain(x: i64) -> i64 { let g = { let f = fn(y: i64) -> i64 { y + 1 }; f }; g(x) }'),
'borrowed': ('''export fn borrowed(x: i64) -> i64 {
    let b = alloc(1, x)
    ({ let get = fn(data: ref buffer(1)) -> i64 { index(data, 0, decide_lt(0, 1)) }; get })(b)
}''', '''export fn borrowed(x: i64) -> i64 {
    let b = alloc(1, x)
    let f = { let get = fn(data: ref buffer(1)) -> i64 { index(data, 0, decide_lt(0, 1)) }; get }
    f(b)
}'''),
'dependent': ('''export fn dependent(x: i64) -> i64 {
    ({ let release = fn(k: erased(u64), b: buffer(k)) -> i64 { free(b, x) }; release })(1, alloc(1, x))
}''', '''export fn dependent(x: i64) -> i64 {
    let f = { let release = fn(k: erased(u64), b: buffer(k)) -> i64 { free(b, x) }; release }
    f(1, alloc(1, x))
}'''),
'factory': ('export fn factory(n: u64) -> i64 { let b = ({ callee_helper.factory(n) })(7); free(b, 9) }',
            'export fn factory(n: u64) -> i64 { let f = { callee_helper.factory(n) }; let b = f(7); free(b, 9) }'),
'evidence': ('export fn evidence(n: u64) -> u64 { let p = ({ let f = fn(k: u64) -> Eq(k + 1, k + 1) { refl(k + 1) }; f })(n); n }',
             'export fn evidence(n: u64) -> u64 { let f = { let g = fn(k: u64) -> Eq(k + 1, k + 1) { refl(k + 1) }; g }; let p = f(n); n }'),
'shadow': ('export fn shadow(x: i64) -> i64 { let f = fn(y: i64) -> i64 { y + 3 }; ({ let f = fn(y: i64) -> i64 { y + 1 }; f })(x) + f(x) }',
           'export fn shadow(x: i64) -> i64 { let f = fn(y: i64) -> i64 { y + 3 }; let g = { let f = fn(y: i64) -> i64 { y + 1 }; f }; g(x) + f(x) }'),
'ordered': ('''export fn ordered(n: u64) -> i64 {
    ({ let marker = free(alloc(n, 7), 1); fn(x: i64) -> i64 { free(alloc(n + 2, 7), x + marker) } })(free(alloc(n + 1, 7), 5))
}''', '''export fn ordered(n: u64) -> i64 {
    let f = { let marker = free(alloc(n, 7), 1); fn(x: i64) -> i64 { free(alloc(n + 2, 7), x + marker) } }
    f(free(alloc(n + 1, 7), 5))
}'''),
'partial': ('''export fn partial(n: u64) -> i64 {
    let g = ({ let marker = free(alloc(n, 7), 1); fn(x: i64, y: i64) -> i64 { free(alloc(n + 2, 7), x + y + marker) } })(free(alloc(n + 1, 7), 5))
    g(2) + g(3)
}''', '''export fn partial(n: u64) -> i64 {
    let f = { let marker = free(alloc(n, 7), 1); fn(x: i64, y: i64) -> i64 { free(alloc(n + 2, 7), x + y + marker) } }
    let g = f(free(alloc(n + 1, 7), 5))
    g(2) + g(3)
}'''),
'unused_partial': ('''export fn unused_partial(n: u64) -> i64 {
    let g = ({ let marker = free(alloc(n, 7), 1); fn(x: i64, y: i64) -> i64 { free(alloc(n + 2, 7), x + y + marker) } })(free(alloc(n + 1, 7), 5))
    0
}''', '''export fn unused_partial(n: u64) -> i64 {
    let f = { let marker = free(alloc(n, 7), 1); fn(x: i64, y: i64) -> i64 { free(alloc(n + 2, 7), x + y + marker) } }
    let g = f(free(alloc(n + 1, 7), 5))
    0
}'''),
}
BODIES['capture_once'] = (
    'export fn capture_once(n: u64) -> i64 { let b = alloc(n, 7); ({ fn(x: i64) -> i64 { free(b, x) } })(11) }',
    'export fn capture_once(n: u64) -> i64 { let b = alloc(n, 7); (fn(x: i64) -> i64 { free(b, x) })(11) }',
)
PROGRAM=PREFIX+'\n'.join(a for a,b in BODIES.values())
REFERENCE=PREFIX+'\n'.join(b for a,b in BODIES.values())
INVALID={
    'scalar-callee': ('fn bad() -> i64 { ({ 1 })(2) }', 'application requires a dependent function'),
    'empty-callee': ('fn bad() -> fn(i64) -> i64 { ({ fn(x: i64) -> i64 { x } })() }', 'a function-valued call needs at least one argument'),
    'escaped-name': ('fn bad() -> i64 { let x = ({ let only = fn(x: i64) -> i64 { x }; only })(1); only(x) }', 'unknown name (or recursive/forward definition): only'),
    'wrong-index': ('fn bad() -> i64 { ({ fn(b: buffer(1)) -> i64 { free(b, 0) } })(alloc(2, 7)) }', 'type mismatch'),
    'owned-capture': ('fn bad(b: buffer(1)) -> i64 { let g = ({ fn(x: i64, y: i64) -> i64 { free(b, x + y) } })(7); g(1) + g(2) }', 'a function cannot capture an owned value'),
    'unused-malformed': ('fn bad() -> i64 { ({ let f = fn(n: u64) -> Eq(n, n + 1) { refl(n) }; fn(x: i64) -> i64 { x } })(7) }', 'type mismatch'),
    'match-contextual': ('fn bad(p: Pick) -> fn(i64) -> i64 { match p { Pick.Left => fn(x) { x }, Pick.Right => fn(x) { x } } }', 'a match result cannot be a function'),
    'match-inferred': ('fn bad(p: Pick) -> i64 { let f = match p { Pick.Left => fn(x: i64) -> i64 { x }, Pick.Right => fn(x: i64) -> i64 { x } }; f(1) }', 'a match result cannot be a function'),
    'match-direct': ('fn bad(p: Pick) -> i64 { (match p { Pick.Left => fn(x: i64) -> i64 { x }, Pick.Right => fn(x: i64) -> i64 { x } })(1) }', 'a match result cannot be a function'),
    'match-single': ('struct Record { value: i64 } fn bad(p: Record) -> i64 { let f = match p { Record { value } => fn(x: i64) -> i64 { value + x } }; f(1) }', 'a match result cannot be a function'),
    'missing-pattern': ('enum Payload { Some(i64) } fn bad(p: Payload) -> fn(i64) -> i64 { match p { Payload.Some() => fn(x) { x } } }', 'a match arm binds every field'),
    'extra-pattern': ('fn bad(p: Pick) -> fn(i64) -> i64 { match p { Pick.Left(x) => fn(y) { y }, Pick.Right => fn(y) { y } } }', 'a match arm binds every field'),
}
TRAPS={
    'callee': 'fn main() -> i64 { ({ let x = 9223372036854775807 + 1; fn(y: i64) -> i64 { y } })(7) }',
    'argument': 'fn main() -> i64 { ({ fn(_: i64) -> i64 { 7 } })(9223372036854775807 + 1) }',
    'body': 'fn main() -> i64 { ({ fn(_: i64) -> i64 { 9223372036854775807 + 1 } })(7) }',
    'discarded-partial': 'fn main() -> i64 { let g = ({ let x = 9223372036854775807 + 1; fn(_: i64, _: i64) -> i64 { 7 } })(0); 0 }',
}


def validate_callees(compiler, root, temporary, environment, run):
    def command(action,path,*args,success=True,env=environment):
        return run([compiler,action,str(path),*args],success=success,env=env)
    (temporary/'callee_helper.jh').write_text(HELPER)
    source=temporary/'callees.jh';source.write_text(PROGRAM)
    reference=temporary/'callees-reference.jh';reference.write_text(REFERENCE)
    command('check',source,'--lib',env={**environment,'JIHOO_LLVM':'/unavailable','JIHOO_CC':'/unavailable'})
    mir=command('emit-mir',source,'--lib').stdout
    assert mir==command('emit-mir',reference,'--lib').stdout,'compound/reference callee MIR differs'
    formatted=temporary/'callees-formatted.jh';formatted.write_text(command('fmt',source).stdout)
    assert command('fmt',formatted).stdout==formatted.read_text()
    assert command('emit-mir',formatted,'--lib').stdout==mir
    counter=temporary/'callees-counter.c';counter.write_text(COUNTER.replace('long allocations, frees;', 'long allocations, frees; long events[64], event_count;').replace('allocations++;','allocations++; if (event_count < 64) events[event_count++] = (long)n;').replace('frees++;','frees++; if (event_count < 64) events[event_count++] = -1;'))
    host='aarch64' if platform.machine() in ('aarch64','arm64') else 'x86_64'
    for target,machine in (('x86_64',62),('aarch64',183)):
        for level in ('-O0','-O2'):
            obj=temporary/f'callees-{target}{level}.o';command('emit-obj',source,'--lib','--target',target,level,'-o',str(obj))
            assert struct.unpack_from('<H',obj.read_bytes(),18)[0]==machine
            if target!=host:continue
            library=temporary/f'callees{level}.so';run([*shlex.split(os.environ.get('JIHOO_CC','clang')),'-shared','-fPIC',str(obj),str(counter),'-Wl,--wrap=malloc','-Wl,--wrap=free','-o',str(library)])
            native=ctypes.CDLL(str(library))
            for name in ('plain','borrowed','dependent','shadow'):
                fn=getattr(native,name);fn.argtypes,fn.restype=[ctypes.c_int64],ctypes.c_int64
            for name in ('factory','ordered','partial','unused_partial','evidence','capture_once'):
                fn=getattr(native,name);fn.argtypes,fn.restype=[ctypes.c_uint64],ctypes.c_uint64
            for x in (-19,0,100):
                assert native.plain(x)==x+1 and native.borrowed(x)==x and native.dependent(x)==x and native.shadow(x)==2*x+4
            for n in (0,1,7):assert native.factory(n)==9 and native.capture_once(n)==11
            for n in (0,1,(1<<64)-1):assert native.evidence(n)==n
            for name,expected,events in (('ordered',6,[32,-1,40,-1,48,-1]),('partial',17,[32,-1,40,-1,48,-1,48,-1]),('unused_partial',0,[32,-1,40,-1])):
                ctypes.c_long.in_dll(native,'event_count').value=0
                assert getattr(native,name)(3)==expected
                if level=='-O0':
                    count=ctypes.c_long.in_dll(native,'event_count').value
                    assert list((ctypes.c_long*64).in_dll(native,'events'))[:count]==events,name
            assert ctypes.c_long.in_dll(native,'allocations').value==ctypes.c_long.in_dll(native,'frees').value
    for name,body in TRAPS.items():
        path=temporary/f'callee-trap-{name}.jh';path.write_text(PREFIX+body)
        for level in ('-O0','-O2'):
            assert command('run',path,level,success=False).returncode==132,(name,level)
    lazy=temporary/'callee-lazy.jh';lazy.write_text(PREFIX+'fn main() -> i64 { let g = ({ fn(_: i64, _: i64) -> i64 { 9223372036854775807 + 1 } })(0); 7 }')
    for level in ('-O0','-O2'):assert command('run',lazy,level,success=False).returncode==7
    flags=('--lib','--release','--no-verify','--error-format=json');env={**environment,'JIHOO_NO_ELAB':'1'}
    anchor='\nexport fn harness_anchor() -> i64 { 0 }\n'
    control=temporary/'callee-control.jh';control.write_text(PREFIX+'fn good() -> i64 { ({ fn(x: i64) -> i64 { x } })(7) }'+anchor)
    obj=temporary/'callee-control.o';command('emit-obj',control,*flags,'-o',str(obj),env=env);assert obj.read_bytes().startswith(b'\x7fELF')
    for name,(body,message) in INVALID.items():
        path=temporary/f'callee-invalid-{name}.jh';path.write_text(PREFIX+body+anchor);obj=temporary/f'callee-invalid-{name}.o'
        for action,extra in (('check',()),('emit-obj',('-o',str(obj)))):
            result=command(action,path,*flags,*extra,success=False,env=env)
            errors=[d for d in json.loads(result.stderr)['diagnostics'] if d['severity']=='error']
            assert result.returncode==1 and len(errors)==1,(name,result.stderr)
            assert errors[0]['kind']=='source' and errors[0]['message']=='core: '+message,(name,result.stderr)
        assert not obj.exists()
    print(f'compound callees: exact named/immediate reference MIR, both targets, native effect order/ownership/traps and {len(INVALID)} exact rejections passed')
