"""Flat records retain field effects once, without a runtime aggregate layout."""
import ctypes
import json
import os
import platform
import shlex
import struct
from core_buffer import COUNTER

PREFIX='#![dependent_core]\n'
PROGRAM=PREFIX+'''
struct Cell(n: u64) { value: i64, same: erased(Eq(n, n)) }
struct Pair { left: i64, right: i64 }
struct Bounded { bound: u64, at: refine(fn(i) { Lt(i, bound) }) }
struct Nested { cell: Cell(1), other: i64 }
enum Choice { Yes(Cell(1)); No(i64) }
fn effect(n: u64, x: i64) -> i64 { free(alloc(n, x), x) }
export fn telescope(n: u64) -> u64 {
    let s = Bounded { bound: free(alloc(n, 0), 1), at: pack(0, decide_lt(0, 1)) }
    let Bounded { bound, at } = s
    bound + witness(at)
}
export fn repeated(n: u64, x: i64) -> i64 {
    let c = Cell(n) { value: effect(n, x), same: refl(n) }
    let Cell { value, .. } = c
    value + value
}
export fn discarded(n: u64, x: i64) -> i64 {
    let _ = Cell(n) { value: effect(n, x), same: refl(n) }
    19
}
export fn ordered(n: u64) -> i64 {
    let p = Pair { right: effect(n + 1, 5), left: effect(n, 3) }
    let Pair { left, right } = p
    left * 10 + right
}
export fn nested(n: u64, x: i64) -> i64 {
    let s = Nested { cell: Cell(1) { value: effect(n, x), same: refl(1) }, other: effect(n + 1, 2) }
    let Nested { cell: Cell { value, .. }, other } = s
    value + other
}
export fn selected(n: u64, x: i64) -> i64 {
    let c = Choice.Yes(Cell(1) { value: if_lt(0, n, fn(_) { effect(n, x) }, effect(n, 7)), same: refl(1) })
    match c { Choice.Yes(Cell { value, .. }) => value + value, Choice.No(value) => value }
}
export fn borrowed(x: i64) -> i64 {
    let b = alloc(1, x)
    let read = index(b, 0, decide_lt(0, 1))
    let c = Cell(1) { value: effect(1, read), same: refl(1) }
    let Cell { value, .. } = c
    free(b, value + value)
}
export fn ghost_index(n: u64) -> i64 {
    let c = Cell(18446744073709551615 + 1) { value: effect(n, 23), same: refl(18446744073709551615 + 1) }
    let Cell { value, .. } = c
    value
}
'''
RAW = """
(data Scalar (Wrap (pi x I64 Scalar)))
(export twice (pi n U64 (pi x I64 I64))
  (lam n U64 (lam x I64
    (app (lam s Scalar
      (induct Scalar (lam _ Scalar I64) (lam y I64 (add y y)) s))
      (Wrap (free (alloc n x) x))))))
"""
RAW_SOURCE = PREFIX + """
struct Scalar { value: i64 }
export fn twice(n: u64, x: i64) -> i64 {
    let s = Scalar { value: free(alloc(n, x), x) }
    let Scalar { value } = s
    value + value
}
"""
REFERENCE = RAW_SOURCE.replace('let s = Scalar { value: free(alloc(n, x), x) }',
    'let item = free(alloc(n, x), x); let s = Scalar { value: item }')
INVALID = {
 'wrong-field': ('fn bad() -> Cell(1) { Cell(1) { value: effect(1, 7), same: refl(2) } }', 'type mismatch'),
 'owner-reused': ('fn bad(b: buffer(1)) -> i64 { let c = Cell(1) { value: free(b, 7), same: refl(1) }; let Cell { value, .. } = c; free(b, value) }', 'an owned value is used more than once'),
 'erased-used': ('fn bad(n: erased(u64)) -> i64 { let c = Cell(n) { value: effect(n, 7), same: refl(n) }; let Cell { value, .. } = c; value }', 'erased value used at runtime'),
}

TRAPS={
 'discarded': 'fn main() -> i64 { let _ = Cell(1) { value: effect(1, 9223372036854775807 + 1), same: refl(1) }; 0 }',
 'unused-field': 'fn main() -> i64 { let p = Pair { left: effect(1, 7), right: 9223372036854775807 + 1 }; let Pair { left, .. } = p; left }',
 'before-effect': 'fn main() -> i64 { let p = Pair { left: 9223372036854775807 + 1, right: effect(1, 7) }; let Pair { right, .. } = p; right }',
}


def validate_record_effects(compiler,root,temporary,environment,run):
    def command(action,path,*args,success=True,env=environment):
        return run([compiler,action,str(path),*args],success=success,env=env)
    source=temporary/'record-effects.jh';source.write_text(PROGRAM)
    command('check',source,'--lib')
    raw=temporary/'record-effects.jhc';raw.write_text(RAW)
    paired=temporary/'record-effects-paired.jh';paired.write_text(RAW_SOURCE)
    reference=temporary/'record-effects-reference.jh';reference.write_text(REFERENCE)
    run([compiler,'core','check',str(raw)],env=environment)
    run([compiler,'core','preserves',str(raw)],env=environment)
    mir=command('emit-mir',paired,'--lib').stdout
    assert mir==run([compiler,'core','emit-mir',str(raw)],env=environment).stdout
    assert mir==command('emit-mir',reference,'--lib').stdout
    counter=temporary/'record-effects-counter.c';counter.write_text(COUNTER.replace('long allocations, frees;', 'long allocations, frees; long events[64], event_count;').replace('allocations++;','allocations++; if (event_count < 64) events[event_count++] = (long)n;').replace('frees++;','frees++; if (event_count < 64) events[event_count++] = -1;'))
    host='aarch64' if platform.machine() in ('aarch64','arm64') else 'x86_64'
    for target,machine in (('x86_64',62),('aarch64',183)):
        for level in ('-O0','-O2'):
            obj=temporary/f'record-effects-{target}{level}.o';command('emit-obj',source,'--lib','--target',target,level,'-o',str(obj))
            assert struct.unpack_from('<H',obj.read_bytes(),18)[0]==machine
            if target!=host:continue
            library=temporary/f'record-effects{level}.so';run([*shlex.split(os.environ.get('JIHOO_CC','clang')),'-shared','-fPIC',str(obj),str(counter),'-Wl,--wrap=malloc','-Wl,--wrap=free','-o',str(library)])
            native=ctypes.CDLL(str(library))
            for name in ('repeated','discarded','nested','selected'):
                f=getattr(native,name);f.argtypes,f.restype=[ctypes.c_uint64,ctypes.c_int64],ctypes.c_int64
            for name in ('ordered','ghost_index','telescope'):
                f=getattr(native,name);f.argtypes,f.restype=[ctypes.c_uint64],ctypes.c_int64
            native.borrowed.argtypes,native.borrowed.restype=[ctypes.c_int64],ctypes.c_int64
            for n in (0,1,7):
                for x in (-9,0,13):
                    before=ctypes.c_long.in_dll(native,'allocations').value
                    assert native.repeated(n,x)==2*x and native.discarded(n,x)==19
                    if level=='-O0': assert ctypes.c_long.in_dll(native,'allocations').value-before==2
                    assert native.nested(n,x)==x+2 and native.selected(n,x)==(2*x if n else 14)
                    assert native.borrowed(x)==2*x
                assert native.ghost_index(n)==23 and native.telescope(n)==1
            ctypes.c_long.in_dll(native,'event_count').value=0
            assert native.ordered(3)==35
            if level=='-O0':
                count=ctypes.c_long.in_dll(native,'event_count').value
                assert list((ctypes.c_long*64).in_dll(native,'events'))[:count]==[32,-1,40,-1]
            assert ctypes.c_long.in_dll(native,'allocations').value==ctypes.c_long.in_dll(native,'frees').value
    for name,body in TRAPS.items():
        path=temporary/f'record-effects-trap-{name}.jh';path.write_text(PROGRAM+body)
        for level in ('-O0','-O2'):assert command('run',path,level,success=False).returncode==132,(name,level)
    flags=('--lib','--release','--no-verify','--error-format=json')
    anchor='\nexport fn rejection_anchor() -> i64 { 0 }\n'
    env={**environment,'JIHOO_NO_ELAB':'1'}
    control=temporary/'record-effects-control.o'
    command('emit-obj',source,*flags,'-o',str(control),env=env)
    assert control.read_bytes().startswith(b'\x7fELF')
    for name,(body,message) in INVALID.items():
        path=temporary/f'record-effects-invalid-{name}.jh';path.write_text(PROGRAM+body+anchor)
        obj=temporary/f'record-effects-invalid-{name}.o'
        for action,extra in (('check',()),('emit-obj',('-o',str(obj)))):
            result=command(action,path,*flags,*extra,success=False,env=env)
            errors=[d for d in json.loads(result.stderr)['diagnostics'] if d['severity']=='error']
            assert result.returncode==1 and len(errors)==1,(name,result.stderr)
            assert errors[0]['kind']=='source' and errors[0]['message']=='core: '+message,(name,result.stderr)
        assert not obj.exists()
    print('flat record effects: both targets, O0/O2 native repetition/discard/nesting/branches/borrows, declaration order, erasure and traps passed')
