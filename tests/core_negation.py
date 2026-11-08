"""Computed signed negation: existing subtraction MIR, traps and single evaluation."""
import ctypes
import json
import os
import platform
import random
import re
import shlex
import struct
from core_buffer import COUNTER

PREFIX = '#![dependent_core]\nimport dependent.list\n'
PROGRAM = PREFIX + '''
fn identity(x: i64) -> i64 { x }
export fn negative(x: i64) -> i64 { -x }
export fn double(x: i64) -> i64 { -(-x) }
export fn arithmetic(x: i64) -> i64 { -(x + 1) }
export fn called(x: i64) -> i64 { -identity(x) }
export fn selected(n: u64, x: i64) -> i64 { if_lt(n, 1, fn(_) { -x }, x) }
export fn array(x: i64) -> i64 { index([-x, x], 0, decide_lt(0, 2)) }
export fn looped(n: u64, x: i64) -> i64 { fold(n, 0, fn(_, _, acc) { acc + -x }) }
fn read(b: ref buffer(1)) -> i64 { -index(b, 0, decide_lt(0, 1)) }
export fn borrowed(x: i64) -> i64 { let b = alloc(1, x); read(b) }
export fn effect(n: u64, x: i64) -> i64 { -free(alloc(n, x), x) }
export fn mapped(x: i64) -> i64 {
    let xs = list.repeat(3, x)
    let ys = list.map(xs, fn(v) { -v })
    list.sum(ys)
}
export fn minimum() -> i64 { -9223372036854775808 }
'''
REFERENCE = PROGRAM.replace('-(-x)', '(0 - (0 - x))').replace('-(x + 1)', '(0 - (x + 1))')
REFERENCE = REFERENCE.replace('-identity(x)', '(0 - identity(x))').replace('-index(b, 0, decide_lt(0, 1))', '(0 - index(b, 0, decide_lt(0, 1)))')
REFERENCE = REFERENCE.replace('-free(alloc(n, x), x)', '(0 - free(alloc(n, x), x))').replace('-x', '(0 - x)').replace('-v', '(0 - v)')
INVALID = {
    'unsigned-operand': ('fn bad(x: u64) -> i64 { -x }', 'type mismatch'),
    'unsigned-result': ('fn bad(x: i64) -> u64 { -x }', 'type mismatch'),
    'mixed-add': ('fn bad(x: u64) -> i64 { -x + 1 }', 'type mismatch'),
    'owned-operand': ('fn bad(b: buffer(1)) -> i64 { -b }', 'type mismatch'),
    'proof-operand': ('fn bad(p: erased(Eq(0, 0))) -> i64 { -p }', 'erased value used at runtime'),
    'erased-operand': ('fn bad(n: erased(u64)) -> i64 { -n }', 'erased value used at runtime'),
    'literal-underflow': ('fn bad() -> i64 { -9223372036854775809 }', 'I64 literal underflow'),
    'discarded-unsigned': ('fn bad(x: u64) -> i64 { let ignored = -x; 0 }', 'type mismatch'),
}
TRAPS = {
    'variable': 'fn negate(x: i64) -> i64 { -x } fn main() -> i64 { negate(-9223372036854775808) }',
    'double': 'fn main() -> i64 { -(-9223372036854775808) }',
    'discarded': 'fn negate(x: i64) -> i64 { let ignored = -x; 7 } fn main() -> i64 { negate(-9223372036854775808) }',
    'argument': 'fn ignore(_: i64) -> i64 { 7 } fn main() -> i64 { ignore(-(-9223372036854775808)) }',
    'captured': 'fn main() -> i64 { let f = fn(_: i64, _: i64) -> i64 { 7 }; let g = f(-(-9223372036854775808)); 0 }',
    'inner-overflow': 'fn main() -> i64 { -(9223372036854775807 + 1) }',
}


def validate_negation(compiler, root, temporary, environment, run):
    def command(action, path, *args, success=True, env=environment):
        return run([compiler, action, str(path), *args], success=success, env=env)
    source = temporary/'negation.jh'; source.write_text(PROGRAM)
    reference = temporary/'negation-reference.jh'; reference.write_text(REFERENCE)
    command('check', source, '--lib', env={**environment, 'JIHOO_LLVM':'/unavailable', 'JIHOO_CC':'/unavailable'})
    mir = command('emit-mir', source, '--lib').stdout
    assert mir == command('emit-mir', reference, '--lib').stdout, 'negation differs from checked subtraction'
    formatted = temporary/'negation-formatted.jh'; formatted.write_text(command('fmt', source).stdout)
    assert command('fmt', formatted).stdout == formatted.read_text()
    assert command('emit-mir', formatted, '--lib').stdout == mir
    counter = temporary/'negation-counter.c'; counter.write_text(COUNTER)
    host = 'aarch64' if platform.machine() in ('aarch64','arm64') else 'x86_64'
    rng = random.Random(6406)
    values = [-(1<<63)+1, -(1<<62), -1, 0, 1, (1<<62), (1<<63)-1]
    values += [rng.randrange(-(1<<63)+1, 1<<63) for _ in range(30)]
    for target, machine in (('x86_64',62), ('aarch64',183)):
        for level in ('-O0','-O2'):
            obj = temporary/f'negation-{target}{level}.o'
            command('emit-obj', source, '--lib', '--target', target, level, '-o', str(obj))
            assert struct.unpack_from('<H', obj.read_bytes(), 18)[0] == machine
            if target != host: continue
            library = temporary/f'negation{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC','clang')), '-shared','-fPIC',str(obj),str(counter),'-Wl,--wrap=malloc','-Wl,--wrap=free','-o',str(library)])
            native = ctypes.CDLL(str(library))
            for name in ('negative','double','arithmetic','called','array','borrowed','mapped'):
                fn=getattr(native,name); fn.argtypes,fn.restype=[ctypes.c_int64],ctypes.c_int64
            for name in ('selected','looped','effect'):
                fn=getattr(native,name); fn.argtypes,fn.restype=[ctypes.c_uint64,ctypes.c_int64],ctypes.c_int64
            native.minimum.restype=ctypes.c_int64
            assert native.minimum()==-(1<<63)
            for x in values:
                assert native.negative(x)==-x and native.double(x)==x
                assert native.called(x)==-x and native.array(x)==-x and native.borrowed(x)==-x
                if x < (1<<63)-1: assert native.arithmetic(x)==-(x+1)
                for n in (0,1,7):
                    before=ctypes.c_long.in_dll(native,'allocations').value
                    assert native.effect(n,x)==-x
                    if level=='-O0': assert ctypes.c_long.in_dll(native,'allocations').value==before+1
                assert native.selected(0,x)==-x and native.selected(1,x)==x
            assert native.selected(1,-(1<<63))==-(1<<63), 'untaken negation trapped'
            assert native.looped(0,-(1<<63))==0, 'zero-iteration negation trapped'
            for x in (-100,-1,0,1,100):
                assert native.mapped(x)==-3*x
                for n in (0,1,8): assert native.looped(n,x)==-n*x
            assert ctypes.c_long.in_dll(native,'allocations').value==ctypes.c_long.in_dll(native,'frees').value
    for name, body in TRAPS.items():
        path=temporary/f'negation-trap-{name}.jh'; path.write_text(PREFIX+body)
        for level in ('-O0','-O2'):
            for mode in ((),('--release',)):
                assert command('run',path,level,*mode,success=False).returncode==132,(name,level,mode)
    flags=('--lib','--release','--no-verify','--error-format=json')
    env={**environment,'JIHOO_NO_ELAB':'1'}
    anchor='\nexport fn harness_anchor() -> i64 { 0 }\n'
    control=temporary/'negation-control.jh';control.write_text(PREFIX+'fn valid(x: i64) -> i64 { -x }'+anchor)
    obj=temporary/'negation-control.o';command('emit-obj',control,*flags,'-o',str(obj),env=env)
    assert obj.read_bytes().startswith(b'\x7fELF')
    for name,(body,message) in INVALID.items():
        path=temporary/f'negation-invalid-{name}.jh';path.write_text(PREFIX+body+anchor)
        obj=temporary/f'negation-invalid-{name}.o'
        for action,extra in (('check',()),('emit-obj',('-o',str(obj)))):
            result=command(action,path,*flags,*extra,success=False,env=env)
            errors=[d for d in json.loads(result.stderr)['diagnostics'] if d['severity']=='error']
            assert result.returncode==1 and len(errors)==1,(name,result.stderr)
            assert errors[0]['kind']=='source' and errors[0]['message']=='core: '+message,(name,result.stderr)
        assert not obj.exists()
    print(f'computed negation: exact subtraction MIR, both targets, native boundaries/ownership/traps and {len(INVALID)} exact rejections passed')
