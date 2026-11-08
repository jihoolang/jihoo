"""Ownership-transferring concatenation inside an indexed runtime loop."""
import ctypes
import json
import os
import platform
import shlex
import struct
from core_buffer import COUNTER

PREFIX = '#![dependent_core]\nimport dependent.list\nimport dependent.sized_list\n'
ANCHOR = '\nexport fn positive_anchor() -> i64 { 0 }\n'
INVALID = {
    'alias-prefix-suffix': ('fn bad(xs: list.List) -> list.List { list.append_into(xs, xs) }', 'an owned value is used more than once'),
    'duplicate-suffix': ('fn bad(xs: ref list.List, ys: list.List) -> i64 { let zs = list.append_into(xs, ys); list.sum(ys) }', 'an owned value is used more than once'),
    'borrowed-suffix': ('fn bad(xs: ref list.List, ys: ref list.List) -> list.List { list.append_into(xs, ys) }', 'type mismatch'),
    'false-length': ('fn bad(xs: ref list.List, ys: list.List) -> Eq(list.length(list.append_into(xs, ys)), list.length(xs)) { list.append_into_length(xs, ys) }', 'type mismatch'),
    'wrong-sized-index': ('fn bad(xs: ref sized_list.Sized(2), ys: sized_list.Sized(3)) -> sized_list.Sized(4) { sized_list.append_into(2, 3, xs, ys) }', 'type mismatch'),
    'duplicate-sized-suffix': ('fn bad(xs: ref sized_list.Sized(2), ys: sized_list.Sized(3)) -> u64 { let zs = sized_list.append_into(2, 3, xs, ys); witness(sized_list.size(3, ys)) }', 'an owned value is used more than once'),
    'wrong-loop-step': ('fn bad(n: u64, pair: ref sized_list.Sized(2)) -> sized_list.Sized(n + n) { fold(n, fn(k) { sized_list.Sized(k + k) }, sized_list.empty(), fn(i, p, acc) { acc }) }', 'type mismatch'),
}
EXTRA = '''
import dependent.list
export fn concatenated(n: u64, m: u64, x: i64, y: i64) -> i64 {
    let xs = list.repeat(n, x)
    let zs = list.append_into(xs, list.repeat(m, y))
    let original = list.sum(xs)
    original + list.sum(zs)
}
fn digits(xs: ref list.List) -> i64 {
    induct(fn(t) { i64 }, 0, fn(x, rest, ih) { x + 10 * ih }, xs)
}
export fn ordered() -> i64 {
    let xs = list.List.Cons(1, list.List.Cons(2, list.List.Nil))
    let zs = list.append_into(xs, list.List.Cons(3, list.List.Cons(4, list.List.Nil)))
    digits(zs)
}
'''
CHECKED = PREFIX + '''
fn pairs(n: u64, pair: ref sized_list.Sized(2)) -> sized_list.Sized(n + n) {
    fold(n, fn(k) { sized_list.Sized(k + k) }, sized_list.empty(),
        fn(i, p, acc) { sized_list.append_into(2, i + i, pair, acc) })
}
export fn total(n: u64, x: i64, y: i64) -> i64 {
    let pair = sized_list.cons(1, x, sized_list.cons(0, y, sized_list.empty()))
    let xs = pairs(n, pair)
    let ys = sized_list.into_list(n + n, xs)
    list.sum(ys)
}
'''
REFERENCE = '''#![dependent_core]
import dependent.list
struct Sized { data: list.List }
fn empty() -> Sized { Sized { data: list.List.Nil } }
fn cons(x: i64, xs: Sized) -> Sized {
    match xs { Sized { data } => Sized { data: list.List.Cons(x, data) } }
}
fn append_into(xs: ref Sized, ys: Sized) -> Sized {
    match xs { Sized { data: left } => match ys {
        Sized { data: right } => Sized { data: list.append_into(left, right) }
    } }
}
fn pairs(n: u64, pair: ref Sized) -> Sized {
    fold(n, empty(), fn(i, p, acc) { append_into(pair, acc) })
}
fn into_list(xs: Sized) -> list.List { match xs { Sized { data } => data } }
export fn total(n: u64, x: i64, y: i64) -> i64 {
    let pair = cons(x, cons(y, empty()))
    let xs = pairs(n, pair)
    let ys = into_list(xs)
    list.sum(ys)
}
'''


def validate_sized_concat(compiler, root, temporary, environment, run):
    def command(action, path, *args, success=True, env=environment):
        return run([compiler, action, str(path), *args], success=success, env=env)
    checked, reference = temporary/'concat-checked.jh', temporary/'concat-reference.jh'
    checked.write_text(CHECKED); reference.write_text(REFERENCE)
    assert command('emit-mir', checked, '--lib').stdout == command('emit-mir', reference, '--lib').stdout
    example = root/'examples/core_sized_concat.jh'
    source = temporary/'sized-concat.jh'; source.write_text(example.read_text()+EXTRA)
    command('check', source, '--lib', env={**environment,'JIHOO_LLVM':'/unavailable','JIHOO_CC':'/unavailable'})
    mir = command('emit-mir', source, '--lib').stdout
    formatted = temporary/'concat-formatted.jh'; formatted.write_text(command('fmt', source).stdout)
    assert command('fmt', formatted).stdout == formatted.read_text()
    assert command('emit-mir', formatted, '--lib').stdout == mir
    counter = temporary/'concat-counter.c'; counter.write_text(COUNTER)
    host = 'aarch64' if platform.machine() in ('aarch64','arm64') else 'x86_64'
    for target, machine in (('x86_64',62),('aarch64',183)):
        for level in ('-O0','-O2'):
            obj=temporary/f'concat-{target}{level}.o'
            command('emit-obj',source,'--lib','--target',target,level,'-o',str(obj))
            assert struct.unpack_from('<H',obj.read_bytes(),18)[0]==machine
            if target!=host: continue
            shared=temporary/f'concat{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC','clang')),'-shared','-fPIC',str(obj),str(counter),'-o',str(shared),'-Wl,--wrap=malloc','-Wl,--wrap=free'])
            native=ctypes.CDLL(str(shared))
            allocations=ctypes.c_long.in_dll(native,'allocations'); frees=ctypes.c_long.in_dll(native,'frees')
            for name,args,result in (
                ('at',[ctypes.c_uint64,ctypes.c_uint64,ctypes.c_int64,ctypes.c_int64],ctypes.c_int64),
                ('measured',[ctypes.c_uint64],ctypes.c_uint64),
                ('concatenated',[ctypes.c_uint64,ctypes.c_uint64,ctypes.c_int64,ctypes.c_int64],ctypes.c_int64),
                ('ordered',[],ctypes.c_int64),
            ):
                getattr(native,name).argtypes=args; getattr(native,name).restype=result
            assert native.ordered()==4321
            assert allocations.value==frees.value
            for n in range(11):
                for m in range(11):
                    before=allocations.value
                    assert native.concatenated(n,m,7,-3)==14*n-3*m
                    # Suffix nodes allocate only once. Append adds n prefix nodes, no Nil.
                    assert allocations.value-before==2*n+m+2,(n,m,allocations.value-before,level)
                    assert allocations.value==frees.value
                assert native.measured(n)==2*n
                assert allocations.value==frees.value
                for i in (*range(23),(1<<64)-1):
                    before=allocations.value
                    assert native.at(n,i,7,9)==((7 if i%2==0 else 9) if i<2*n else -1)
                    assert allocations.value-before==3*n+(8 if level=="-O0" else 5),(n,i,allocations.value-before,level)
                    assert allocations.value==frees.value
            for x,y in ((-(1<<63),(1<<63)-1),(-9,0),(0,12)):
                assert native.at(2,0,x,y)==x and native.at(2,3,x,y)==y
                assert allocations.value==frees.value
    for level in ('-O0','-O2'):
        assert command('run',example,level,success=False).returncode==9
    flags=('--lib','--release','--no-verify','--error-format=json'); env={**environment,'JIHOO_NO_ELAB':'1'}
    control=temporary/'concat-control.jh'
    control.write_text(PREFIX+'fn good(xs: ref list.List, ys: list.List) -> list.List { list.append_into(xs, ys) }'+ANCHOR)
    command('check',control,*flags,env=env)
    command('emit-obj',control,*flags,'-o',str(temporary/'concat-control.o'),env=env)
    def rejected(path,blame,expected='type mismatch'):
        obj=temporary/'concat-rejected.o'
        for action,opts in (('check',()),('emit-obj',('-o',str(obj)))):
            result=command(action,path,*flags,*opts,success=False,env=env)
            errors=[d for d in json.loads(result.stderr)['diagnostics'] if d['severity']=='error']
            assert result.returncode==1 and len(errors)==1,result.stderr
            assert errors[0]['kind']=='source' and errors[0]['message']=='core: '+expected,result.stderr
            assert errors[0]['span']['file']==str(blame),result.stderr
        assert not obj.exists()
    for name,(body,expected) in INVALID.items():
        bad=temporary/f'concat-{name}.jh'; bad.write_text(PREFIX+body+ANCHOR)
        rejected(bad,bad,expected)
    module=(root/'lib/dependent/list.jh').read_text()
    broken=temporary/'broken_concat.jh'; importer=temporary/'concat-broken-import.jh'
    importer.write_text('#![dependent_core]\nimport broken_concat\n'+ANCHOR); broken.write_text(module)
    command('check',importer,*flags,env=env)
    command('emit-obj',importer,*flags,'-o',str(temporary/'concat-import-control.o'),env=env)
    for old,new in (
        ('refl(length(ys)), fn(x, rest, ih)', 'refl(0), fn(x, rest, ih)'),
        ('refl(length(append_into(rest, ys)) + 1)', 'ih'),
    ):
        assert module.count(old)==1,old
        broken.write_text(module.replace(old,new)); rejected(importer,broken)
    sized_module=(root/'lib/dependent/sized_list.jh').read_text()
    sized_copy=temporary/'broken_sized_concat.jh'
    importer.write_text('#![dependent_core]\nimport broken_sized_concat\n'+ANCHOR)
    sized_copy.write_text(sized_module)
    command('check',importer,*flags,env=env)
    command('emit-obj',importer,*flags,'-o',str(temporary/'sized-concat-import-control.o'),env=env)
    for old,new in (
        ('                    right_exact,', '                    left_exact,'),
        ('                        left_exact,', '                        right_exact,'),
    ):
        assert sized_module.count(old)==1,old
        sized_copy.write_text(sized_module.replace(old,new)); rejected(importer,sized_copy)
    print('transferring concat: exact indexed-loop erasure, both targets, native O0/O2 order/linear allocation models and 11 intended rejections passed')
