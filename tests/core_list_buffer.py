"""Structural list-to-buffer transfer and exact contiguous collection output."""
import ctypes
import json
import os
import platform
import re
import shlex
import struct
from core_buffer import COUNTER

PREFIX = '#![dependent_core]\nimport dependent.list\nimport dependent.sized_list\nimport dependent.collect\nimport dependent.vec\n'
ANCHOR = '\nexport fn positive_anchor() -> i64 { 0 }\n'
CHECKED = PREFIX + '''
fn total(n: u64, xs: ref buffer(n)) -> i64 {
    fold(n, 0, fn(i, p, acc) { acc + index(xs, i, p) })
}
export fn copied(n: u64, x: i64) -> i64 {
    let xs = sized_list.repeat(n, x)
    let result: buffer(n) = sized_list.to_buffer(n, xs)
    total(n, result)
}
'''
# Primitive reference has no dependency on private Sized or Bounded evidence.
REFERENCE = """#![dependent_core]
import dependent.list
fn write(cap: erased(u64), xs: ref list.List, start: u64, dest: buffer(cap),
    fits: erased(Lt(start + list.length(xs), cap + 1))) -> buffer(cap) {
    induct(fn(t, offset: u64, acc: buffer(cap), p: erased(Lt(offset + list.length(t), cap + 1))) { buffer(cap) },
        fn(offset, acc, p) { acc },
        fn(x, rest, ih, offset, acc, p) {
            ih(offset + 1, store(acc, offset, x,
                lt_le(offset, offset + list.length(rest) + 1, cap,
                    lt_add(0, list.length(rest) + 1, offset, zero_le(list.length(rest))), p)), p)
        }, xs)(start, dest, fits)
}
fn copy(n: u64, xs: ref list.List, exact: erased(Eq(list.length(xs), n))) -> buffer(n) {
    write(n, xs, 0, alloc(n, 0),
        transport(fn(k) { Lt(k, n + 1) },
            transport(fn(k) { Eq(k, list.length(xs)) }, exact, refl(list.length(xs))),
            lt_add(0, 1, n, decide_lt(0, 1))))
}
"""
ERASURE_BODY = """
fn read(n: u64, xs: ref buffer(n)) -> i64 {
    fold(n, 0, fn(i, p, acc) { acc + index(xs, i, p) })
}
fn copied_list(xs: ref list.List) -> i64 {
    let result: buffer(list.length(xs)) = list.to_buffer(list.length(xs), xs, refl(list.length(xs)))
    read(list.length(xs), result)
}
export fn copied(n: u64, x: i64) -> i64 { let xs = list.repeat(n, x); copied_list(xs) }
"""
ERASURE_SOURCE = PREFIX + ERASURE_BODY
ERASURE_REFERENCE = REFERENCE + ERASURE_BODY.replace('list.to_buffer(', 'copy(')
EXTRA = '''
fn digits(n: u64, xs: ref buffer(n)) -> i64 {
    fold(n, 0, fn(i, p, acc) { acc * 10 + index(xs, i, p) })
}
fn write_range(xs: ref list.List, offset: u64, dest: buffer(8)) -> buffer(8) {
    if_lt(offset, 9, fn(start) {
        if_lt(list.length(xs), sub(8, offset, start) + 1, fn(fits) {
            list.write_into(8, xs, offset, dest,
                lt_add(list.length(xs), sub(8, offset, start) + 1, offset, fits))
        }, dest)
    }, dest)
}
export fn offset_write(offset: u64) -> i64 {
    let xs = list.List.Cons(1, list.List.Cons(2, list.List.Cons(3, list.List.Nil)))
    let result = write_range(xs, offset, alloc(8, 9))
    digits(8, result)
}
export fn empty_write(offset: u64) -> i64 {
    let xs = list.List.Nil
    let result = write_range(xs, offset, alloc(8, 9))
    digits(8, result)
}
export fn independent() -> i64 {
    let xs = sized_list.repeat(3, 7)
    let result: buffer(3) = sized_list.to_buffer(3, xs)
    let changed = store(result, 0, 9, decide_lt(0, 3))
    let first = index(changed, 0, decide_lt(0, 3))
    first * 10 + sized_list.head(3, xs, decide_lt(0, 3))
}
fn released_buffer(n: u64, x: i64) -> buffer(n) {
    let xs = sized_list.repeat(n, x)
    sized_list.to_buffer(n, xs)
}
export fn released(n: u64, x: i64) -> i64 {
    let result = released_buffer(n, x)
    total(n, result)
}
fn chosen(n: u64, limit: u64, x: i64) -> collect.Bounded(n) {
    collect.build(n, fn(i, p) { if_lt(i, limit, fn(q) { collect.Entry.Keep(x) }, collect.Entry.Skip) })
}
fn vector(n: u64, limit: u64, x: i64) -> vec.Vec {
    let xs = chosen(n, limit, x)
    collect.to_vec(n, xs)
}
fn vec_total(v: ref vec.Vec) -> i64 { fold(vec.len(v), 0, fn(i, p, acc) { acc + vec.get(v, i, p) }) }
export fn selected_total(n: u64, limit: u64, x: i64) -> i64 {
    let v = vector(n, limit, x)
    vec_total(v)
}
export fn capacity(n: u64, limit: u64) -> u64 { let v = vector(n, limit, 0); vec.capacity(v) }
export fn length(n: u64, limit: u64) -> u64 { let v = vector(n, limit, 0); vec.len(v) }
fn ghost_length(n: erased(u64), xs: ref collect.Bounded(n)) -> u64 {
    let exact = collect.to_vec_length(n, xs)
    collect.len(n, xs)
}
export fn ghost(n: u64, limit: u64) -> u64 {
    let xs = chosen(n, limit, 0)
    ghost_length(n, xs)
}
export fn signed(x: i64) -> i64 {
    let xs = sized_list.repeat(1, x)
    let result: buffer(1) = sized_list.to_buffer(1, xs)
    index(result, 0, decide_lt(0, 1))
}
'''
INVALID = {
    'wrong-buffer-size': ('fn bad(xs: ref sized_list.Sized(3)) -> buffer(2) { sized_list.to_buffer(3, xs) }','type mismatch'),
    'wrong-source-size': ('fn bad(xs: ref sized_list.Sized(3)) -> buffer(2) { sized_list.to_buffer(2, xs) }','type mismatch'),
    'false-exact-length': ('fn bad(xs: ref list.List) -> buffer(2) { list.to_buffer(2, xs, refl(2)) }','type mismatch'),
    'wrong-destination': ('fn bad(xs: ref list.List, dest: buffer(3), p: erased(Lt(list.length(xs), 3))) -> buffer(2) { list.write_into(2, xs, 0, dest, p) }','type mismatch'),
    'wrong-offset': ('fn bad(xs: ref list.List, dest: buffer(3), p: erased(Lt(list.length(xs), 4))) -> buffer(3) { list.write_into(3, xs, 1, dest, p) }','type mismatch'),
    'duplicate-destination': ('fn bad(xs: ref list.List, dest: buffer(3), p: erased(Lt(list.length(xs), 4))) -> i64 { let ys = list.write_into(3, xs, 0, dest, p); free(dest, 0) }','an owned value is used more than once'),
    'borrowed-destination': ('fn bad(xs: ref list.List, dest: ref buffer(3), p: erased(Lt(list.length(xs), 4))) -> buffer(3) { list.write_into(3, xs, 0, dest, p) }','type mismatch'),
    'false-conversion-length': ('fn bad(n: u64, xs: ref collect.Bounded(n)) -> Eq(vec.len(collect.to_vec(n, xs)), n) { collect.to_vec_length(n, xs) }','type mismatch'),
}


def validate_list_buffer(compiler, root, temporary, environment, run):
    def command(action,path,*args,success=True,env=environment):
        return run([compiler,action,str(path),*args],success=success,env=env)
    checked,reference = temporary/'list-buffer-checked.jh',temporary/'list-buffer-reference.jh'
    checked.write_text(ERASURE_SOURCE); reference.write_text(ERASURE_REFERENCE)
    assert command('emit-mir',checked,'--lib').stdout == command('emit-mir',reference,'--lib').stdout
    sized = temporary/'list-buffer-sized.jh'; sized.write_text(CHECKED)
    sized_mir = command('emit-mir',sized,'--lib').stdout
    # Sized supplies the runtime allocation count, so only the writer requires
    # a structural recursion helper. Ghost tail lengths must not add another.
    assert len(re.findall(r'^fn recursion\.',sized_mir,re.M)) == 1, sized_mir
    assert sized_mir.count('call recursion.') == 2, sized_mir
    source = temporary/'list-buffer.jh'; source.write_text(CHECKED+EXTRA)
    command('check',source,'--lib',env={**environment,'JIHOO_LLVM':'/unavailable','JIHOO_CC':'/unavailable'})
    formatted = temporary/'list-buffer-formatted.jh'; formatted.write_text(command('fmt',source).stdout)
    assert command('fmt',formatted).stdout == formatted.read_text()
    assert command('emit-mir',source,'--lib').stdout == command('emit-mir',formatted,'--lib').stdout
    no_ghost = temporary/'list-buffer-no-ghost.jh'
    no_ghost.write_text((CHECKED+EXTRA).replace('    let exact = collect.to_vec_length(n, xs)\n',''))
    assert command('emit-mir',source,'--lib').stdout == command('emit-mir',no_ghost,'--lib').stdout
    guide = temporary/'list-buffer-guide.jh'
    guide.write_text(re.search(r'```jihoo\n(.*?)```', (root/'docs/language/list-buffer-transfer.md').read_text(), re.S).group(1))
    for level in ('-O0','-O2'):
        assert command('run',guide,level,success=False).returncode == 17
    counter = temporary/'list-buffer-counter.c'; counter.write_text(COUNTER)
    host = 'aarch64' if platform.machine() in ('aarch64','arm64') else 'x86_64'
    for target,machine in (('x86_64',62),('aarch64',183)):
        for level in ('-O0','-O2'):
            obj = temporary/f'list-buffer-{target}{level}.o'
            command('emit-obj',source,'--lib','--target',target,level,'-o',str(obj))
            assert struct.unpack_from('<H',obj.read_bytes(),18)[0] == machine
            if target != host: continue
            shared = temporary/f'list-buffer{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC','clang')),'-shared','-fPIC',str(obj),str(counter),'-o',str(shared),'-Wl,--wrap=malloc','-Wl,--wrap=free'])
            native = ctypes.CDLL(str(shared))
            allocations = ctypes.c_long.in_dll(native,'allocations'); frees = ctypes.c_long.in_dll(native,'frees')
            def call(name,args,expected,allocs=None):
                fn=getattr(native,name);fn.argtypes=[ctypes.c_uint64]*len(args)
                if name in ('copied','released','selected_total','signed'): fn.argtypes[-1]=ctypes.c_int64
                fn.restype=ctypes.c_uint64 if name in ('length','capacity','ghost') else ctypes.c_int64
                allocations.value=frees.value=0
                assert fn(*args)==expected,(name,args,expected)
                assert allocations.value==frees.value,(name,args,allocations.value,frees.value)
                if level=='-O0' and allocs is not None: assert allocations.value==allocs,(name,args,allocations.value,allocs)
            for n in (*range(9),64,256):
                for x in (-7,0,12):
                    call('copied',(n,x),n*x,2*n+3)
                    call('released',(n,x),n*x,2*n+3)
                for limit in (0,1,3,8,256,(1<<64)-1):
                    k=min(n,limit)
                    call('selected_total',(n,limit,7),k*7,3*k+5)
                    call('length',(n,limit),k)
                    call('capacity',(n,limit),k)
                    call('ghost',(n,limit),k,3*k+3)
            for offset in (*range(10),(1<<64)-1):
                values=[9]*8
                if offset<=5: values[offset:offset+3]=[1,2,3]
                call('offset_write',(offset,),int(''.join(map(str,values))),5)
                call('empty_write',(offset,),99999999,2)
            call('independent',(),97)
            for x in (-(1<<63),-1,0,1,(1<<63)-1): call('signed',(x,),x)
            assert command('run',root/'examples/core_list_buffer.jh',level,success=False).returncode==6
    positive=temporary/'list-buffer-positive.jh';positive.write_text(PREFIX+ANCHOR)
    command('emit-obj',positive,'--lib','-o',str(temporary/'list-buffer-positive.o'))
    def rejected(path,name,expected,importer=None):
        obj=temporary/f'list-buffer-invalid-{name}.o'
        for action,options in (('check',[]),('emit-obj',['-o',str(obj)])):
            result=command(action,importer or path,'--lib','--release','--no-verify','--error-format=json',*options,
                success=False,env={**environment,'JIHOO_NO_ELAB':'1'})
            errors=[d for d in json.loads(result.stderr)['diagnostics'] if d['severity']=='error']
            assert result.returncode==1 and len(errors)==1,(name,result.stderr)
            assert errors[0]['kind']=='source' and errors[0]['message']=='core: '+expected,(name,result.stderr)
            assert errors[0]['span']['file']==str(path) and not obj.exists(),(name,result.stderr)
    for name,(body,expected) in INVALID.items():
        path=temporary/f'list-buffer-invalid-{name}.jh';path.write_text(PREFIX+body+ANCHOR)
        rejected(path,name,expected)
    for name,filename,old,new in (
        ('write-index','list.jh','store(acc, offset, x,','store(acc, offset + 1, x,'),
        ('write-step','list.jh','ih(offset + 1, store','ih(offset + 2, store'),
        ('exact-output','sized_list.jh','list.to_buffer(n, data, exact)','list.to_buffer(n + 1, data, exact)'),
        ('vector-length','collect.jh','len: count,','len: count + 1,'),
        ('length-theorem','collect.jh','=> refl(count) }','=> refl(count + 1) }'),
    ):
        original=(root/'lib/dependent'/filename).read_text();assert old in original
        module='broken_list_buffer_'+name.replace('-','_')
        path=temporary/f'{module}.jh';path.write_text(original)
        importer=temporary/f'list-buffer-import-{name}.jh';importer.write_text(f'#![dependent_core]\nimport {module}\n'+ANCHOR)
        control=temporary/f'list-buffer-control-{name}.o'
        command('emit-obj',importer,'--lib','--release','--no-verify','-o',str(control),env={**environment,'JIHOO_NO_ELAB':'1'})
        assert control.read_bytes().startswith(b'\x7fELF')
        path.write_text(original.replace(old,new));rejected(path,name,'type mismatch',importer)
    print('list buffer transfer: exact erasure, both targets, structural copying, ownership, allocation and rejection models passed')
