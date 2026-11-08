"""Capacity-aware bulk appends with an inout length postcondition."""
import ctypes
import json
import os
import platform
import re
import shlex
import struct
from core_buffer import COUNTER

PREFIX = '#![dependent_core]\nimport dependent.vec\nimport dependent.vec_bulk\nimport dependent.sized_list\nimport dependent.nat\n'
ANCHOR = '\nexport fn positive_anchor() -> i64 { 0 }\n'
ERASURE = PREFIX + '''
fn total(v: ref vec.Vec) -> i64 {
    fold(vec.len(v), 0, fn(i, p, acc) { acc + vec.get(v, i, p) })
}
export fn extended(cap: u64, n: u64, x: i64) -> i64 {
    var v = vec.with_capacity(cap)
    let empty = vec.clear(&v)
    let xs = alloc(n, x)
    let grown = vec_bulk.extend(&v, n, xs)
    let exact = transport(fn(k) { Eq(vec.len(v), k + n) }, empty, grown)
    total(v)
}
'''
EXTRA = '''
fn digits(v: ref vec.Vec) -> i64 {
    fold(vec.len(v), 0, fn(i, p, acc) { acc * 10 + vec.get(v, i, p) })
}
export fn sum(cap: u64, prefix: u64, n: u64, x: i64, y: i64) -> i64 {
    if_lt(prefix, cap + 1, fn(room) {
        var v = vec.Vec { len: prefix, cap, data: alloc(cap, x), room }
        let xs = alloc(n, y)
        let grown = vec_bulk.extend(&v, n, xs)
        total(v)
    }, -1)
}
export fn capacity(cap: u64, prefix: u64, n: u64) -> u64 {
    if_lt(prefix, cap + 1, fn(room) {
        var v = vec.Vec { len: prefix, cap, data: alloc(cap, 0), room }
        let xs = alloc(n, 0)
        let grown = vec_bulk.extend(&v, n, xs)
        vec.capacity(v)
    }, 999)
}
export fn length(cap: u64, prefix: u64, n: u64) -> u64 {
    if_lt(prefix, cap + 1, fn(room) {
        var v = vec.Vec { len: prefix, cap, data: alloc(cap, 0), room }
        let xs = alloc(n, 0)
        let grown = vec_bulk.extend(&v, n, xs)
        vec.len(v)
    }, 999)
}
fn triple() -> buffer(3) {
    store(store(store(alloc(3, 0), 0, 1, decide_lt(0, 3)), 1, 2, decide_lt(1, 3)), 2, 3, decide_lt(2, 3))
}
export fn ordered(cap: u64) -> i64 {
    if_lt(2, cap + 1, fn(room) {
        var v = vec.Vec { len: 2, cap,
            data: store(store(alloc(cap, 0), 0, 8, lt_le(0, 2, cap, decide_lt(0, 2), room)),
                1, 9, lt_le(1, 2, cap, decide_lt(1, 2), room)), room }
        let xs = triple()
        let grown = vec_bulk.extend(&v, 3, xs)
        digits(v)
    }, -1)
}
export fn retained(cap: u64) -> i64 {
    var v = vec.with_capacity(cap)
    let empty = vec.clear(&v)
    let xs = triple()
    let grown = vec_bulk.extend(&v, 3, xs)
    let three = transport(fn(k) { Eq(vec.len(v), k + 3) }, empty, grown)
    let changed = vec.set(&v, 0, 9,
        nat.rewrite_upper(0, 3, vec.len(v), nat.eq_sym(vec.len(v), 3, three), decide_lt(0, 3)))
    let original = index(xs, 0, decide_lt(0, 3))
    original * 1000 + digits(v)
}
fn build(cap: u64, x: i64) -> vec.Vec {
    var v = vec.with_capacity(cap)
    let xs = alloc(1, x)
    let grown = vec_bulk.extend(&v, 1, xs)
    v
}
export fn released(cap: u64, x: i64) -> i64 { let v = build(cap, x); total(v) }
'''
INVALID = {
    'self-source-alias': ('fn bad(inout v: vec.Vec) -> i64 { match v { vec.Vec { len, cap, data, room } => { let p = vec_bulk.extend(&v, cap, data); 0 } } }','an owned value is used more than once'),
    'wrong-length-contract': ('fn bad(inout v: vec.Vec, n: u64, xs: ref buffer(n)) -> Eq(vec.len(v), vec.len(old(v)) + n + 1) { vec_bulk.extend(&v, n, xs) }','type mismatch'),
    'wrong-source-length': ('fn bad(inout v: vec.Vec, n: u64, xs: ref buffer(n + 1)) -> Eq(vec.len(v), vec.len(old(v)) + n) { vec_bulk.extend(&v, n, xs) }','type mismatch'),
    'stale-read-proof': ('fn bad(inout v: vec.Vec, n: u64, xs: ref buffer(n), i: u64, p: erased(Lt(i, vec.len(v)))) -> i64 { let grown = vec_bulk.extend(&v, n, xs); vec.get(v, i, p) }','type mismatch'),
    'stale-exact-proof': ('fn bad(inout v: vec.Vec, n: u64, xs: ref buffer(n), p: erased(Eq(vec.len(v), 0))) -> Eq(vec.len(v), 0) { let grown = vec_bulk.extend(&v, n, xs); p }','type mismatch'),
    'borrowed-vector': ('fn bad(v: ref vec.Vec, xs: ref buffer(1)) -> i64 { let grown = vec_bulk.extend(&v, 1, xs); 0 }','&v needs a var or an inout parameter'),
    'wrong-buffer-length': ('fn bad(inout v: vec.Vec, xs: ref buffer(3)) -> Eq(vec.len(v), vec.len(old(v)) + 2) { vec_bulk.extend(&v, 2, xs) }','type mismatch'),
    'wrong-capacity-contract': ('fn bad(inout v: vec.Vec, n: u64, xs: ref buffer(n)) -> Eq(vec.capacity(v), vec.capacity(old(v))) { let grown = vec_bulk.extend(&v, n, xs); refl(vec.capacity(v)) }','type mismatch'),
}


def validate_vec_extend(compiler, root, temporary, environment, run):
    def command(action,path,*args,success=True,env=environment):
        return run([compiler,action,str(path),*args],success=success,env=env)
    checked,erased = temporary/'vec-extend-proof.jh',temporary/'vec-extend-erased.jh'
    checked.write_text(ERASURE)
    erased.write_text(ERASURE.replace('    let exact = transport(fn(k) { Eq(vec.len(v), k + n) }, empty, grown)\n',''))
    assert command('emit-mir',checked,'--lib').stdout == command('emit-mir',erased,'--lib').stdout
    example=(root/'examples/core_vec_extend.jh').read_text()
    combined=ERASURE+EXTRA+example[example.index('export fn appended'):example.index('fn main')]
    # Each consumer is checked independently within the core's fixed arena budget.
    exports={}; spans=[]
    for match in re.finditer(r'^export fn (\w+)\(',combined,re.M):
        begin=combined.index('{',match.start()); depth=1; end=begin+1
        while depth:
            depth += (combined[end]=='{') - (combined[end]=='}'); end+=1
        exports[match.group(1)]=combined[match.start():end]
        spans.append((match.start(),end))
    private=combined
    for begin,end in reversed(spans):private=private[:begin]+private[end:]
    sources={}
    for name,body in exports.items():
        path=temporary/f'vec-extend-{name}.jh';path.write_text(private+body)
        command('check',path,'--lib',env={**environment,'JIHOO_LLVM':'/unavailable','JIHOO_CC':'/unavailable'})
        formatted=temporary/f'vec-extend-formatted-{name}.jh';formatted.write_text(command('fmt',path).stdout)
        assert command('fmt',formatted).stdout==formatted.read_text()
        assert command('emit-mir',path,'--lib').stdout==command('emit-mir',formatted,'--lib').stdout
        sources[name]=path
    guide=temporary/'vec-extend-guide.jh'
    guide.write_text(re.search(r'```jihoo\n(.*?)```',(root/'docs/language/vector-extension.md').read_text(),re.S).group(1))
    for level in ('-O0','-O2'):
        assert command('run',guide,level,success=False).returncode==17
    counter=temporary/'vec-extend-counter.c';counter.write_text(COUNTER)
    host='aarch64' if platform.machine() in ('aarch64','arm64') else 'x86_64'
    for target,machine in (('x86_64',62),('aarch64',183)):
        for level in ('-O0','-O2'):
            natives={}
            for name,source in sources.items():
                obj=temporary/f'vec-extend-{name}-{target}{level}.o'
                command('emit-obj',source,'--lib','--target',target,level,'-o',str(obj))
                assert struct.unpack_from('<H',obj.read_bytes(),18)[0]==machine
                if target!=host:continue
                shared=temporary/f'vec-extend-{name}{level}.so'
                run([*shlex.split(os.environ.get('JIHOO_CC','clang')),'-shared','-fPIC',str(obj),str(counter),'-o',str(shared),'-Wl,--wrap=malloc','-Wl,--wrap=free'])
                natives[name]=ctypes.CDLL(str(shared))
            if target!=host:continue
            def call(name,args,expected,allocs=None):
                native=natives[name]
                allocations=ctypes.c_long.in_dll(native,'allocations')
                frees=ctypes.c_long.in_dll(native,'frees')
                fn=getattr(native,name);fn.argtypes=[ctypes.c_uint64]*len(args)
                if name in ('extended','released'):fn.argtypes[-1]=ctypes.c_int64
                if name=='sum':fn.argtypes[-2:]=[ctypes.c_int64,ctypes.c_int64]
                fn.restype=ctypes.c_uint64 if name in ('capacity','length') else ctypes.c_int64
                allocations.value=frees.value=0
                assert fn(*args)==expected,(name,args,expected)
                assert allocations.value==frees.value,(name,args,allocations.value,frees.value)
                if level=='-O0' and allocs is not None:assert allocations.value==allocs,(name,args,allocations.value,allocs)
            for cap in range(8):
                for prefix in range(cap+2):
                    for n in range(6):
                        valid=prefix<=cap;total=prefix+n
                        allocs=4+(total>cap) if valid else 0
                        call('sum',(cap,prefix,n,-3,7),-3*prefix+7*n if valid else -1,allocs)
                        call('capacity',(cap,prefix,n),max(cap,total) if valid else 999,allocs)
                        call('length',(cap,prefix,n),total if valid else 999,allocs)
                call('ordered',(cap,),89123 if cap>=2 else -1)
                call('retained',(cap,),1923)
                for i in (*range(7),(1<<64)-1):call('appended',(cap,i),7 if i<2 else 9 if i<5 else -1)
                for x in (-(1<<63),-1,0,1,(1<<63)-1):call('released',(cap,x),x)
            for n in (0,1,64,256):
                for cap in (0,n,n+1):call('extended',(cap,n,7),n*7,4+(n>cap))
            assert command('run',root/'examples/core_vec_extend.jh',level,success=False).returncode==9
    positive=temporary/'vec-extend-positive.jh';positive.write_text(PREFIX+ANCHOR)
    command('emit-obj',positive,'--lib','-o',str(temporary/'vec-extend-positive.o'))
    def rejected(path,name,expected,importer=None):
        obj=temporary/f'vec-extend-invalid-{name}.o'
        for action,options in (('check',[]),('emit-obj',['-o',str(obj)])):
            result=command(action,importer or path,'--lib','--release','--no-verify','--error-format=json',*options,
                success=False,env={**environment,'JIHOO_NO_ELAB':'1'})
            errors=[d for d in json.loads(result.stderr)['diagnostics'] if d['severity']=='error']
            assert result.returncode==1 and len(errors)==1,(name,result.stderr)
            assert errors[0]['kind']=='source' and errors[0]['message']=='core: '+expected,(name,result.stderr)
            assert errors[0]['span']['file']==str(path) and not obj.exists(),(name,result.stderr)
    for name,(body,expected) in INVALID.items():
        path=temporary/f'vec-extend-invalid-{name}.jh';path.write_text(PREFIX+body+ANCHOR)
        rejected(path,name,expected)
    for name,filename,old,new in (
        ('reuse-length','vec_bulk.jh','len: total,','len: total + 1,'),
        ('reuse-offset','vec_bulk.jh','appended(len, cap, n, data, source, fits)','appended(len + 1, cap, n, data, source, fits)'),
        ('growth-offset','vec_bulk.jh','appended(len, total, n, grown, source, nat.le_refl(total))','appended(len + 1, total, n, grown, source, nat.le_refl(total))'),
        ('postcondition','vec_bulk.jh','refl(total)','refl(total + 1)'),
        ('source-index','vec_bulk.jh','index(source, i, p)','index(source, i + 1, p)'),
    ):
        original=(root/'lib/dependent'/filename).read_text();assert old in original
        module='broken_vec_extend_'+name.replace('-','_')
        path=temporary/f'{module}.jh';path.write_text(original)
        importer=temporary/f'vec-extend-import-{name}.jh';importer.write_text(f'#![dependent_core]\nimport {module}\n'+ANCHOR)
        control=temporary/f'vec-extend-control-{name}.o'
        command('emit-obj',importer,'--lib','--release','--no-verify','-o',str(control),env={**environment,'JIHOO_NO_ELAB':'1'})
        assert control.read_bytes().startswith(b'\x7fELF')
        path.write_text(original.replace(old,new));rejected(path,name,'type mismatch',importer)
    print('vector bulk extension: both targets, inout proof erasure, capacity reuse/growth, ownership and exact rejections passed')
