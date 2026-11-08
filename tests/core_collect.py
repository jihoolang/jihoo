"""Runtime-selected cardinalities checked by an indexed owned accumulator."""
import ctypes
import json
import os
import platform
import re
import shlex
import struct
from core_list_map import RECORDER

PREFIX = '#![dependent_core]\nimport dependent.collect\nimport dependent.list\n'
ANCHOR = '\nexport fn positive_anchor() -> i64 { 0 }\n'
CHECKED = PREFIX + '''
export fn total(n: u64, limit: u64, x: i64) -> i64 {
    let xs = collect.build(n, fn(i, p) {
        if_lt(i, limit, fn(q) { collect.Entry.Keep(x) }, collect.Entry.Skip)
    })
    let ys = collect.into_list(n, xs)
    list.sum(ys)
}
'''
REFERENCE = PREFIX + '''
struct Sized { data: list.List }
struct Bounded { count: u64, data: Sized }
fn cons(x: i64, xs: Sized) -> Sized {
    match xs { Sized { data } => Sized { data: list.List.Cons(x, data) } }
}
fn empty() -> Bounded { Bounded { count: 0, data: Sized { data: list.List.Nil } } }
fn step(entry: collect.Entry, acc: Bounded) -> Bounded {
    match acc {
        Bounded { count, data } => match entry {
            Skip => Bounded { count, data }
            Keep(x) => Bounded { count: count + 1, data: cons(x, data) }
        }
    }
}
fn build(n: u64, f: fn(i: u64, erased(Lt(i, n))) -> collect.Entry) -> Bounded {
    fold(n, empty(), fn(i, p, acc) {
        step(f(sub(n, i + 1, lt_add(i, n, 1, p)),
            lt_add(0, i + 1, sub(n, i + 1, lt_add(i, n, 1, p)), zero_le(i))), acc)
    })
}
fn into_list(xs: Bounded) -> list.List {
    match xs { Bounded { data, .. } => match data { Sized { data } => data } }
}
export fn total(n: u64, limit: u64, x: i64) -> i64 {
    let xs = build(n, fn(i, p) {
        if_lt(i, limit, fn(q) { collect.Entry.Keep(x) }, collect.Entry.Skip)
    })
    let ys = into_list(xs)
    list.sum(ys)
}
'''
EXTRA = '''
fn chosen(n: u64, limit: u64, x: i64) -> collect.Bounded(n) {
    collect.build(n, fn(i, p) {
        if_lt(i, limit, fn(q) { collect.Entry.Keep(x) }, collect.Entry.Skip)
    })
}
export fn count(n: u64, limit: u64) -> u64 { let xs = chosen(n, limit, 7); collect.len(n, xs) }
fn read(n: erased(u64), xs: ref collect.Bounded(n), i: u64) -> i64 {
    if_lt(i, collect.len(n, xs), fn(p) { collect.nth(n, xs, i, p) }, -1)
}
export fn at(n: u64, limit: u64, i: u64, x: i64) -> i64 {
    let xs = chosen(n, limit, x)
    read(n, xs, i)
}
fn digits(xs: ref list.List) -> i64 {
    induct(fn(t) { i64 }, 0, fn(x, rest, ih) { x + 10 * ih }, xs)
}
fn record(cap: u64, x: i64) -> i64 {
    let b = alloc(cap, x)
    if_lt(0, cap, fn(p) { index(b, 0, p) }, -1)
}
export fn traced(n: u64, limit: u64, cap: u64) -> i64 {
    if_lt(n, 9, fn(bound) {
        let xs = collect.build(n, fn(i, p) {
            let x = record(cap, index([0,1,2,3,4,5,6,7], i, lt_le(i, n, 8, p, bound)))
            if_lt(i, limit, fn(q) { collect.Entry.Keep(x) }, collect.Entry.Skip)
        })
        let ys = collect.into_list(n, xs)
        digits(ys)
    }, -1)
}
fn filtered(source: ref buffer(4)) -> collect.Bounded(4) {
    collect.build(4, fn(i, p) {
        if_eq(i, 1, fn(q) { collect.Entry.Skip }, collect.Entry.Keep(index(source, i, p)))
    })
}
fn source() -> buffer(4) {
    fold(4, alloc(4, 0), fn(i, p, acc) { store(acc, i, index([1,2,3,4], i, p), p) })
}
export fn independent() -> i64 {
    let original = source()
    let xs = filtered(original)
    let changed = store(original, 0, 9, decide_lt(0, 4))
    let first = index(changed, 0, decide_lt(0, 4))
    let ys = collect.into_list(4, xs)
    first * 1000 + digits(ys)
}
fn escaped() -> collect.Bounded(4) { let original = source(); filtered(original) }
export fn released() -> i64 {
    let ys = collect.into_list(4, escaped())
    digits(ys)
}
'''
INVALID = {
    'wrong-result-bound': ('fn bad(n: u64) -> collect.Bounded(n + 1) { collect.build(n, fn(i, p) { collect.Entry.Skip }) }', 'type mismatch'),
    'wrong-callback': ('fn bad(n: u64) -> collect.Bounded(n) { collect.build(n, fn(i, p) { 1 }) }', 'type mismatch'),
    'wrong-callback-bound': ('fn bad(n: u64, f: fn(i: u64, erased(Lt(i + 1, n))) -> collect.Entry) -> collect.Bounded(n) { collect.build(n, f) }', 'type mismatch'),
    'captured-owner': ('fn bad(source: buffer(3)) -> collect.Bounded(3) { collect.build(3, fn(i, p) { free(source, collect.Entry.Skip) }) }', 'a function cannot capture an owned value'),
    'upper-is-not-length': ('fn bad(n: u64, xs: ref collect.Bounded(n), i: u64, p: erased(Lt(i, n))) -> i64 { collect.nth(n, xs, i, p) }', 'type mismatch'),
    'strict-upper': ('fn bad(n: u64, xs: ref collect.Bounded(n)) -> Lt(collect.len(n, xs), n) { collect.bound(n, xs) }', 'type mismatch'),
    'private-count': ('fn bad(xs: ref collect.Bounded(3)) -> u64 { match xs { collect.Bounded { count, .. } => count } }', 'private struct field: count'),
    'duplicate-owner': ('fn bad(n: u64, xs: collect.Bounded(n)) -> u64 { list.into_length(collect.into_list(n, xs)) + list.into_length(collect.into_list(n, xs)) }', 'an owned value is used more than once'),
}


def validate_collect(compiler, root, temporary, environment, run):
    def command(action, path, *args, success=True, env=environment):
        return run([compiler, action, str(path), *args], success=success, env=env)
    checked, reference = temporary/'collect-checked.jh', temporary/'collect-reference.jh'
    checked.write_text(CHECKED); reference.write_text(REFERENCE)
    assert command('emit-mir',checked,'--lib').stdout == command('emit-mir',reference,'--lib').stdout
    source = temporary/'collect.jh'
    example = (root/'examples/core_collect.jh').read_text()
    source.write_text(CHECKED + EXTRA + example[example.index('fn pick'):example.index('fn main')])
    command('check',source,'--lib',env={**environment,'JIHOO_LLVM':'/unavailable','JIHOO_CC':'/unavailable'})
    formatted = temporary/'collect-formatted.jh'; formatted.write_text(command('fmt',source).stdout)
    assert command('fmt',formatted).stdout == formatted.read_text()
    assert command('emit-mir',source,'--lib').stdout == command('emit-mir',formatted,'--lib').stdout
    guide = temporary/'collect-guide.jh'
    guide.write_text(re.search(r'```jihoo\n(.*?)```', (root/'docs/language/bounded-collection.md').read_text(), re.S).group(1))
    for level in ('-O0','-O2'):
        assert command('run',guide,level,success=False).returncode == 40
    recorder = temporary/'collect-counter.c'; recorder.write_text(RECORDER)
    host = 'aarch64' if platform.machine() in ('aarch64','arm64') else 'x86_64'
    for target,machine in (('x86_64',62),('aarch64',183)):
        for level in ('-O0','-O2'):
            obj = temporary/f'collect-{target}{level}.o'
            command('emit-obj',source,'--lib','--target',target,level,'-o',str(obj))
            assert struct.unpack_from('<H',obj.read_bytes(),18)[0] == machine
            if target != host: continue
            shared = temporary/f'collect{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC','clang')),'-shared','-fPIC',str(obj),str(recorder),'-o',str(shared),'-Wl,--wrap=malloc','-Wl,--wrap=free'])
            native = ctypes.CDLL(str(shared))
            allocations = ctypes.c_long.in_dll(native,'allocations')
            frees = ctypes.c_long.in_dll(native,'frees')
            calls = ctypes.c_long.in_dll(native,'calls')
            trace = (ctypes.c_int64 * 64).in_dll(native,'trace')
            def call(name,args,expected,count_alloc=None):
                fn = getattr(native,name); fn.argtypes = [ctypes.c_uint64] * len(args)
                if name in ('total','at'): fn.argtypes[-1] = ctypes.c_int64
                fn.restype = ctypes.c_uint64 if name == 'count' else ctypes.c_int64
                allocations.value = frees.value = calls.value = 0
                assert fn(*args) == expected, (name,args,expected)
                assert allocations.value == frees.value, (name,args,allocations.value,frees.value)
                if level == '-O0' and count_alloc is not None:
                    assert allocations.value == count_alloc, (name,args,allocations.value,count_alloc)
            for n in range(9):
                for limit in (*range(10),(1<<64)-1):
                    k = min(n,limit)
                    call('count',(n,limit),k,3*k+3)
                    for x in (-7,0,12): call('total',(n,limit,x),k*x,3*k+3)
                    for i in (*range(k+1),(1<<64)-1): call('at',(n,limit,i,17),17 if i<k else -1)
                    call('traced',(n,limit,3),sum(i*10**i for i in range(k)))
                    assert calls.value == n and list(trace[:n]) == list(reversed(range(n))), (level,n,limit,calls.value,list(trace[:n]))
            for limit in (*range(6),(1<<64)-1):
                call('after_selected',(limit,),10*(min(limit,4)+1))
            call('independent',(),9431)
            call('released',(),431)
            for x in (-(1<<63), (1<<63)-1): call('at',(1,1,0,x),x)
            assert command('run',root/'examples/core_collect.jh',level,success=False).returncode == 40
    positive = temporary/'collect-positive.jh'; positive.write_text(PREFIX + ANCHOR)
    command('emit-obj',positive,'--lib','-o',str(temporary/'collect-positive.o'))
    def rejected(path,name,expected,importer=None):
        obj = temporary/f'collect-invalid-{name}.o'
        for action,options in (('check',[]),('emit-obj',['-o',str(obj)])):
            result = command(action,importer or path,'--lib','--release','--no-verify','--error-format=json',*options,
                success=False,env={**environment,'JIHOO_NO_ELAB':'1'})
            errors = [d for d in json.loads(result.stderr)['diagnostics'] if d['severity']=='error']
            assert result.returncode == 1 and len(errors) == 1, (name,result.stderr)
            assert errors[0]['kind'] == 'source' and errors[0]['message'] == 'core: ' + expected, (name,result.stderr)
            assert errors[0]['span']['file'] == str(path) and not obj.exists(), (name,result.stderr)
    for name,(body,expected) in INVALID.items():
        path = temporary/f'collect-invalid-{name}.jh'; path.write_text(PREFIX+body+ANCHOR)
        rejected(path,name,expected)
    original = (root/'lib/dependent/collect.jh').read_text()
    for name,old,new in (
        ('skip-bound','nat.weaken(count, k + 1, within)','within'),
        ('keep-bound','lt_add(count, k + 1, 1, within)','within'),
        ('keep-length','count: count + 1','count: count'),
        ('callback-index','f(sub(n, i + 1, lt_add(i, n, 1, p)), nat.mirror_lt(i, n, p))','f(i + 1, p)'),
    ):
        assert old in original
        module = 'broken_collect_' + name.replace('-','_')
        path = temporary/f'{module}.jh'; path.write_text(original)
        importer = temporary/f'collect-import-{name}.jh'; importer.write_text(f'#![dependent_core]\nimport {module}\n'+ANCHOR)
        control = temporary/f'collect-control-{name}.o'
        command('emit-obj',importer,'--lib','--release','--no-verify','-o',str(control),env={**environment,'JIHOO_NO_ELAB':'1'})
        assert control.read_bytes().startswith(b'\x7fELF')
        path.write_text(original.replace(old,new))
        rejected(path,name,'type mismatch',importer)
    for n in (0,1,3):
        path = temporary/f'collect-trap-{n}.jh'
        path.write_text(PREFIX + '''
fn invoke(n: u64, x: i64) -> u64 {
    let xs = collect.build(n, fn(i, p) { let value = x + 1; collect.Entry.Skip })
    collect.len(n, xs)
}
''' + f'fn main() -> i64 {{ let ignored = invoke({n}, 9223372036854775807); 0 }}')
        for level in ('-O0','-O2'):
            result = command('run',path,level,success=n==0)
            assert result.returncode == (0 if n==0 else 132), (n,level,result.stderr)
    print('bounded collection: exact erasure, both targets, variable cardinality, effects, ownership and intended rejections passed')
