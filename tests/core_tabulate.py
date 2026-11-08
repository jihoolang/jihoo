"""Bounded higher-order list construction and direct range conversion."""
import ctypes
import json
import os
import platform
import shlex
import struct
from core_list_map import RECORDER

PREFIX = '#![dependent_core]\nimport dependent.sized_list\nimport dependent.list\n'
ANCHOR = '\nexport fn positive_anchor() -> i64 { 0 }\n'
CHECKED = PREFIX + '''
fn copied(n: u64, source: ref buffer(n)) -> list.List {
    sized_list.into_list(n, sized_list.from_buffer(n, source))
}
export fn total(n: u64, value: i64) -> i64 {
    let source = alloc(n, value)
    let xs = copied(n, source)
    list.sum(xs)
}
'''
REFERENCE = '''#![dependent_core]
import dependent.list
struct Sized { data: list.List }
fn empty() -> Sized { Sized { data: list.List.Nil } }
fn cons(x: i64, xs: Sized) -> Sized {
    match xs { Sized { data } => Sized { data: list.List.Cons(x, data) } }
}
fn tabulate(n: u64, f: fn(i: u64, erased(Lt(i, n))) -> i64) -> Sized {
    fold(n, empty(), fn(i, p, acc) {
        cons(f(sub(n, i + 1, lt_add(i, n, 1, p)),
            lt_add(0, i + 1, sub(n, i + 1, lt_add(i, n, 1, p)), zero_le(i))), acc)
    })
}
fn copied(n: u64, source: ref buffer(n)) -> list.List {
    let xs = tabulate(n, fn(i, p) { index(source, i, p) })
    match xs { Sized { data } => data }
}
export fn total(n: u64, value: i64) -> i64 {
    let source = alloc(n, value)
    let xs = copied(n, source)
    list.sum(xs)
}
'''
EXTRA = '''
fn digits(xs: ref list.List) -> i64 {
    induct(fn(t) { i64 }, 0, fn(x, rest, ih) { x + 10 * ih }, xs)
}
fn ascending() -> buffer(8) {
    fold(8, alloc(8, 0), fn(i, p, acc) { store(acc, i, index([0,1,2,3,4,5,6,7], i, p), p) })
}
fn capture(source: ref buffer(8), offset: u64, count: u64,
    fits: erased(Lt(offset + count, 9))) -> list.List {
    sized_list.into_list(count, sized_list.from_range(8, source, offset, count, fits))
}
export fn selected_range(offset: u64, count: u64) -> i64 {
    let source = ascending()
    if_lt(offset, 9, fn(start) {
        if_lt(count, sub(8, offset, start) + 1, fn(fits) {
            let xs = capture(source, offset, count, lt_add(count, sub(8, offset, start) + 1, offset, fits))
            digits(xs)
        }, -1)
    }, -1)
}
export fn independent() -> i64 {
    let source = ascending()
    let xs = capture(source, 1, 2, decide_lt(3, 9))
    let changed = store(source, 1, 9, decide_lt(1, 8))
    let value = index(changed, 1, decide_lt(1, 8))
    digits(xs) * 100 + value
}
fn released_source() -> list.List {
    let source = ascending()
    capture(source, 1, 2, decide_lt(3, 9))
}
export fn released() -> i64 { let xs = released_source(); digits(xs) }
fn recorded(cap: u64, x: i64) -> i64 {
    let b = alloc(cap, x)
    if_lt(0, cap, fn(p) { index(b, 0, p) }, -1)
}
export fn traced(n: u64, cap: u64) -> i64 {
    if_lt(n, 9, fn(bound) {
        let xs = sized_list.tabulate(n, fn(i, p) {
            recorded(cap, index([0,1,2,3,4,5,6,7], i, lt_le(i, n, 8, p, bound)))
        })
        let ys = sized_list.into_list(n, xs)
        digits(ys)
    }, -1)
}
export fn count(n: u64) -> u64 {
    let xs = sized_list.tabulate(n, fn(i, p) { 7 })
    witness(sized_list.size(n, xs))
}
export fn scalar(n: u64, by: i64) -> i64 {
    let xs = sized_list.tabulate(n, fn(i, p) { by })
    let ys = sized_list.into_list(n, xs)
    list.sum(ys)
}
export fn signed(value: i64) -> i64 {
    let source = alloc(1, value)
    let xs = sized_list.from_buffer(1, source)
    sized_list.head(1, xs, decide_lt(0, 1))
}
'''
INVALID = {
    'wrong-index': ('fn bad(n: u64) -> sized_list.Sized(n + 1) { sized_list.tabulate(n, fn(i, p) { 0 }) }', 'type mismatch'),
    'wrong-callback-result': ('fn bad(n: u64) -> sized_list.Sized(n) { sized_list.tabulate(n, fn(i, p) { i }) }', 'type mismatch'),
    'wrong-callback-bound': ('fn bad(n: u64, f: fn(i: u64, erased(Lt(i + 1, n))) -> i64) -> sized_list.Sized(n) { sized_list.tabulate(n, f) }', 'type mismatch'),
    'out-of-bounds-callback': ('fn bad(source: ref buffer(3)) -> sized_list.Sized(3) { sized_list.tabulate(3, fn(i, p) { index(source, i + 1, p) }) }', 'type mismatch'),
    'consume-captured-owner': ('fn bad(source: buffer(3)) -> sized_list.Sized(3) { sized_list.tabulate(3, fn(i, p) { free(source, 0) }) }', 'a function cannot capture an owned value'),
    'wrong-range-end': ('fn bad(source: ref buffer(3)) -> sized_list.Sized(2) { sized_list.from_range(3, source, 2, 2, decide_lt(3, 4)) }', 'type mismatch'),
    'wrong-buffer-length': ('fn bad(source: ref buffer(3)) -> sized_list.Sized(2) { sized_list.from_buffer(2, source) }', 'type mismatch'),
    'duplicate-result': ('fn bad(n: u64) -> u64 { let xs = sized_list.tabulate(n, fn(i, p) { 0 }); list.into_length(sized_list.into_list(n, xs)) + list.into_length(sized_list.into_list(n, xs)) }', 'an owned value is used more than once'),
}


def validate_tabulate(compiler, root, temporary, environment, run):
    def command(action, path, *args, success=True, env=environment):
        return run([compiler, action, str(path), *args], success=success, env=env)
    checked, reference = temporary/'tabulate-checked.jh', temporary/'tabulate-reference.jh'
    checked.write_text(CHECKED); reference.write_text(REFERENCE)
    assert command('emit-mir', checked, '--lib').stdout == command('emit-mir', reference, '--lib').stdout
    source = temporary/'tabulate.jh'; source.write_text(CHECKED + EXTRA)
    command('check', source, '--lib', env={**environment, 'JIHOO_LLVM':'/unavailable', 'JIHOO_CC':'/unavailable'})
    formatted = temporary/'tabulate-formatted.jh'; formatted.write_text(command('fmt', source).stdout)
    assert command('fmt', formatted).stdout == formatted.read_text()
    assert command('emit-mir', source, '--lib').stdout == command('emit-mir', formatted, '--lib').stdout
    recorder = temporary/'tabulate-recorder.c'; recorder.write_text(RECORDER)
    host = 'aarch64' if platform.machine() in ('aarch64','arm64') else 'x86_64'
    for target, machine in (('x86_64',62),('aarch64',183)):
        for level in ('-O0','-O2'):
            obj = temporary/f'tabulate-{target}{level}.o'
            command('emit-obj', source, '--lib', '--target', target, level, '-o', str(obj))
            assert struct.unpack_from('<H', obj.read_bytes(), 18)[0] == machine
            if target != host: continue
            shared = temporary/f'tabulate{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC','clang')), '-shared', '-fPIC', str(obj), str(recorder), '-o', str(shared), '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
            native = ctypes.CDLL(str(shared))
            allocations = ctypes.c_long.in_dll(native,'allocations')
            frees = ctypes.c_long.in_dll(native,'frees')
            calls = ctypes.c_long.in_dll(native,'calls')
            trace = (ctypes.c_int64 * 64).in_dll(native,'trace')
            def call(name, args, expected, expected_allocations=None):
                fn = getattr(native,name)
                fn.argtypes = [ctypes.c_uint64] * len(args)
                if name in ('total','scalar','signed'): fn.argtypes[-1] = ctypes.c_int64
                fn.restype = ctypes.c_uint64 if name == 'count' else ctypes.c_int64
                allocations.value = frees.value = calls.value = 0
                assert fn(*args) == expected, (name,args,expected)
                assert allocations.value == frees.value, (name,args,allocations.value,frees.value)
                if expected_allocations is not None:
                    assert allocations.value == expected_allocations, (name,args,allocations.value,expected_allocations)
            for n in range(9):
                call('count',(n,),n)
                call('traced',(n,3),sum(i * 10**i for i in range(n)))
                assert calls.value == n and list(trace[:n]) == list(reversed(range(n))), (level, n, list(trace[:n]), calls.value)
                for x in (-7,0,12):
                    call('total',(n,x),n*x,2*n+3 if level=='-O0' else None)
                    call('scalar',(n,x),n*x)
            for offset in range(10):
                for count in range(10):
                    valid = offset <= 8 and count <= 8-offset
                    expected = sum((offset+i)*10**i for i in range(count)) if valid else -1
                    call('selected_range',(offset,count),expected, (2*count+3 if valid else 1) if level=='-O0' else None)
            call('independent',(),2109)
            call('released',(),21)
            for x in (-(1<<63),-1,0,1,(1<<63)-1): call('signed',(x,),x)
            assert command('run',root/'examples/core_tabulate.jh',level,success=False).returncode == 9
    positive = temporary/'tabulate-positive.jh'; positive.write_text(PREFIX + ANCHOR)
    command('emit-obj',positive,'--lib','-o',str(temporary/'tabulate-positive.o'))
    for name,(body,expected) in INVALID.items():
        path = temporary/f'tabulate-invalid-{name}.jh'; path.write_text(PREFIX + body + ANCHOR)
        obj = temporary/f'tabulate-invalid-{name}.o'
        for action,options in (('check',[]),('emit-obj',['-o',str(obj)])):
            result = command(action,path,'--lib','--release','--no-verify','--error-format=json',*options,
                success=False,env={**environment,'JIHOO_NO_ELAB':'1'})
            errors = [d for d in json.loads(result.stderr)['diagnostics'] if d['severity']=='error']
            assert result.returncode == 1 and len(errors) == 1, (name,result.stderr)
            assert errors[0]['kind'] == 'source' and errors[0]['message'] == 'core: ' + expected, (name,result.stderr)
            assert errors[0]['span']['file'] == str(path) and not obj.exists(), (name,result.stderr)
    # Even unused imported definitions must prove their callback and loop indices.
    original = (root/'lib/dependent/sized_list.jh').read_text()
    for name,old,new in (
        ('callback-index','f(sub(n, i + 1, lt_add(i, n, 1, p)), nat.mirror_lt(i, n, p))','f(i + 1, p)'),
        ('loop-index','cons(i, f(sub(n, i + 1, lt_add(i, n, 1, p)), nat.mirror_lt(i, n, p)), acc)','acc'),
        ('range-index','index(source, offset + i, range.offset_lt(n, offset, count, i, fits, p))','index(source, offset + i + 1, range.offset_lt(n, offset, count, i, fits, p))'),
    ):
        assert old in original
        module = 'broken_tabulate_' + name.replace('-','_')
        path = temporary/f'{module}.jh'; path.write_text(original)
        importer = temporary/f'tabulate-import-{name}.jh'; importer.write_text(f'#![dependent_core]\nimport {module}\n'+ANCHOR)
        control = temporary/f'tabulate-control-{name}.o'
        command('emit-obj',importer,'--lib','--release','--no-verify','-o',str(control),
            env={**environment,'JIHOO_NO_ELAB':'1'})
        assert control.read_bytes().startswith(b'\x7fELF')
        path.write_text(original.replace(old,new))
        obj = temporary/f'tabulate-broken-{name}.o'
        for action,options in (('check',[]),('emit-obj',['-o',str(obj)])):
            result = command(action,importer,'--lib','--release','--no-verify','--error-format=json',*options,
                success=False,env={**environment,'JIHOO_NO_ELAB':'1'})
            errors = [d for d in json.loads(result.stderr)['diagnostics'] if d['severity']=='error']
            assert result.returncode == 1 and len(errors) == 1, (name,result.stderr)
            assert errors[0]['kind'] == 'source' and errors[0]['message'] == 'core: type mismatch', (name,result.stderr)
            assert errors[0]['span']['file'] == str(path) and not obj.exists(), (name,result.stderr)
    # A discarded generated list still executes its callback. Empty ones do not.
    trap = '''
fn generate(n: u64, x: i64) -> u64 {
    let xs = sized_list.tabulate(n, fn(i, p) { x + 1 })
    witness(sized_list.size(n, xs))
}
'''
    for n in (0,1,3):
        path = temporary/f'tabulate-trap-{n}.jh'
        path.write_text(PREFIX + trap + f'fn main() -> i64 {{ let ignored = generate({n}, 9223372036854775807); 0 }}')
        for level in ('-O0','-O2'):
            result = command('run',path,level,success=n==0)
            assert result.returncode == (0 if n==0 else 132), (n,level,result.stderr)
    print('indexed tabulation: exact erasure, both targets, callback order, ownership/allocation models and intended rejections passed')
