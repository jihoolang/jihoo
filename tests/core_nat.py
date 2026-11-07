"""Imported natural-index lemmas and structural proofs used by runtime loops."""
import ctypes
import json
import os
import platform
import shlex
import struct

EXTRA = '''
fn accept(a: u64, b: erased(u64), p: erased(Lt(a, b + 1))) -> u64 { a }
export fn erased_trace(a: u64, n: u64, k: u64) -> u64 {
    accept(a, a + n + k, nat.steps_bound(a, a + n + k,
        nat.concatenate(a, a + n, a + n + k, nat.advance(a, n), nat.advance(a + n, k))))
}
export fn lookup(n: u64, i: u64) -> i64 {
    if_eq(3, n, fn(e) {
        if_lt(i, n, fn(p) { index([11, 22, 33], i,
            nat.rewrite_upper(i, n, 3, nat.eq_sym(3, n, e), p)) }, -1)
    }, -2)
}
export fn mirror(i: u64) -> i64 {
    if_lt(i, 3, fn(p) { index([10, 20, 30], sub(3, i + 1, lt_add(i, 3, 1, p)), nat.mirror_lt(i, 3, p)) }, -1)
}
fn difference(n: u64, k: u64, p: erased(Lt(k, n + 1))) -> refine(fn(v) { Eq(v + k, n) }) {
    pack(sub(n, k, p), nat.sub_cancel(n, k, p))
}
export fn subtract(n: u64, k: u64) -> u64 {
    if_lt(k, n, fn(p) { witness(difference(n, k, nat.weaken(k, n, p))) }, 0)
}
'''
REFERENCE = '''#![dependent_core]
fn counted(n: u64, limit: u64) -> refine(fn(c) { Lt(c, n + 1) }) {
    fold(n, fn(k) { refine(fn(c) { Lt(c, k + 1) }) }, pack(0, zero_le(0)),
        fn(i, p, acc) {
            if_lt(i, limit, fn(q) { pack(witness(acc) + 1, lt_add(witness(acc), i + 1, 1, proof(acc))) },
                pack(witness(acc), lt_le(witness(acc), i + 1, i + 2, proof(acc), lt_add(0, 2, i + 1, decide_lt(0, 2)))))
        })
}
export fn count(n: u64, limit: u64) -> u64 { witness(counted(n, limit)) }
export fn slot(limit: u64) -> i64 { let c = counted(4, limit); index([10, 20, 30, 40, 50], witness(c), proof(c)) }
fn main() -> i64 { slot(2) }
export fn erased_trace(a: u64, n: u64, k: u64) -> u64 { a }
export fn lookup(n: u64, i: u64) -> i64 {
    if_eq(3, n, fn(e) { if_lt(i, n, fn(p) {
        index([11, 22, 33], i, transport(fn(m) { Lt(i, m) }, transport(fn(m) { Eq(m, 3) }, e, refl(3)), p))
    }, -1) }, -2)
}
export fn mirror(i: u64) -> i64 {
    if_lt(i, 3, fn(p) { index([10, 20, 30], sub(3, i + 1, lt_add(i, 3, 1, p)),
        lt_add(0, i + 1, sub(3, i + 1, lt_add(i, 3, 1, p)), zero_le(i))) }, -1)
}
export fn subtract(n: u64, k: u64) -> u64 {
    if_lt(k, n, fn(p) { sub(n, k, lt_le(k, n, n + 1, p, lt_add(0, 2, n, decide_lt(0, 2)))) }, 0)
}
'''
# Every invalid helper is checked alongside a valid runtime export.
PREFIX = '#![dependent_core]\nimport dependent.nat\n'
ANCHOR = '\nexport fn harness_anchor() -> i64 { 0 }\n'
INVALID = {
    'false-equality': 'fn bad() -> Eq(1, 2) { nat.eq_trans(1, 1, 2, refl(1), refl(1)) }',
    'wrong-add-equality': 'fn bad() -> Eq(2, 3) { nat.eq_add(1, 1, 1, refl(1)) }',
    'wrong-upper': 'fn bad() -> Lt(0, 2) { nat.rewrite_upper(0, 1, 2, refl(1), decide_lt(0, 1)) }',
    'wrong-lower': 'fn bad() -> Lt(2, 1) { nat.rewrite_lower(0, 2, 1, refl(0), decide_lt(0, 1)) }',
    'strict-from-reflexive': 'fn bad(n: u64) -> Lt(n, n) { nat.le_refl(n) }',
    'wrong-middle': 'fn bad() -> Lt(0, 3) { nat.lt_trans(0, 2, 3, decide_lt(0, 1), decide_lt(2, 3)) }',
    'wrong-le-middle': 'fn bad() -> Lt(0, 4) { nat.le_trans(0, 2, 3, nat.le_refl(0), nat.le_refl(3)) }',
    'false-contradiction': 'fn bad() -> Lt(0, 0) { nat.lt_irrefl(1, nat.le_refl(1)) }',
    'underflow-evidence': 'fn bad() -> Eq(0, 1) { nat.sub_cancel(1, 2, nat.le_refl(2)) }',
    'false-stationary': 'fn bad() -> nat.Steps(2, 1) { nat.stationary(2) }',
    'wrong-successor': 'fn bad() -> nat.Steps(0, 2) { nat.successor(0, 1, nat.stationary(0)) }',
    'wrong-concatenation': 'fn bad() -> nat.Steps(0, 2) { nat.concatenate(0, 1, 2, nat.advance(0, 1), nat.advance(0, 2)) }',
    'reversed-bound': 'fn bad() -> Lt(2, 1) { nat.steps_bound(2, 0, nat.advance(0, 2)) }',
    'wrong-shift': 'fn bad() -> nat.Steps(1, 3) { nat.steps_add(0, 1, 2, nat.advance(0, 1)) }',
    'false-strict-end': 'fn bad() -> Lt(0, 2) { nat.steps_lt(0, 2, 2, nat.advance(0, 2), nat.le_refl(2)) }',
}


def validate_nat(compiler, root, temporary, environment, run):
    def command(action, path, *args, success=True, env=environment):
        return run([compiler, action, str(path), *args], success=success, env=env)
    source, reference = temporary/'nat-library.jh', temporary/'nat-reference.jh'
    example = root/'examples/core_nat.jh'
    source.write_text(example.read_text() + EXTRA)
    reference.write_text(REFERENCE)
    command('check', source, '--lib', env={**environment, 'JIHOO_LLVM':'/unavailable', 'JIHOO_CC':'/unavailable'})
    mir = command('emit-mir', source, '--lib').stdout
    assert mir == command('emit-mir', reference, '--lib').stdout, 'imported structural proofs changed runtime MIR'
    formatted = temporary/'nat-formatted.jh'; formatted.write_text(command('fmt', source).stdout)
    assert command('fmt', formatted).stdout == formatted.read_text()
    assert command('emit-mir', formatted, '--lib').stdout == mir
    host = 'aarch64' if platform.machine() in ('aarch64', 'arm64') else 'x86_64'
    for target, machine in (('x86_64', 62), ('aarch64', 183)):
        for level in ('-O0', '-O2'):
            obj = temporary/f'nat-{target}{level}.o'
            command('emit-obj', source, '--lib', '--target', target, level, '-o', str(obj))
            assert struct.unpack_from('<H', obj.read_bytes(), 18)[0] == machine
            if target != host: continue
            library = temporary/f'nat{level}.so'
            run([*shlex.split(os.environ.get('JIHOO_CC','clang')), '-shared', '-fPIC', str(obj), '-o', str(library)])
            native = ctypes.CDLL(str(library))
            for name, arity, result in (('count',2,ctypes.c_uint64),('slot',1,ctypes.c_int64),('erased_trace',3,ctypes.c_uint64),('lookup',2,ctypes.c_int64),('mirror',1,ctypes.c_int64),('subtract',2,ctypes.c_uint64)):
                fn=getattr(native,name); fn.argtypes,fn.restype=[ctypes.c_uint64]*arity,result
            for n in range(9):
                for limit in range(11): assert native.count(n,limit)==min(n,limit)
            for limit in (0,1,2,3,4,5,(1<<64)-1): assert native.slot(limit)==10*(min(4,limit)+1)
            for a in (0,1,9,(1<<64)-1):
                assert native.erased_trace(a,(1<<64)-1,(1<<64)-1)==a
            for n in range(5):
                for i in range(5): assert native.lookup(n,i)==(-2 if n!=3 else [11,22,33][i] if i<3 else -1)
            for i in range(5): assert native.mirror(i)==([30,20,10][i] if i<3 else -1)
            for n in (0,1,9,(1<<64)-1):
                for k in (0,1,8,(1<<64)-1): assert native.subtract(n,k)==(n-k if k<n else 0)
    for level in ('-O0','-O2'):
        assert command('run', example, level, success=False).returncode==30
    trap=temporary/'nat-runtime-overflow.jh'
    trap.write_text(PREFIX+'fn main() -> i64 { let n: u64 = 18446744073709551615; let p = nat.add_le(n, 1); let value = n + 1; 0 }')
    for level in ('-O0','-O2'):
        assert command('run',trap,level,success=False).returncode==132
    flags=('--lib','--release','--no-verify','--error-format=json')
    env={**environment,'JIHOO_NO_ELAB':'1'}
    control=temporary/'nat-positive-control.jh'
    control.write_text(PREFIX+'fn valid() -> nat.Steps(0, 2) { nat.advance(0, 2) }'+ANCHOR)
    command('check',control,*flags,env=env)
    control_obj=temporary/'nat-positive-control.o'
    command('emit-obj',control,*flags,'-o',str(control_obj),env=env)
    assert control_obj.read_bytes().startswith(b'\x7fELF')
    for name, body in INVALID.items():
        bad=temporary/f'nat-{name}.jh'; bad.write_text(PREFIX+body+ANCHOR)
        obj=temporary/f'nat-{name}.o'
        for action,opts in (('check',()),('emit-obj',('-o',str(obj)))):
            r=command(action,bad,*flags,*opts,success=False,env=env)
            errors=[d for d in json.loads(r.stderr)['diagnostics'] if d['severity']=='error']
            assert r.returncode==1 and len(errors)==1,(name,action,r.stderr)
            assert errors[0]['kind']=='source' and errors[0]['message']=='core: type mismatch',(name,action,r.stderr)
            assert errors[0]['span']['file']==str(bad),(name,action,r.stderr)
        assert not obj.exists(),name
    # All symbolic induction cases must be checked even if the importing
    # program never calls the theorem or constructs that case.
    original=(root/'lib/dependent/nat.jh').read_text()
    mutations=(
        ('fn(x) { le_refl(x) }','fn(x) { zero_le(x) }'),
        ('weaken(x, y + 1, ih)','ih'),
        ('le_trans(x, y, z, ihp, ihq)','ihp'),
        ('stationary(x + k)','stationary(x)'),
    )
    broken=temporary/'broken.jh'
    importer=temporary/'nat-broken-import.jh'
    importer.write_text('#![dependent_core]\nimport broken\n'+ANCHOR)
    broken.write_text(original)
    command('check',importer,*flags,env=env)
    imported_control=temporary/'nat-import-positive-control.o'
    command('emit-obj',importer,*flags,'-o',str(imported_control),env=env)
    assert imported_control.read_bytes().startswith(b'\x7fELF')
    for before,after in mutations:
        assert original.count(before)==1,before
        broken.write_text(original.replace(before,after))
        obj=temporary/'nat-broken-import.o'
        for action,opts in (('check',()),('emit-obj',('-o',str(obj)))):
            r=command(action,importer,*flags,*opts,success=False,env=env)
            errors=[d for d in json.loads(r.stderr)['diagnostics'] if d['severity']=='error']
            assert r.returncode==1 and len(errors)==1,(before,r.stderr)
            assert errors[0]['kind']=='source' and errors[0]['message']=='core: type mismatch',(before,r.stderr)
            assert errors[0]['span']['file']==str(broken),(before,r.stderr)
        assert not obj.exists(),before
    print(f'natural proof library: imported induction/loop invariants, exact MIR erasure, both targets, native boundary values, positive control and {len(INVALID)} intended rejections and 4 unused-induction-case mutations passed')
