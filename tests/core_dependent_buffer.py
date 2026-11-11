#!/usr/bin/env python3
"""A single checked dynamic Buffer(n) graph runs at multiple runtime lengths.
Runtime U64 length/index arguments are distinct from erased proof and I64 payload.
Native evidence and graph-view checks are not a general lowering proof.
"""
import argparse
import ctypes
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
from core_linear_heap import bind
from core_owned_call import COUNTER
from core_scoped_lend import command, require

ROOT = Path(__file__).resolve().parent.parent
SIZED_COUNTER = COUNTER.replace('long freed_ids[64];',
    'long freed_ids[64]; long request_count; size_t request_sizes[64];').replace(
    'void *p = __real_malloc(n);',
    'if (request_count < 64) request_sizes[request_count++] = n; else bad++;\n    void *p = __real_malloc(n);')

def source(name, copy=False, original=False):
    ty='(Buffer savedN)'
    read='(index r k bound)'
    if copy:
        after='(free first (lend copied (lam r (Ref (Buffer savedN)) (index r k bound)) (lam observed I64 (lam last (Buffer savedN) (free last observed)))))'
        access=f'(lend moved (lam r (Ref (Buffer savedN)) (alloc savedN {read})) (lam copied {ty} (lam first {ty} {after})))'
    else:
        owner='moved' if original else 'first'
        again=f'(lend handed (lam r (Ref (Buffer savedN)) {read}) (lam observed I64 (lam last {ty} (free last observed))))'
        after=bind('handed',ty,bind('transfer',ty,owner,'transfer'),again)
        access=f'(lend moved (lam r (Ref (Buffer savedN)) {read}) (lam ignored I64 (lam first {ty} {after})))'
    body=f'(if-lt k savedN bound {access} (free moved (int 99)))'
    body=bind('n','U64','shadow',bind('i','U64','shadow',body))
    body=bind('moved',ty,bind('transfer',ty,'buffer','transfer'),body)
    body=bind('buffer',ty,'(alloc savedN value)',body)
    body=bind('savedN','U64','n',bind('k','U64','i',body))
    return f'(export {name} (pi n U64 (pi i U64 (pi value I64 (pi shadow U64 I64)))) (lam n U64 (lam i U64 (lam value I64 (lam shadow U64 {body})))))\n'

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler',required=True)
    compiler=str(Path(parser.parse_args().compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='dependent-buffer-') as directory:
        tmp=Path(directory)
        fixture=ROOT/'tests/core_dependent_buffer.jhc'
        require(fixture.read_text()==source('dependent'), 'representative dynamic source fixture drift')
        probe=tmp/'probe'
        command([compiler,'build','-O0','-I',ROOT/'compiler',ROOT/'tests/core_linear_graph_probe.jh','-o',probe])
        exported=subprocess.run([str(probe)],input=fixture.read_text(),capture_output=True,text=True,timeout=180)
        require(exported.returncode==0,exported.stderr)
        graph=json.loads(exported.stdout)
        nodes=graph[3]; root=graph[1]
        for expected in ('u64','u64','i64','u64'):
            lam=nodes[root]
            require(lam[0]=='lam' and lam[1]==0 and nodes[lam[2]]==[expected],
                    f'runtime parameter type {expected} was erased, opaque or confused: {lam}')
            root=lam[3]
        require(any(node[0]=='alloc' and nodes[node[1]][0]=='var' for node in nodes),
                'fixture lost its runtime-dependent allocation length')
        exact=ROOT/'tests/core_dependent_index.jhc'
        exact_export=subprocess.run([str(probe)],input=exact.read_text(),capture_output=True,text=True,timeout=180)
        require(exact_export.returncode==0,exact_export.stderr)
        require(json.loads(exact_export.stdout)==json.loads((ROOT/'tests/core_dependent_index.json').read_text()),
                'full checked dynamic graph differs from exact formal fixture')
        specs=[('dependent',False,False),('original',False,True),('copied',True,False)]
        text=''.join(source(*spec) for spec in specs)+exact.read_text()
        specs.append(('dynamic',False,False))
        core=tmp/'all.jhc';core.write_text(text)
        command([compiler,'core','check',core]);command([compiler,'core','preserves',core])
        counter=tmp/'counter.c';counter.write_text(SIZED_COUNTER)
        cc=shlex.split(os.environ.get('JIHOO_CC','clang'))
        cases=0
        inputs=((0,0,0,3),(0,(1<<64)-1,-7,0),(1,0,11,0),(1,1,22,9),
                (2,1,-9,31),(4,3,37,1),(4,1,99,0),(4,4,9,2),
                (7,6,-11,1),(7,(1<<64)-1,44,0),(64,63,17,3))
        for level in ('-O0','-O2'):
            obj,library=tmp/f'{level}.o',tmp/f'{level}.so'
            command([compiler,'core','emit-obj',core,level,'-o',obj])
            command([*cc,'-shared','-fPIC',obj,counter,'-o',library,
                     '-Wl,--wrap=malloc','-Wl,--wrap=free'])
            native=ctypes.CDLL(str(library))
            stats={key:ctypes.c_long.in_dll(native,key) for key in
                   ('allocations','frees','active_count','peak','bad','free_count','request_count')}
            frees=(ctypes.c_long*64).in_dll(native,'freed_ids')
            sizes=(ctypes.c_size_t*64).in_dll(native,'request_sizes')
            for name,copy,_ in specs:
                fn=getattr(native,name)
                fn.argtypes=[ctypes.c_uint64,ctypes.c_uint64,ctypes.c_int64]
                if name!='dynamic':
                    fn.argtypes=fn.argtypes+[ctypes.c_uint64]
                fn.restype=ctypes.c_int64
                for n,i,value,shadow in inputs:
                    for _ in range(3):
                        before=stats['allocations'].value,stats['frees'].value
                        stats['peak'].value=stats['free_count'].value=stats['request_count'].value=0
                        expected=value if i<n else 99
                        args=(n,i,value) if name=='dynamic' else (n,i,value,shadow)
                        require(fn(*args)==expected,
                                f'{name}: dynamic n={n}/i={i} or captured length was misinterpreted')
                        count=2 if copy and i<n else 1
                        delta=stats['allocations'].value-before[0],stats['frees'].value-before[1]
                        require(delta[0]==delta[1] and 0<=delta[0]<=count,f'{name}: lifecycle {delta}')
                        if level=='-O0':
                            require(delta==(count,count) and stats['peak'].value==count,
                                    f'{name}: dynamic buffer lifetime')
                            actual=[frees[j]-before[0] for j in range(stats['free_count'].value)]
                            require(actual==list(range(count)),f'{name}: wrong owner order {actual}')
                            requested=[sizes[j] for j in range(stats['request_count'].value)]
                            require(requested==[8*(n+1)]*count,
                                    f'{name}: wrong dynamic allocation layout {requested}, n={n}')
                        require(stats['active_count'].value==0 and stats['bad'].value==0,
                                f'{name}: invalid release/leak')
                        cases+=1
        invalid={
            'mismatched-length': ('type mismatch',
                '(def bad (pi n U64 (Buffer 1)) (lam n U64 (alloc n (int 7))))'),
            'signed-runtime-length': ('type mismatch',
                '(def bad (pi n I64 I64) (lam n I64 (free (alloc n (int 7)) (int 0))))'),
            'erased-runtime-length': ('erased value used at runtime',
                '(def bad (pi0 n U64 I64) (lam0 n U64 (free (alloc n (int 7)) (int 0))))'),
            'wrong-index-evidence': ('type mismatch',
                source('bad').replace('(index r k bound)','(index r savedN bound)')),
            'out-of-range-evidence': ('type mismatch',
                '(def bad I64 (app (lam b (Buffer 2) (load b 2 (decide-lt 2 3) '
                '(lam x I64 (lam returned (Buffer 2) (free returned x))))) (alloc 2 (int 7))))'),
        }
        for name,(diagnostic,text) in invalid.items():
            path=tmp/f'{name}.jhc';path.write_text(text)
            failed=command([compiler,'core','check',path],success=False)
            require(diagnostic in failed.stderr,f'{name}: unexpected diagnostic: {failed.stderr}')
            obj=tmp/f'{name}.o';command([compiler,'core','emit-obj',path,'-o',obj],success=False)
            require(not obj.exists(),f'{name}: invalid program emitted object')
        print(f'dependent-buffer: runtime U64 graph, {len(specs)} variants, {cases} native lifecycles, {len(invalid)} rejects')


if __name__=='__main__':
    main()
