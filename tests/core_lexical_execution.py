#!/usr/bin/env python3
"""Native lexical captures survive consumed slots, shadowing and Lend aliases.
There is no compiler partition-plan input. Ownership/borrow checks and native
allocation lifetimes are observed; erased leases have no runtime counter here.
The composed graph exporter association remains separately trusted.
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
from core_mixed_lend import lend
from core_owned_call import COUNTER
from core_scoped_lend import command, require

ROOT = Path(__file__).resolve().parent.parent


def source(name, owned, original, depth, result):
    # A consumed owner slot sits between retained scalar/owner captures.
    chosen = ('moved' if original else 'restored')
    result_name = {'saved': 'saved', 'read': 'observed', 'shadow': 'x'}[result]
    tail = f'(free final {result_name})'
    if owned:
        tail = f'(free final (free {"copy" if original else "copyBack"} {result_name}))'
    nested = bind('final', '(Buffer 1)', bind('transfer', '(Buffer 1)', chosen, 'transfer'), tail)
    for i in range(depth):
        nested = bind('pad', 'I64', f'(int {100+i})', nested)
    if owned:
        nested = lend('copy', 'observed', 'copyBack', nested)
        body = lend('moved', 'copy', 'restored', nested, owned=True)
    else:
        body = lend('moved', 'observed', 'restored', nested)
    body = bind('x', 'I64', 'c', body)  # Shadows the earlier scalar, not saved.
    body = bind('moved', '(Buffer 1)', bind('transfer', '(Buffer 1)', 'owner', 'transfer'), body)
    body = f'(free junk {body})'
    body = bind('owner', '(Buffer 1)', '(alloc 1 b)',
                bind('junk', '(Buffer 1)', '(alloc 1 c)', body))
    body = bind('x', 'I64', 'a', bind('saved', 'I64', 'x', body))
    return (f'(export {name} (pi a I64 (pi b I64 (pi c I64 I64))) '
            f'(lam a I64 (lam b I64 (lam c I64 {body}))))\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    compiler = str(Path(parser.parse_args().compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='lexical-execution-') as directory:
        tmp = Path(directory)
        fixture = ROOT / 'tests/core_composed_call.jhc'
        probe = tmp / 'probe'
        command([compiler, 'build', '-O0', '-I', ROOT/'compiler',
                 ROOT/'tests/core_linear_graph_probe.jh', '-o', probe])
        exported = subprocess.run([str(probe)], input=fixture.read_text(), text=True,
                                  capture_output=True, timeout=180)
        require(exported.returncode == 0, exported.stderr)
        require(json.loads(exported.stdout) == json.loads((ROOT/'tests/core_composed_graph.json').read_text()),
                'retained composed Core graph does not match the full formal snapshot')
        texts, specs = [fixture.read_text()], []
        for owned in (False, True):
            for original in (False, True):
                for depth in (0, 2, 5):
                    for result in ('saved', 'read', 'shadow'):
                        name = f'f{len(specs)}'
                        texts.append(source(name, owned, original, depth, result))
                        specs.append((name, owned, result))
        core = tmp/'lexical.jhc'; core.write_text(''.join(texts))
        command([compiler, 'core', 'check', core]); command([compiler, 'core', 'preserves', core])
        counter = tmp/'counter.c'; counter.write_text(COUNTER)
        cc = shlex.split(os.environ.get('JIHOO_CC', 'clang'))
        cases = 0
        for level in ('-O0', '-O2'):
            obj, library = tmp/f'{level}.o', tmp/f'{level}.so'
            command([compiler, 'core', 'emit-obj', core, level, '-o', obj])
            command([*cc, '-shared', '-fPIC', obj, counter, '-o', library,
                     '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
            native = ctypes.CDLL(str(library))
            stats = {key: ctypes.c_long.in_dll(native, key) for key in
                     ('allocations', 'frees', 'active_count', 'peak', 'bad', 'free_count')}
            freed_ids = (ctypes.c_long * 64).in_dll(native, 'freed_ids')
            fixture_fn = native.composed; fixture_fn.argtypes=[]; fixture_fn.restype=ctypes.c_int64
            require(fixture_fn() == 99, 'closed composed fixture differs from formal result')
            require(stats['active_count'].value == 0 and stats['bad'].value == 0,
                    'closed composed fixture leaked or double-freed')
            for name, owned, result in specs:
                fn=getattr(native, name); fn.argtypes=[ctypes.c_int64]*3; fn.restype=ctypes.c_int64
                for a,b,c in ((99,7,37), (11,37,99), (7,7,7), (-9,-7,42), (0,0,0)):
                    before=stats['allocations'].value,stats['frees'].value
                    stats['peak'].value=stats['free_count'].value=0
                    expected={'saved':a,'read':b,'shadow':c}[result]
                    require(fn(a,b,c)==expected, f'{name}: capture changed after consumed slot or shadowing')
                    count=3 if owned else 2
                    delta=stats['allocations'].value-before[0],stats['frees'].value-before[1]
                    require(delta[0]==delta[1] and 0<=delta[0]<=count, f'{name}: lifecycle {delta}')
                    if level=='-O0':
                        require(delta==(count,count) and stats['peak'].value==2,
                                f'{name}: consumed slot revived or borrow lifetime changed')
                        actual=[freed_ids[i]-before[0] for i in range(stats['free_count'].value)]
                        expected_ids=[1,0,2] if owned else [1,0]
                        require(actual==expected_ids, f'{name}: allocation identity order {actual} != {expected_ids}')
                    require(stats['active_count'].value==0 and stats['bad'].value==0,
                            f'{name}: invalid release or leak')
                    cases+=1
        valid=source('bad',False,True,2,'saved')
        invalid={
            'consumed-original': ('an owned value is used more than once',
                valid.replace('(free final saved)', '(free final (free owner saved))')),
            'consumed-junk': ('an owned value is used more than once',
                valid.replace('(free final saved)', '(free final (free junk saved))')),
            'lend-alias-duplicated': ('a lent owner is used exactly once after its lend',
                valid.replace('(free final saved)', '(free final (free restored saved))')),
            'shadow-is-not-owner': ('expected a buffer',
                valid.replace('(free final saved)', '(free x (free final saved))')),
            'lost-moved-owner': ('an owned value must be used',
                valid.replace('(free final saved)', 'saved')),
        }
        escape = bind('owner', '(Buffer 1)', '(alloc 1 (int 7))',
                      bind('junk', '(Buffer 1)', '(alloc 1 (int 37))',
                           '(free junk (lend owner (lam r (Ref (Buffer 1)) r) '
                           '(lam escaped (Ref (Buffer 1)) (lam restored (Buffer 1) '
                           '(free restored (int 0))))))'))
        invalid['borrow-through-consumed-context'] = (
            'a borrow cannot outlive its lend', f'(export bad I64 {escape})')
        for name,(diagnostic,text) in invalid.items():
            path=tmp/f'{name}.jhc';path.write_text(text)
            rejected=command([compiler,'core','check',path],success=False)
            require(diagnostic in rejected.stderr, f'{name}: unexpected diagnostic: {rejected.stderr}')
            obj=tmp/f'{name}.o';command([compiler,'core','emit-obj',path,'-o',obj],success=False)
            require(not obj.exists(), f'{name}: invalid source emitted an object')
        print(f'lexical-execution: full graph match, {len(specs)} variants, {cases} native lifecycles, {len(invalid)} rejects')


if __name__=='__main__':
    main()
