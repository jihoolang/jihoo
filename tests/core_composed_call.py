#!/usr/bin/env python3
"""Closed Core programs compose application through resource continuations.
The checked export fixture is compared in full with the Lean example snapshot;
that exporter association is trusted, not general checker/lowering refinement.
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


def source(name, saved, payload, owned, extra, observed):
    chosen = 'observed' if observed else 'saved'
    end = bind('chosen', 'I64', chosen,
               bind('move', '(Buffer 1)', 'final', '(free move chosen)'))
    nested = bind('final', '(Buffer 1)', bind('moved', '(Buffer 1)', 'received', 'moved'), end)
    if owned:
        nested = f'(free copyBack {nested})'
    nested = f'(free restored {nested})'
    if extra:
        # App is below another allocation and free, not merely a top-level wrapper.
        nested = bind('scratch', '(Buffer 1)', '(alloc 1 (int 123))', f'(free scratch {nested})')
    if owned:
        nested = lend('copy', 'observed', 'copyBack', nested)
        consumer = lend('held', 'copy', 'restored', nested, owned=True)
    else:
        consumer = lend('held', 'observed', 'restored', nested)
    body = bind('received', '(Buffer 1)', bind('moved', '(Buffer 1)', 'input', 'moved'), consumer)
    body = bind('held', '(Buffer 1)', f'(alloc 1 (int {payload}))',
                bind('input', '(Buffer 1)', '(alloc 1 (int 7))', body))
    body = bind('saved', 'I64', f'(int {saved})', body)
    count = 2 + owned + extra
    free_order = ([2 + owned] if extra else []) + [0] + ([2] if owned else []) + [1]
    return f'(export {name} I64 {body})\n', payload if observed else saved, count, free_order


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    compiler = str(Path(parser.parse_args().compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='composed-call-') as directory:
        tmp = Path(directory)
        fixture = ROOT / 'tests/core_composed_call.jhc'
        snapshot = json.loads((ROOT / 'tests/core_composed_graph.json').read_text())
        probe = tmp / 'probe'
        command([compiler, 'build', '-O0', '-I', ROOT / 'compiler',
                 ROOT / 'tests/core_linear_graph_probe.jh', '-o', probe])
        exported = subprocess.run([str(probe)], input=fixture.read_text(), capture_output=True,
                                  text=True, timeout=180)
        require(exported.returncode == 0, exported.stderr)
        require(json.loads(exported.stdout) == snapshot,
                'actual checked Core graph differs from full Lean snapshot fixture')
        texts = [fixture.read_text()]
        specs = [('composed', 99, 2, [0, 1])]
        for saved in (37, 99):
            for payload in (7, 37):
                for owned in (False, True):
                    for extra in (False, True):
                        for observed in (False, True):
                            name = f'f{len(specs)}'
                            text, value, count, frees = source(name, saved, payload, owned, extra, observed)
                            texts.append(text); specs.append((name, value, count, frees))
        core = tmp / 'all.jhc'; core.write_text(''.join(texts))
        command([compiler, 'core', 'check', core]); command([compiler, 'core', 'preserves', core])
        counter = tmp / 'counter.c'; counter.write_text(COUNTER)
        cc = shlex.split(os.environ.get('JIHOO_CC', 'clang'))
        cases = 0
        for level in ('-O0', '-O2'):
            obj, library = tmp / f'{level}.o', tmp / f'{level}.so'
            command([compiler, 'core', 'emit-obj', core, level, '-o', obj])
            command([*cc, '-shared', '-fPIC', obj, counter, '-o', library,
                     '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
            native = ctypes.CDLL(str(library))
            stats = {n: ctypes.c_long.in_dll(native, n) for n in
                     ('allocations', 'frees', 'active_count', 'peak', 'bad', 'free_count')}
            freed_ids = (ctypes.c_long * 64).in_dll(native, 'freed_ids')
            for name, value, count, free_order in specs:
                fn = getattr(native, name); fn.argtypes = []; fn.restype = ctypes.c_int64
                # Repeat with allocator address reuse, retaining distinct allocation IDs.
                for _ in range(3):
                    before = stats['allocations'].value, stats['frees'].value
                    stats['peak'].value = stats['free_count'].value = 0
                    require(fn() == value, f'{name}: incorrect saved/read result')
                    delta = stats['allocations'].value-before[0], stats['frees'].value-before[1]
                    require(delta[0] == delta[1] and 0 <= delta[0] <= count,
                            f'{name}: unbalanced lifecycle {delta}')
                    if level == '-O0':
                        require(delta == (count, count) and stats['peak'].value == count,
                                f'{name}: incorrect compositional lifetime')
                        actual = [freed_ids[i]-before[0] for i in range(stats['free_count'].value)]
                        require(actual == free_order, f'{name}: wrong free IDs/order {actual} != {free_order}')
                    require(stats['active_count'].value == 0 and stats['bad'].value == 0,
                            f'{name}: invalid free or leak')
                    cases += 1
        valid = fixture.read_text()
        invalid = {
            'stale-input': ('an owned value is used more than once',
                           valid.replace('(free move chosen)', '(free move (free input chosen))')),
            'lost-result': ('an owned value must be used', valid.replace('(free move chosen)', 'chosen')),
            'stale-frame': ('a lent owner is used exactly once after its lend',
                           valid.replace('(free move chosen)', '(free move (free held chosen))')),
            'scalar-as-owner': ('expected a buffer', valid.replace('(free move chosen)', '(free chosen move)')),
        }
        for name, (diagnostic, text) in invalid.items():
            path = tmp / f'{name}.jhc'; path.write_text(text)
            failed = command([compiler, 'core', 'check', path], success=False)
            require(diagnostic in failed.stderr, f'{name}: unexpected diagnostic: {failed.stderr}')
            obj = tmp / f'{name}.o'; command([compiler, 'core', 'emit-obj', path, '-o', obj], success=False)
            require(not obj.exists(), f'{name}: invalid program emitted object')
        print(f'composed-call: full graph match, {len(specs)} variants, {cases} native lifecycles, {len(invalid)} rejects')


if __name__ == '__main__':
    main()
