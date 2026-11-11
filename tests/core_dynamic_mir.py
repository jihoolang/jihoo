#!/usr/bin/env python3
"""Full native dynamic MIR association, strict admission and native ABI tests.
The proof models nonnegative I64 payloads only. Negative payload cases below
are separate native evidence and do not enlarge the formal theorem's scope.
"""
import argparse
import copy
import ctypes
import json
import os
from pathlib import Path
import shlex
import tempfile
from core_scoped_graph import ROOT, run, require
from core_dependent_buffer import SIZED_COUNTER
from core_mir_callers import single


def execute(snapshot, n, i, value):
    """Independent bounded interpreter used for mutation diagnostics, not proof."""
    schema, arguments, types, blocks = snapshot
    require(schema == 2 and len(arguments) == 3, 'entry schema')
    locals_ = [None] * len(types)
    for slot, v in zip(arguments, (n, i, value)):
        locals_[slot] = v
    cells = {}
    size = None
    live = False
    allocated = freed = 0

    def read(place):
        slot, deref = place
        v = locals_[slot]
        require(v is not None, 'uninitialized local')
        if deref:
            require(live and isinstance(v, tuple) and 0 <= v[1] < size,
                    'invalid read')
            require(v[1] in cells, 'uninitialized read')
            return cells[v[1]]
        return v

    def op(operand):
        return read(operand[1]) if operand[0] == 'copy' else operand[2]

    def write(place, value):
        slot, deref = place
        if deref:
            p = locals_[slot]
            require(live and isinstance(p, tuple) and 0 <= p[1] < size,
                    'invalid store')
            cells[p[1]] = value
        else:
            locals_[slot] = value

    pc = 0
    for _ in range(4*n + 30):
        statements, term = blocks[pc]
        for place, rhs in statements:
            kind = rhs[0]
            a = op(rhs[1])
            if kind == 'use': result = a
            elif kind == 'cast': result = 1 if isinstance(a, tuple) else a
            else:
                b = op(rhs[2])
                if kind == 'offset': result = (a[0], a[1] + b)
                elif kind == 'mul': result = a*b
                elif kind == 'add': result = a+b
                elif kind == 'lt': result = int(a < b)
                elif kind == 'ne': result = int(a != b)
                else: raise RuntimeError('unsupported operation')
            write(place, result)
        kind = term[0]
        if kind == 'return':
            require(not live and allocated == freed == 1, 'lifecycle')
            return locals_[0]
        if kind == 'goto': pc = term[1]
        elif kind == 'switch':
            pc = dict(term[2]).get(op(term[1]), term[3])
        elif kind == 'assert':
            require(op(term[1]), 'failed assertion')
            pc = term[2]
        elif kind == 'malloc':
            require(not live, 'duplicate allocation')
            size = op(term[1]) // 8
            live = True
            allocated += 1
            write(term[2], (allocated, 0))
            pc = term[3]
        elif kind == 'free':
            require(live and op(term[1]) == (allocated, 0), 'invalid free')
            live = False
            freed += 1
            write(term[2], 0)
            pc = term[3]
        else: raise RuntimeError('unsupported terminator')
    raise RuntimeError('execution fuel exhausted')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    args = parser.parse_args()
    source = (ROOT/'tests/core_dependent_index.jhc').read_text()
    fixture = json.loads((ROOT/'tests/core_dynamic_mir.json').read_text())
    with tempfile.TemporaryDirectory(prefix='dynamic-mir-') as directory:
        tmp = Path(directory)
        probe = tmp/'probe'
        built = run([args.compiler, 'build', '-O0', '-I', 'compiler',
                     'tests/core_mir_probe.jh', '-o', probe])
        require(built.returncode == 0, built.stderr)
        exported = run([probe], source)
        require(exported.returncode == 0, exported.stderr)
        require(json.loads(exported.stdout) == fixture, 'complete dynamic MIR fixture drift')
        closed = run([probe], single())
        require(closed.returncode == 0, closed.stderr)
        require(json.loads(closed.stdout) == json.loads((ROOT/'tests/core_mir_single.json').read_text()),
                'closed schema1 compatibility drift')
        invalid = (
            '(export bad (pi n U64 I64) (lam n U64 (int 0)))',
            '(export bad (pi n I64 (pi i U64 (pi v I64 I64))) '
            '(lam n I64 (lam i U64 (lam v I64 v))))',
            '(export bad (pi n U64 (pi v I64 (pi i U64 I64))) '
            '(lam n U64 (lam v I64 (lam i U64 v))))',
        )
        for text in invalid:
            result = run([probe], text)
            require(result.returncode != 0 and 'entry signature' in result.stderr,
                    f'unsupported signature was not rejected: {result.stderr}')

        # Exercise the validation guards on malformed internal metadata. These
        # test-only injected exporter variants never alter compiler sources.
        original = (ROOT/'tests/core_mir_probe.jh').read_text()
        anchor = '    var found = false'
        for name, edit in (
            ('argc', 'body.arg_count = 2'),
            ('local', 'body.locals[1].ty = types.I64'),
            ('kind', 'body.locals[1].kind = mir.LocalKind.Temp'),
        ):
            injected = tmp/f'{name}.jh'
            injected.write_text(original.replace(anchor,
                '    match &p.fns[0].body { Some(body) => { ' + edit +
                ' }, None => {} }\n' + anchor))
            malformed = tmp/name
            result = run([args.compiler, 'build', '-O0', '-I', 'compiler',
                          injected, '-o', malformed])
            require(result.returncode == 0, result.stderr)
            result = run([malformed], source)
            require(result.returncode != 0 and 'argument/local mismatch' in result.stderr,
                    f'{name}: malformed metadata was not rejected: {result.stderr}')

        cases = [(0, 0, 0), (0, (1<<64)-1, 11), (1, 0, 11),
                 (1, 1, 37), (2, 1, 0), (7, 6, (1<<63)-1),
                 (64, 63, 17), (4095, 4094, 37), (4095, 4095, 11),
                 (4095, (1<<64)-1, 0)]
        for n, i, value in cases:
            require(execute(fixture, n, i, value) == (value if i < n else 99),
                    'independent dynamic execution mismatch')

        mutations = []
        def mutate(name, edit):
            changed = copy.deepcopy(fixture)
            edit(changed)
            require(changed != fixture, f'ineffective mutation {name}')
            mutations.append((name, changed))
        mutate('argument-order', lambda s: s.__setitem__(1, [2,1,3]))
        mutate('argument-slot', lambda s: s.__setitem__(1, [1,2,4]))
        mutate('argument-type', lambda s: s[2].__setitem__(3, 'u64'))
        mutate('loop-bound', lambda s: s[3][3][0][0][1].__setitem__(2, ['copy',[2,0]]))
        mutate('offset', lambda s: s[3][6][0][1][1].__setitem__(2, ['copy',[1,0]]))
        mutate('allocation-extent', lambda s: s[3][0][0][1][1].__setitem__(2, ['int','u64',0]))
        mutate('free-target', lambda s: s[3][6][1].__setitem__(1, ['copy',[14,0]]))
        mutate('missing-store', lambda s: s[3][4][0].pop(1))
        mutate('wrong-result', lambda s: s[3][10][0][0][1].__setitem__(1, ['int','i64',98]))
        # Execute safety-relevant corruptions independently of exact matching.
        for name, changed in mutations:
            if name not in ('loop-bound', 'offset', 'free-target', 'missing-store'): continue
            failed = False
            try: execute(changed, 3, 1, 37)
            except RuntimeError: failed = True
            require(failed, f'{name}: independent execution should fail')

        graph_probe = tmp/'graph-probe'
        built = run([args.compiler, 'build', '-O0', '-I', 'compiler',
                     'tests/core_linear_graph_probe.jh', '-o', graph_probe])
        require(built.returncode == 0, built.stderr)
        exported_graph = run([graph_probe], source)
        require(exported_graph.returncode == 0, exported_graph.stderr)
        graph = json.loads(exported_graph.stdout)
        require(graph == json.loads((ROOT/'tests/core_dependent_index.json').read_text()),
                'complete dynamic Core graph fixture drift')
        def check(envelope, want=True, raw=False):
            payload = envelope if raw else json.dumps(envelope, separators=(',', ':'))
            result = run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run',
                          'CheckDynamicMir.lean'], payload, ROOT/'proofs')
            require((result.returncode == 0) == want,
                    f'dynamic admission expected {want}: {result.stdout} {result.stderr}')
            require(('dynamic-mir accepted' in result.stdout) if want else
                    ('dynamic-mir rejected:' in result.stderr), 'unexpected checker path')
        envelope = [1, graph, fixture]
        check(envelope)
        for name, changed in mutations:
            check([1, graph, changed], False)
        wrong_graph = copy.deepcopy(graph)
        wrong_graph[1] = wrong_graph[2]
        check([1, wrong_graph, fixture], False)
        wrong_graph = copy.deepcopy(graph)
        wrong_graph[3][0] = ['i64']
        check([1, wrong_graph, fixture], False)
        check([2, graph, fixture], False)
        check(envelope + [0], False)
        check(json.dumps(envelope) + ' garbage', False, raw=True)
        check(' ' * (8*1024*1024+1), False, raw=True)

        core = tmp/'dynamic.jhc'; core.write_text(source)
        counter = tmp/'counter.c'; counter.write_text(SIZED_COUNTER)
        cc = shlex.split(os.environ.get('JIHOO_CC', 'clang'))
        native_cases = cases + [(1,0,-1), (2,1,-(1<<63)), (4095,4094,-37), (0,0,-7)]
        count = 0
        for level in ('-O0', '-O2'):
            obj, library = tmp/f'{level}.o', tmp/f'{level}.so'
            result = run([args.compiler,'core','emit-obj',core,level,'-o',obj])
            require(result.returncode == 0, result.stderr)
            result = run([*cc,'-shared','-fPIC',obj,counter,'-o',library,
                          '-Wl,--wrap=malloc','-Wl,--wrap=free'])
            require(result.returncode == 0, result.stderr)
            native = ctypes.CDLL(str(library))
            fn = native.dynamic
            fn.argtypes = [ctypes.c_uint64,ctypes.c_uint64,ctypes.c_int64]
            fn.restype = ctypes.c_int64
            stats = {key: ctypes.c_long.in_dll(native,key) for key in
                     ('allocations','frees','active_count','bad','request_count','free_count')}
            sizes = (ctypes.c_size_t*64).in_dll(native,'request_sizes')
            for n,i,value in native_cases:
                before = stats['allocations'].value, stats['frees'].value
                stats['request_count'].value = stats['free_count'].value = 0
                require(fn(n,i,value) == (value if i < n else 99), 'native scalar mismatch')
                delta = stats['allocations'].value-before[0], stats['frees'].value-before[1]
                require(delta[0] == delta[1] and 0 <= delta[0] <= 1, 'native lifecycle')
                if level == '-O0':
                    require(delta == (1,1) and stats['request_count'].value == 1 and sizes[0] == 8*(n+1),
                            'native allocation extent')
                require(stats['active_count'].value == stats['bad'].value == 0, 'native invalid free/leak')
                count += 1
        print(f'dynamic MIR: full fixture match, {len(cases)} independent executions, '
              f'{len(mutations)} mutations, {count} native runs (signed cases are native only)')


if __name__ == '__main__':
    main()
