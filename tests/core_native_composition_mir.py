#!/usr/bin/env python3
"""Exact root-81 native MIR association and independent execution regressions.
The parametric theorem covers nonnegative I64s. Signed native cases do not
extend that theorem, and snapshot admission is not generic compiler verification.
"""
import argparse
import copy
import ctypes
import json
import os
from pathlib import Path
import shlex
import tempfile

from core_dependent_buffer import SIZED_COUNTER
from core_scoped_graph import ROOT, require, run


CASES = [(0, 0, 0, 0), (0, 7, 0, 42), (0, 7, (1 << 64)-1, 11),
         (1, 0, 0, 37), (7, 0, 6, 42), (7, 2, 6, 42), (2, 7, 1, 17),
         (4, 9, 4, 0), (7, 2, (1 << 64)-1, 11), (1, 1, 0, (1 << 63)-1),
         (4094, 0, 4093, 37), (2047, 2047, 2046, 17),
         (1, 4093, 0, 11), (4094, 0, (1 << 64)-1, 0)]


def expected(n, m, i, value):
    lengths = [n, m] if i < n else [n]
    heap = [(False, [value] * length + [None]) for length in lengths]
    events = [('alloc', j, 8*(length+1)) for j, length in enumerate(lengths)]
    events += [('free', j) for j in range(len(lengths))]
    return value if i < n else 99, heap, events


def execute(snapshot, n, m, i, value):
    """Independent multi-object interpreter, not a proof or production decoder."""
    schema, arguments, types, blocks = snapshot
    require(schema == 2 and len(arguments) == 4, 'entry schema')
    require(len(set(arguments)) == 4, 'duplicate argument slot')
    locals_ = [None] * len(types)
    for slot, kind, v in zip(arguments, ('u64', 'u64', 'u64', 'i64'), (n, m, i, value)):
        require(0 < slot < len(types) and types[slot] == kind, 'entry type/slot')
        locals_[slot] = v
    heap, events = [], []

    def pointer(p, access=False):
        require(isinstance(p, tuple) and len(p) == 2, 'non-pointer')
        object_id, offset = p
        require(0 <= object_id < len(heap), 'unknown object')
        alive, cells = heap[object_id]
        require(alive and 0 <= offset <= len(cells), 'dead/invalid pointer')
        if access:
            require(offset < len(cells), 'out-of-bounds access')
        return object_id, offset, cells

    def read(place):
        slot, deref = place
        v = locals_[slot]
        require(v is not None, 'uninitialized local')
        if deref:
            _, offset, cells = pointer(v, True)
            require(cells[offset] is not None, 'uninitialized read')
            return cells[offset]
        return v

    def op(operand):
        if operand[0] == 'copy':
            return read(operand[1])
        require(operand[0] == 'int', 'unsupported operand')
        return operand[2]

    def write(place, value):
        slot, deref = place
        if deref:
            _, offset, cells = pointer(locals_[slot], True)
            cells[offset] = value
        else:
            locals_[slot] = value

    pc = 0
    for _ in range(4*(n+m) + 80):
        require(0 <= pc < len(blocks), 'invalid block')
        statements, term = blocks[pc]
        for place, rhs in statements:
            kind, a = rhs[0], op(rhs[1])
            if kind == 'use': result = a
            elif kind == 'cast':
                pointer(a)
                result = a[0] + 1
            else:
                b = op(rhs[2])
                if kind == 'offset':
                    pointer(a)
                    result = (a[0], a[1] + b)
                    pointer(result)
                elif kind == 'mul': result = a*b
                elif kind == 'add': result = a+b
                elif kind == 'lt': result = int(a < b)
                elif kind == 'ne': result = int(a != b)
                else: raise RuntimeError('unsupported operation')
            write(place, result)
        kind = term[0]
        if kind == 'return':
            require(not any(alive for alive, _ in heap), 'leaked object')
            return locals_[0], heap, events
        if kind == 'goto': pc = term[1]
        elif kind == 'switch': pc = dict(term[2]).get(op(term[1]), term[3])
        elif kind == 'assert':
            require(op(term[1]), 'failed assertion')
            pc = term[2]
        elif kind == 'malloc':
            size = op(term[1])
            require(size > 0 and size % 8 == 0, 'allocation extent')
            require(sum(len(cells) for _, cells in heap) + size//8 <= 4096,
                    'allocation capacity')
            object_id = len(heap)
            heap.append((True, [None] * (size//8)))
            events.append(('alloc', object_id, size))
            write(term[2], (object_id, 0))
            pc = term[3]
        elif kind == 'free':
            object_id, offset, cells = pointer(op(term[1]))
            require(offset == 0, 'interior free')
            heap[object_id] = (False, cells)
            events.append(('free', object_id))
            write(term[2], 0)
            pc = term[3]
        else: raise RuntimeError('unsupported terminator')
    raise RuntimeError('execution fuel exhausted')


def mutations(fixture):
    changed = []
    def add(name, edit):
        snapshot = copy.deepcopy(fixture)
        edit(snapshot)
        require(snapshot != fixture, f'ineffective mutation {name}')
        changed.append((name, snapshot))
    add('argument-order', lambda s: s.__setitem__(1, [2, 1, 3, 4]))
    add('argument-type', lambda s: s[2].__setitem__(4, 'u64'))
    add('argument-arity', lambda s: s[1].pop())
    add('argument-duplicate', lambda s: s[1].__setitem__(2, 1))
    add('outer-false-edge', lambda s: s[3][5][1][2][0].__setitem__(1, 6))
    add('inner-false-edge', lambda s: s[3][13][1][2][0].__setitem__(1, 14))
    add('outer-true-edge', lambda s: s[3][5][1].__setitem__(3, 7))
    add('inner-true-edge', lambda s: s[3][13][1].__setitem__(3, 15))
    add('second-length', lambda s: s[3][6][0][3][1].__setitem__(1, ['copy', [1, 0]]))
    add('second-fill', lambda s: s[3][12][0][1][1].__setitem__(1, ['int', 'i64', 0]))
    add('first-offset', lambda s: s[3][6][0][1][1].__setitem__(2, ['copy', [1, 0]]))
    add('second-offset', lambda s: s[3][14][0][1][1].__setitem__(2, ['copy', [2, 0]]))
    for block, other in ((7, 19), (14, 19), (15, 19), (17, 7), (19, 7)):
        add(f'free-target-{block}', lambda s, block=block, other=other:
            s[3][block][1].__setitem__(1, ['copy', [other, 0]]))
    def swap_frees(s):
        s[3][14][1][1], s[3][17][1][1] = s[3][17][1][1], s[3][14][1][1]
    add('free-order', swap_frees)
    for block in (8, 16, 18, 20, 21):
        add(f'join-write-{block}', lambda s, block=block:
            s[3][block][0][0][1].__setitem__(1, ['int', 'i64', 98]))
    for block in (4, 12):
        add(f'missing-fill-store-{block}', lambda s, block=block: s[3][block][0].pop(1))
    add('first-extent', lambda s: s[3][0][0][1][1].__setitem__(2, ['int', 'u64', 0]))
    add('second-extent', lambda s: s[3][6][0][4][1].__setitem__(2, ['int', 'u64', 0]))
    return changed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    args = parser.parse_args()
    source = (ROOT/'tests/core_sized_composition.jhc').read_text()
    fixture = json.loads((ROOT/'tests/core_native_composition_mir.json').read_text())
    for case in CASES:
        require(execute(fixture, *case) == expected(*case), f'independent execution {case}')
    changed = mutations(fixture)
    # Most corruptions change behavior or fail safety. The inner-true-edge
    # mutation skips a redundant read, so only exact CFG admission detects it.
    diagnostic_cases = [(3, 2, 1, 37), (3, 0, 1, 37), (0, 2, 0, 37), (3, 2, 3, 37)]
    for name, snapshot in changed:
        if name == 'inner-true-edge': continue
        detected = False
        for case in diagnostic_cases:
            try: detected |= execute(snapshot, *case) != expected(*case)
            except (RuntimeError, TypeError, IndexError, ValueError): detected = True
        require(detected, f'{name}: independent execution did not detect mutation')

    with tempfile.TemporaryDirectory(prefix='native-composition-mir-') as directory:
        tmp = Path(directory)
        def build_probe(filename, name):
            probe = tmp/name
            result = run([args.compiler, 'build', '-O0', '-I', 'compiler', filename, '-o', probe])
            require(result.returncode == 0, result.stderr)
            return probe
        probe = build_probe('tests/core_mir_probe.jh', 'mir-probe')
        exported = run([probe], source)
        require(exported.returncode == 0, exported.stderr)
        require(json.loads(exported.stdout) == fixture, 'complete native MIR fixture drift')
        graph_probe = build_probe('tests/core_linear_graph_probe.jh', 'graph-probe')
        exported = run([graph_probe], source)
        require(exported.returncode == 0, exported.stderr)
        graph = json.loads(exported.stdout)
        require(graph == json.loads((ROOT/'tests/core_sized_composition.json').read_text()),
                'complete original Core graph drift')
        for kinds in [('U64',), ('U64',)*4, ('I64', 'U64', 'U64', 'I64'),
                      ('U64', 'I64', 'U64', 'U64'), ('U64', 'U64', 'I64', 'U64'),
                      ('U64', 'U64', 'U64', 'U64', 'I64')]:
            body, ty = '(int 0)', 'I64'
            for j, kind in reversed(list(enumerate(kinds))):
                body, ty = f'(lam x{j} {kind} {body})', f'(pi x{j} {kind} {ty})'
            result = run([probe], f'(export bad {ty} {body})')
            require(result.returncode != 0 and 'entry signature' in result.stderr,
                    f'unsupported signature admitted: {kinds}: {result.stderr}')

        def check(envelope, want=True, raw=False):
            payload = envelope if raw else json.dumps(envelope, separators=(',', ':'))
            result = run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run',
                          'CheckNativeCompositionMir.lean'], payload, ROOT/'proofs')
            require((result.returncode == 0) == want,
                    f'native composition admission expected {want}: {result.stdout} {result.stderr}')
            require(('native-composition-mir accepted' in result.stdout) if want else
                    ('native-composition-mir rejected:' in result.stderr), 'unexpected checker path')
        envelope = [1, graph, fixture]
        check(envelope)
        for _, snapshot in changed: check([1, graph, snapshot], False)
        for index, value in ((1, graph[2]), (2, graph[1])):
            wrong = copy.deepcopy(graph); wrong[index] = value
            check([1, wrong, fixture], False)
        wrong = copy.deepcopy(graph); wrong[3][0] = ['i64']
        check([1, wrong, fixture], False)
        wrong = copy.deepcopy(graph); wrong[3][81][-1] = 0
        check([1, wrong, fixture], False)
        for field in (2, 3):
            oversized = copy.deepcopy(fixture)
            oversized[field] = oversized[field] * (513 // len(oversized[field]) + 1)
            check([1, graph, oversized], False)
        for malformed in ([2, graph, fixture], envelope + [0], envelope[:-1], None, {}):
            check(malformed, False)
        for malformed in ('', '[', json.dumps(envelope) + ' garbage',
                          '['*17 + '0' + ']'*17, '[123456789012345678901]',
                          '[1e0]', '[-1]', '[1.0]', '["\\u0061"]',
                          ' '*(8*1024*1024+1)):
            check(malformed, False, raw=True)

        core = tmp/'composition.jhc'; core.write_text(source)
        counter = tmp/'counter.c'; counter.write_text(SIZED_COUNTER)
        cc = shlex.split(os.environ.get('JIHOO_CC', 'clang'))
        native_cases = CASES + [(1, 0, 0, -1), (2, 7, 1, -(1 << 63)),
                                (7, 2, 6, -37), (0, 0, 0, -7)]
        count = 0
        for level in ('-O0', '-O2'):
            obj, library = tmp/f'{level}.o', tmp/f'{level}.so'
            result = run([args.compiler, 'core', 'emit-obj', core, level, '-o', obj])
            require(result.returncode == 0, result.stderr)
            result = run([*cc, '-shared', '-fPIC', obj, counter, '-o', library,
                          '-Wl,--wrap=malloc', '-Wl,--wrap=free'])
            require(result.returncode == 0, result.stderr)
            native = ctypes.CDLL(str(library)); fn = native.copied
            fn.argtypes = [ctypes.c_uint64]*3 + [ctypes.c_int64]
            fn.restype = ctypes.c_int64
            stats = {key: ctypes.c_long.in_dll(native, key) for key in
                     ('allocations', 'frees', 'active_count', 'peak', 'bad', 'request_count', 'free_count')}
            sizes = (ctypes.c_size_t*64).in_dll(native, 'request_sizes')
            frees = (ctypes.c_long*64).in_dll(native, 'freed_ids')
            for n, m, i, value in native_cases:
                before = stats['allocations'].value, stats['frees'].value
                for key in ('peak', 'request_count', 'free_count'): stats[key].value = 0
                require(fn(n, m, i, value) == (value if i < n else 99), 'native scalar mismatch')
                delta = stats['allocations'].value-before[0], stats['frees'].value-before[1]
                allocations = 2 if i < n else 1
                require(delta[0] == delta[1] and 0 <= delta[0] <= allocations, 'native lifecycle')
                if level == '-O0':
                    require(delta == (allocations, allocations) and stats['peak'].value == allocations,
                            'native captured owner lifetime')
                    require([sizes[j] for j in range(stats['request_count'].value)] ==
                            ([8*(n+1), 8*(m+1)] if i < n else [8*(n+1)]), 'native allocation extents')
                    require([frees[j]-before[0] for j in range(stats['free_count'].value)] ==
                            list(range(allocations)), 'native free order')
                require(stats['active_count'].value == stats['bad'].value == 0, 'native invalid free/leak')
                count += 1
        print(f'native composition MIR: full source/MIR match, {len(CASES)} independent executions, '
              f'{len(changed)} mutations, {count} native runs (signed cases are native only)')


if __name__ == '__main__':
    main()
