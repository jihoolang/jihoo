#!/usr/bin/env python3
"""Owned-producing arguments preserve captured live owners and scalar values.
These native tests exercise framed application; the formal partition is explicit,
not a claim that the compiler infers it or that general lowering is proved.
"""
import argparse
import ctypes
import os
from pathlib import Path
import shlex
import tempfile
from core_linear_heap import bind
from core_mixed_lend import lend
from core_owned_call import COUNTER
from core_scoped_lend import command, require


def source(name, fresh, depth, result):
    # Allocation 0 is a held frame; 1 is the input given to the producer.
    producer = bind('made', '(Buffer 1)', '(alloc 1 b)',
                    '(free input made)' if fresh else '(free made input)')
    selected = 2 if fresh else 1
    freed = [1 if fresh else 2]
    for i in range(depth):
        # The held frame is live across both the nested producer and this caller.
        producer = bind('intermediate', '(Buffer 1)', producer,
                        bind('scratch', '(Buffer 1)', '(alloc 1 b)',
                             '(free scratch intermediate)'))
        freed.append(3+i)
    if result == 'sum':
        consumer = lend('held', 'frameValue', 'frameOwner',
                     lend('received', 'argumentValue', 'argumentOwner',
                          '(free argumentOwner (free frameOwner (add bonus (add frameValue argumentValue))))'))
        body = bind('received', '(Buffer 1)', producer, consumer)
        freed += [selected, 0]
    else:
        # Return either the caller's capture or the argument, then consume it later.
        consumer = '(free received held)' if result == 'frame' else '(free held received)'
        call = bind('received', '(Buffer 1)', producer, consumer)
        body = bind('escaped', '(Buffer 1)', call,
                    lend('escaped', 'answer', 'last', '(free last (add answer bonus))'))
        freed += [selected, 0] if result == 'frame' else [0, selected]
    body = bind('held', '(Buffer 1)', '(alloc 1 frame)',
                bind('input', '(Buffer 1)', '(alloc 1 a)', body))
    text = (f'(export {name} (pi frame I64 (pi a I64 (pi b I64 (pi bonus I64 I64)))) '
            f'(lam frame I64 (lam a I64 (lam b I64 (lam bonus I64 {body})))))\n')
    return text, freed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    compiler = str(Path(parser.parse_args().compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='framed-call-') as directory:
        tmp = Path(directory)
        specs, texts = [], []
        for fresh in (False, True):
            for depth in (0, 2):
                for result in ('frame', 'argument', 'sum'):
                    name = f'f{len(specs)}'
                    text, free_order = source(name, fresh, depth, result)
                    texts.append(text); specs.append((name, fresh, depth, result, free_order))
        core = tmp / 'calls.jhc'; core.write_text(''.join(texts))
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
            for name, fresh, depth, result, free_order in specs:
                fn = getattr(native, name); fn.argtypes = [ctypes.c_int64]*4; fn.restype = ctypes.c_int64
                for frame, a, b, bonus in ((99, 11, 37, 5), (11, 37, 99, 3), (7, 7, 7, 7),
                                            (-7, -11, 42, 8), (0, 0, 0, 0)):
                    before = stats['allocations'].value, stats['frees'].value
                    stats['peak'].value = stats['free_count'].value = 0
                    argument = b if fresh else a
                    expected = {'frame': frame, 'argument': argument, 'sum': frame+argument}[result]+bonus
                    require(fn(frame, a, b, bonus) == expected, f'{name}: frame/argument/scalar changed')
                    delta = stats['allocations'].value-before[0], stats['frees'].value-before[1]
                    require(delta[0] == delta[1] and 0 <= delta[0] <= depth+3,
                            f'{name}: unbalanced lifecycle {delta}')
                    if level == '-O0':
                        require(delta == (depth+3, depth+3) and stats['peak'].value == 3,
                                f'{name}: frame not held across producer')
                        actual = [freed_ids[i]-before[0] for i in range(stats['free_count'].value)]
                        require(actual == free_order, f'{name}: wrong identity/order {actual} != {free_order}')
                    require(stats['active_count'].value == 0 and stats['bad'].value == 0,
                            f'{name}: invalid free or leak')
                    cases += 1
        producer = bind('moved', '(Buffer 1)', 'input', 'moved')
        invalid = {
            'producer-uses-frame-twice': ('an owned value is used more than once',
                bind('result', '(Buffer 1)', '(free held '+producer+')', '(free result (free held (int 9)))')),
            'old-input-alias': ('an owned value is used more than once',
                bind('result', '(Buffer 1)', producer, '(free input (free result (free held (int 9))))')),
            'lost-frame': ('an owned value must be used',
                bind('result', '(Buffer 1)', producer, '(free result (int 9))')),
            'lost-argument': ('an owned value must be used',
                bind('result', '(Buffer 1)', producer, '(free held (int 9))')),
            'captured-frame-duplicated': ('an owned value is used more than once',
                bind('result', '(Buffer 1)', producer, '(free result (free held (free held (int 9))))')),
        }
        for name, (diagnostic, body) in invalid.items():
            path = tmp / f'{name}.jhc'
            path.write_text(f'(def bad (pi held (Buffer 1) (pi input (Buffer 1) I64)) '
                            f'(lam held (Buffer 1) (lam input (Buffer 1) {body})))')
            failed = command([compiler, 'core', 'check', path], success=False)
            require(diagnostic in failed.stderr, f'{name}: unexpected diagnostic: {failed.stderr}')
            obj = tmp / f'{name}.o'; command([compiler, 'core', 'emit-obj', path, '-o', obj], success=False)
            require(not obj.exists(), f'{name}: invalid program emitted object')
        print(f'framed-call: {len(specs)} variants, {cases} native lifecycles, {len(invalid)} rejects')


if __name__ == '__main__':
    main()
