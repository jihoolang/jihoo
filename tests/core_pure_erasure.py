#!/usr/bin/env python3
"""Generated well-typed pure Core twins, not literal untyped erasures.
Native MIR/results/traps test trusted implementation behavior, not refinement.
The guarded_read/selected_branch families use native IfLt, which is extra
regression coverage, not a claim that the formal pure grammar includes branches.
"""
import argparse
import ctypes
import os
from pathlib import Path
import shlex
import signal
import subprocess
import sys
import tempfile
from core_scoped_lend import command, require

MAX = (1 << 64) - 1
FAMILIES = {
    'add': ('U64', lambda x: f'(uadd {x} 3)', lambda x: x+3, True),
    'guarded_read': ('I64', lambda x: f'(if-lt {x} 3 q (index (array (int 11) (int 22) (int 33)) {x} q) (int -1))',
                     lambda x: (11, 22, 33)[x] if x < 3 else -1, False),
    'subtract': ('U64', lambda x: f'(uadd {x} (usub 10 3 (app (lam0 p (Lt 3 11) p) (decide-lt 3 11))))',
                 lambda x: x+7, True),
    'ignored_runtime': ('I64', lambda x: f'(app (lam ignored U64 (int 7)) (uadd {x} 1))', lambda x: 7, True),
    'unselected_array': ('I64', lambda x: f'(index (array (int 7) (app (lam ignored U64 (int 8)) (uadd {x} 1))) 0 (decide-lt 0 2))',
                         lambda x: 7, True),
    'selected_branch': ('I64', lambda x: f'(if-lt {x} 1 q (int 7) (app (lam ignored U64 (int 8)) (uadd {x} 1)))',
                        lambda x: 7 if x == 0 else 8, True),
}


def nested(make_body, depth, value='x'):
    if depth == 0:
        return make_body(value)
    runtime, erased, proof = f'r{depth}', f'n{depth}', f'p{depth}'
    body = nested(make_body, depth-1, runtime)
    return (f'(app (lam {runtime} U64 (app (lam0 {erased} U64 '
            f'(app (lam0 {proof} (Eq {erased} {erased}) {body}) (refl {erased}))) '
            f'(uadd {MAX} 1))) {value})')


def export(name, result_type, body):
    return f'(export {name} (pi x U64 {result_type}) (lam x U64 {body}))\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    compiler = str(Path(parser.parse_args().compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='pure-erasure-') as directory:
        tmp = Path(directory)
        all_sources, specs = [], []
        comparisons = 0
        for family, (result_type, make, expected, traps) in FAMILIES.items():
            for depth in (1, 2, 4):
                twins = (make('x'), nested(make, depth))
                mir = []
                for variant, body in enumerate(twins):
                    name = f'{family}_{depth}_{variant}'
                    all_sources.append(export(name, result_type, body))
                    specs.append((name, result_type, expected, traps))
                    path = tmp / f'{name}.jhc'
                    path.write_text(export('same_symbol', result_type, body))
                    command([compiler, 'core', 'check', path])
                    command([compiler, 'core', 'preserves', path])
                    mir.append(command([compiler, 'core', 'emit-mir', path, '-O0']).stdout)
                require(mir[0] == mir[1], f'{family} depth{depth}: erased payload changed MIR')
                comparisons += 1
        changed = tmp / 'runtime-change.jhc'
        changed.write_text(export('same_symbol', 'U64', '(uadd x 4)'))
        baseline = tmp / 'add_1_0.jhc'
        require(command([compiler, 'core', 'emit-mir', changed]).stdout !=
                command([compiler, 'core', 'emit-mir', baseline]).stdout,
                'MIR comparison failed to detect runtime change')
        combined = tmp / 'all.jhc'; combined.write_text(''.join(all_sources))
        cc = shlex.split(os.environ.get('JIHOO_CC', 'clang'))
        results = trapped_cases = 0
        trap_script = (
            'import ctypes,resource,sys; resource.setrlimit(resource.RLIMIT_CORE,(0,0)); '
            'f=getattr(ctypes.CDLL(sys.argv[1]),sys.argv[2]); '
            'f.argtypes=[ctypes.c_uint64]; f.restype=ctypes.c_uint64; '
            'print("entered",flush=True); f((1<<64)-1)')
        for level in ('-O0', '-O2'):
            obj, library = tmp / f'{level}.o', tmp / f'{level}.so'
            command([compiler, 'core', 'emit-obj', combined, level, '-o', obj])
            command([*cc, '-shared', obj, '-o', library])
            native = ctypes.CDLL(str(library))
            for name, result_type, expected, traps in specs:
                fn = getattr(native, name); fn.argtypes = [ctypes.c_uint64]
                fn.restype = ctypes.c_uint64 if result_type == 'U64' else ctypes.c_int64
                for value in (0, 1, 2, 7):
                    require(fn(value) == expected(value), f'{name}/{level}: wrong scalar')
                    results += 1
                if not traps:
                    require(fn(MAX) == expected(MAX), 'guard failed on maximum input')
                    results += 1
                else:
                    child = subprocess.run([sys.executable, '-c', trap_script, str(library), name],
                                           capture_output=True, timeout=10)
                    require(child.returncode in (-signal.SIGILL, -signal.SIGTRAP) and
                            child.stdout == b'entered\n', f'{name}/{level}: runtime trap lost: {child}')
                    trapped_cases += 1
        invalid = {
            'erased-runtime': ('erased value used at runtime',
                export('bad', 'U64', '(app (lam0 n U64 n) x)')),
            'wrong-index-proof': ('type mismatch',
                '(export bad I64 (index (array (int 7)) 1 (decide-lt 0 1)))'),
            'wrong-sub-proof': ('type mismatch', '(export bad U64 (usub 10 3 (decide-lt 2 11)))'),
        }
        for name, (diagnostic, text) in invalid.items():
            path = tmp / f'{name}.jhc'; path.write_text(text)
            failure = command([compiler, 'core', 'check', path], success=False)
            require(diagnostic in failure.stderr, f'{name}: wrong rejection: {failure.stderr}')
            obj = tmp / f'{name}.o'
            command([compiler, 'core', 'emit-obj', path, '-o', obj], success=False)
            require(not obj.exists(), 'invalid pure program emitted object')
        print(f'pure erasure: {comparisons} MIR twin pairs, {results} native results, '
              f'{trapped_cases} runtime traps, {len(invalid)} rejected programs')


if __name__ == '__main__':
    main()
