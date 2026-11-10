#!/usr/bin/env python3
"""Regression correspondence for Lean-derived primitive safety fixtures.

The native checks exercise the trusted executable kernel and backend; they do
not turn the model's local-array/USub theorem into a compiler refinement proof.
"""
from __future__ import annotations
import argparse
import ctypes
import os
from pathlib import Path
import platform
import shlex
import struct
import subprocess
import sys
import tempfile
from core_certificate_process import ROOT, command, success
from core_typing_producer import require

FIXTURE = ROOT / 'tests/core_preserves/lean-primitive-safety.jhc'
ANCHOR = '(export valid_anchor I64 (int 1))\n'
# Each negative has a working exported anchor and a repaired positive control.
PAIRS = {
    'out-of-range-read': (
        '(def bad I64 (index (array (int 7)) 1 (decide-lt 0 1)))',
        '(def bad I64 (index (array (int 7)) 0 (decide-lt 0 1)))'),
    'empty-array-read': (
        '(def bad I64 (index (array) 0 (decide-lt 0 1)))',
        '(def bad I64 (index (array (int 7)) 0 (decide-lt 0 1)))'),
    'underflow': (
        '(def bad U64 (usub 0 1 (zero-le 0)))',
        '(def bad U64 (usub 0 0 (zero-le 0)))'),
    'wrong-subtraction-bound': (
        '(def bad U64 (usub 10 3 (decide-lt 2 11)))',
        '(def bad U64 (usub 10 3 (decide-lt 3 11)))'),
    'wrong-subtracted-equality': (
        '(def bad (Eq (usub 7 5 (decide-lt 5 8)) 3) (refl 2))',
        '(def bad (Eq (usub 7 5 (decide-lt 5 8)) 2) (refl 2))'),
    'false-zero-le-type': (
        '(def bad (Lt 1 2) (zero-le 1))',
        '(def bad (Lt 0 2) (zero-le 1))'),
}


def test(compiler, out):
    def core(*args):
        return command([*compiler, 'core', *args])
    success(core('check', FIXTURE))
    success(core('preserves', FIXTURE))
    mir = success(core('emit-mir', FIXTURE))
    require(b'primitive_max_proof' not in mir and b'zero-le' not in mir and b'decide-lt' not in mir,
            'evidence escaped erasure')
    require(b'assert' not in mir, 'closed safe primitives unexpectedly require runtime checks')
    host = 'aarch64' if platform.machine() in ('aarch64', 'arm64') else 'x86_64'
    cc = shlex.split(os.environ.get('JIHOO_CC', 'clang'))
    expected = {'primitive_first': (ctypes.c_int64, -(1 << 63)),
                'primitive_last': (ctypes.c_int64, (1 << 63)-1),
                'primitive_computed': (ctypes.c_int64, (1 << 63)-1),
                'primitive_subtract': (ctypes.c_uint64, 7),
                'primitive_max_subtract': (ctypes.c_uint64, (1 << 64)-1),
                'primitive_nested_subtract': (ctypes.c_uint64, 2),
                'primitive_subtracted_index': (ctypes.c_int64, (1 << 63)-1),
                'primitive_sub_annotation': (ctypes.c_int64, 9)}
    for target, machine in [('x86_64', 62), ('aarch64', 183)]:
        for level in ['-O0', '-O2']:
            obj = out / f'{target}{level}.o'
            success(core('emit-obj', FIXTURE, '--target', target, level, '-o', obj))
            binary = obj.read_bytes()
            require(binary[:4] == b'\x7fELF' and struct.unpack_from('<H', binary, 18)[0] == machine,
                    'wrong object target')
            if target == host:
                library = out / f'primitive{level}.so'
                success(command([*cc, '-shared', obj, '-o', library]))
                native = ctypes.CDLL(str(library))
                for name, (result_type, value) in expected.items():
                    function = getattr(native, name)
                    function.argtypes, function.restype = [], result_type
                    require(function() == value, f'{name} {level}: wrong native result')
    for name, (bad, fixed) in PAIRS.items():
        bad_path, good_path = out / f'{name}.jhc', out / f'{name}-control.jhc'
        bad_path.write_text(ANCHOR + bad)
        good_path.write_text(ANCHOR + fixed)
        success(core('check', good_path))
        success(core('emit-obj', good_path, '-o', out / f'{name}-control.o'))
        for action in ['check', 'emit-obj']:
            obj = out / f'{name}.o'
            args = ['-o', obj] if action == 'emit-obj' else []
            rejected = core(action, bad_path, *args)
            require(rejected.returncode != 0 and b'type mismatch' in rejected.stderr,
                    f'{name}: wrong rejection: {rejected.stderr!r}')
            require(not obj.exists(), f'{name}: invalid program emitted an object')
    # The natural-index safety theorem does not assert overflow-free machine
    # addition. A well-typed UAdd can trap, and its erased proof-bound counterpart
    # in primitive_max_subtract above must not be evaluated at runtime.
    overflow = out / 'overflow.jhc'
    overflow.write_text('(export primitive_overflow U64 (uadd 18446744073709551615 1))\n')
    success(core('check', overflow))
    for level in ['-O0', '-O2']:
        obj, library = out / f'overflow{level}.o', out / f'overflow{level}.so'
        success(core('emit-obj', overflow, level, '-o', obj))
        success(command([*cc, '-shared', obj, '-o', library]))
        script = ("import ctypes,sys; f=ctypes.CDLL(sys.argv[1]).primitive_overflow; "
                  "f.restype=ctypes.c_uint64; print('entered',flush=True); f()")
        result = subprocess.run([sys.executable, '-c', script, str(library)],
                                capture_output=True, timeout=10)
        require(result.returncode < 0 and result.stdout == b'entered\n',
                f'{level}: expected arithmetic trap after successful load: {result}')
    print('primitive safety: Lean fixture checked/preserved; 8 native results at O0/O2, '
          'both object targets, 6 paired rejections, erasure and overflow boundaries')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-primitive-') as folder:
        test(shlex.split(args.compiler), Path(folder))

if __name__ == '__main__':
    main()
