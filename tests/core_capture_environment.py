#!/usr/bin/env python3
"""Generated-recursion capture layouts: native regressions, not a refinement proof."""
import argparse
import ctypes
import os
from pathlib import Path
import platform
import shlex
import struct
import sys
import tempfile
from core_buffer import COUNTER
from core_certificate_process import ROOT, command, success
from core_typing_producer import require


def program(ghost):
    prefix = (ROOT / 'examples/core_nth.jh').read_text().split('fn length')[0]
    parameter = ', p: erased(Eq(0, 0))' if ghost else ''
    domain = ', q: erased(Eq(0, 0))' if ghost else ''
    binder = ', q' if ghost else ''
    evidence = ', q' if ghost else ''
    initial = ', p' if ghost else ''
    exported = ', refl(0)' if ghost else ''
    return prefix + f'''
fn captured(xs: ref List, a: i64, b: i64, c: i64{parameter}) -> i64 {{
    induct(fn(t, m: i64{domain}) {{ i64 }}, fn(m{binder}) {{ a * m + b + c }},
        fn(x, rest, ih, m{binder}) {{
            induct(fn(u) {{ i64 }}, ih(m + x{evidence}),
                fn(y, more, again) {{ again + ih(a * y + b{evidence}) + c }}, rest)
        }}, xs)(0{initial})
}}
fn captured_three(xs: ref List, a: i64, b: i64, c: i64{parameter}) -> i64 {{
    induct(fn(t, m: i64{domain}) {{ i64 }}, fn(m{binder}) {{ a * m + b + c }},
        fn(x, rest, ih, m{binder}) {{
            induct(fn(u, z: i64) {{ i64 }}, fn(z) {{ ih(m + z{evidence}) }},
                fn(y, more, again, z) {{
                    induct(fn(v) {{ i64 }}, again(z + y),
                        fn(w, tail, deep) {{ deep + ih(a * w + b{evidence}) + again(w + c) }}, more)
                }}, rest)(x)
        }}, xs)(0{initial})
}}
export fn capture_three(n: u64, x: i64, a: i64, b: i64, c: i64) -> i64 {{
    let xs = ascending(n, x)
    captured_three(xs, a, b, c{exported})
}}
fn threaded(xs: ref List, b: buffer(1), a: i64{parameter}) -> buffer(1) {{
    induct(fn(t, buf: buffer(1){domain}) {{ buffer(1) }}, fn(buf{binder}) {{ buf }},
        fn(x, rest, ih, buf{binder}) {{
            let v = induct(fn(u) {{ i64 }}, a * x, fn(y, more, total) {{ total + y }}, rest)
            ih(store(buf, 0, v, decide_lt(0, 1)){evidence})
        }}, xs)(b{initial})
}}
export fn capture_owned(n: u64, x: i64, a: i64, b: i64, c: i64) -> i64 {{
    let xs = ascending(n, x)
    let result = threaded(xs, alloc(1, b + c), a{exported})
    load(result, 0, decide_lt(0, 1), fn(v, result) {{ v }})
}}
fn paired(xs: ref List, a: i64, b: i64, c: i64{parameter}) -> i64 {{
    induct(fn(t, m: i64{domain}, z: i64) {{ i64 }}, fn(m{binder}, z) {{ a * m - z }},
        fn(x, rest, ih, m{binder}, z) {{ ih(m + x{evidence}, z - 1) }}, xs)(b{initial}, c)
}}
export fn capture_pair(n: u64, x: i64, a: i64, b: i64, c: i64) -> i64 {{
    let xs = ascending(n, x)
    paired(xs, a, b, c{exported})
}}
export fn capture(n: u64, x: i64, a: i64, b: i64, c: i64) -> i64 {{
    let xs = ascending(n, x)
    captured(xs, a, b, c{exported})
}}
'''


def expected(n, x, a, b, c):
    values = tuple(x + n - i for i in range(n))

    def outer(items, m):
        if not items:
            return a * m + b + c
        head, rest = items[0], items[1:]
        result = outer(rest, m + head)
        for y in reversed(rest):
            result = result + outer(rest, a * y + b) + c
        return result
    return outer(values, 0)


def expected_three(n, x, a, b, c):
    values = tuple(x + n - i for i in range(n))

    def outer(items, m):
        if not items:
            return a * m + b + c
        head, rest = items[0], items[1:]

        def inner(items2, z):
            if not items2:
                return outer(rest, m + z)
            y, more = items2[0], items2[1:]
            result = inner(more, z + y)
            for w in reversed(more):
                result += outer(rest, a * w + b) + inner(more, w + c)
            return result
        return inner(rest, head)
    return outer(values, 0)


def expected_owned(n, x, a, b, c):
    return a * (x + 1) if n else b + c


def expected_pair(n, x, a, b, c):
    return a * (b + n * x + n * (n + 1) // 2) - (c - n)


def native_worker(path):
    native = ctypes.CDLL(str(path))
    functions = [(native.capture, expected), (native.capture_three, expected_three),
                 (native.capture_owned, expected_owned), (native.capture_pair, expected_pair)]
    for function, _ in functions:
        function.argtypes = [ctypes.c_uint64, *([ctypes.c_int64] * 4)]
        function.restype = ctypes.c_int64
    allocations = ctypes.c_long.in_dll(native, 'allocations')
    frees = ctypes.c_long.in_dll(native, 'frees')
    cases = 0
    for n in range(5):
        for x in (-3, 0, 7):
            # Distinct scalar values catch argument permutations; equal values
            # separately exercise equal-typed/equal-payload capture slots.
            for a, b, c in ((2, 3, 5), (-2, 7, 11), (4, 4, 4)):
                for function, model in functions:
                    before_alloc, before_free = allocations.value, frees.value
                    result = function(n, x, a, b, c)
                    require(result == model(n, x, a, b, c),
                            f'capture result mismatch: {(n, x, a, b, c, result)}')
                    require(allocations.value - before_alloc == frees.value - before_free,
                            f'unbalanced ownership for n={n}')
                    require(allocations.value > before_alloc or n == 0,
                            'nonempty list did not exercise heap allocation')
                    cases += 1
    print(f'{cases} native capture cases and allocation balances passed')


def test(compiler, out):
    require(expected(3, 7, 2, 3, 5) != expected(3, 7, 3, 2, 5),
            'two-level model cannot detect permuted scalar captures')
    require(expected_three(3, 7, 2, 3, 5) != expected_three(3, 7, 3, 2, 5),
            'three-level model cannot detect permuted scalar captures')
    paths = []
    for name, ghost in (('plain', False), ('ghost', True)):
        path = out / f'capture-{name}.jh'
        path.write_text(program(ghost))
        success(command([*compiler, 'check', path, '--lib']))
        paths.append(path)
    mir = [success(command([*compiler, 'emit-mir', path, '--lib'])) for path in paths]
    require(mir[0] == mir[1], 'ghost capture changes complete MIR')
    require(mir[0].count(b'fn recursion.') >= 5, 'nested recursion was not lowered')
    require(b'call' in mir[0], 'generated recursion calls are missing')
    counter = out / 'counter.c'
    counter.write_text(COUNTER)
    cc = shlex.split(os.environ.get('JIHOO_CC', 'clang'))
    host = 'aarch64' if platform.machine() in ('aarch64', 'arm64') else 'x86_64'
    objects = runs = 0
    for target, machine in (('x86_64', 62), ('aarch64', 183)):
        for level in ('-O0', '-O2'):
            for path in paths:
                obj = out / f'{path.stem}-{target}-{level}.o'
                success(command([*compiler, 'emit-obj', path, '--lib', '--target', target, level, '-o', obj]))
                data = obj.read_bytes()
                require(len(data) >= 20 and data[:4] == b'\x7fELF' and
                        struct.unpack_from('<H', data, 18)[0] == machine, 'wrong object architecture')
                objects += 1
                if target == host:
                    library = obj.with_suffix('.so')
                    success(command([*cc, '-shared', '-fPIC', obj, counter, '-o', library,
                                     '-Wl,--wrap=malloc', '-Wl,--wrap=free']))
                    output = success(command([sys.executable, *(['-O'] if sys.flags.optimize else []),
                                              __file__, '--native-library', library]))
                    require(b'180 native capture cases' in output, f'worker did not finish: {output!r}')
                    runs += 180
    # The valid exported counterpart above makes this an ownership rejection,
    # not a no-export or unsupported-lowering failure. Never execute it.
    invalid = out / 'capture-owned-duplicate.jh'
    original = 'ih(store(buf, 0, v, decide_lt(0, 1)), q)'
    bad = program(True)
    require(original in bad, 'ownership mutation did not target a real call')
    invalid.write_text(bad.replace(original, 'free(buf, ih(buf, q))'))
    rejected = command([*compiler, 'check', invalid, '--lib'])
    require(rejected.returncode != 0 and b'an owned value is used more than once' in rejected.stderr,
            f'wrong duplicate-owner diagnostic: {rejected.stderr!r}')
    obj = out / 'invalid.o'
    rejected = command([*compiler, 'emit-obj', invalid, '--lib', '-o', obj])
    require(rejected.returncode != 0 and not obj.exists(), 'duplicate owner reached an object')
    print(f'capture environments: exact plain/ghost MIR; {objects} target objects; '
          f'{runs} native differential cases with balanced allocations; duplicate-owner rejection')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--native-library', type=Path)
    args = parser.parse_args()
    if args.native_library:
        native_worker(args.native_library)
        return
    with tempfile.TemporaryDirectory(prefix='jihoo-capture-') as folder:
        test(shlex.split(args.compiler), Path(folder))


if __name__ == '__main__':
    main()
