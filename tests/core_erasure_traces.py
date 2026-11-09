#!/usr/bin/env python3
"""Differential native lowering checks; not a verified Core/MIR simulation.

Compare complete MIR for ghost-annotated and runtime-only twins. No input
program is executed (some deliberately retain potentially trapping arithmetic).
"""
import argparse
from pathlib import Path
import shlex
import struct
import tempfile
from core_certificate_process import command, success
from core_typing_producer import require


def export(body):
    return f'(export test (pi x U64 U64) (lam x U64 {body}))\n'


def export_i64(body):
    return f'(export test (pi x U64 I64) (lam x U64 {body}))\n'


def ghost(body):
    return f'(app (lam0 p (Eq 1 1) (lam0 q (Lt 0 1) {body})) (refl 1) (decide-lt 0 1))'


PAIRS = {
    'identity': (export('x'), export(ghost('x'))),
    'branch': (export('(if-lt x 1 h x (uadd x 1))'),
               export(ghost('(if-lt x 1 h x (uadd x 1))'))),
    'local-owner': (export('(app (lam b (Buffer 1) (free b x)) (alloc 1 (int 7)))'),
                    export(ghost('(app (lam b (Buffer 1) '
                         f'{ghost("(free b x)")}) (alloc 1 (int 7)))'))),
    'trap-before-free': (
        export('(app (lam b (Buffer 1) (app (lam y U64 (free b y)) (uadd x 1))) (alloc 1 (int 7)))'),
        export(ghost('(app (lam b (Buffer 1) (app (lam y U64 (free b y)) (uadd x 1))) (alloc 1 (int 7)))'))),
    'trap-after-free': (
        export('(app (lam b (Buffer 1) (free b (uadd x 1))) (alloc 1 (int 7)))'),
        export(ghost('(app (lam b (Buffer 1) (free b (uadd x 1))) (alloc 1 (int 7)))'))),
    'loop': (export_i64('(fold x (int 0) (lam i U64 (lam0 p (Lt i x) (lam acc I64 (add acc (int 1))))))'),
             export_i64(ghost('(fold x (int 0) (lam i U64 (lam0 p (Lt i x) (lam acc I64 (add acc (int 1))))))'))),
    'erased-overflow': (export('x'),
        export('(app (lam0 n U64 x) (uadd 18446744073709551615 1))')),
}

INVALID = {
    'foreign-erased-proof': ('exports cannot require erased evidence from foreign callers',
        '(export test (pi0 p (Eq 1 1) (pi x U64 U64)) '
        '(lam0 p (Eq 1 1) (lam x U64 x)))'),
    'erased-runtime-use': ('erased value used at runtime',
        '(export test (pi0 n U64 U64) (lam0 n U64 n))'),
    'duplicate-owner': ('an owned value is used more than once',
        export(ghost('(app (lam b (Buffer 1) (free b (free b x))) (alloc 1 (int 7)))'))),
    'discard-owner': ('an owned value must be used',
        export(ghost('(app (lam b (Buffer 1) x) (alloc 1 (int 7)))'))),
}


def test(compiler, out):
    comparisons = 0
    for name, twins in PAIRS.items():
        paths = []
        for tag, source in zip(('plain', 'ghost'), twins):
            path = out / f'{name}-{tag}.jhc'
            path.write_text(source)
            success(command([*compiler, 'core', 'check', path]))
            paths.append(path)
        for target in ('x86_64', 'aarch64'):
            for level in ('-O0', '-O2'):
                outputs = [success(command([*compiler, 'core', 'emit-mir', path,
                           '--target', target, level])) for path in paths]
                require(outputs[0] == outputs[1], f'{name}/{target}/{level}: MIR differs\n{outputs!r}')
                require(b'fn test' in outputs[0], f'{name}: empty or missing export')
                for index, path in enumerate(paths):
                    obj = out / f'{name}-{target}-{level}-{index}.o'
                    success(command([*compiler, 'core', 'emit-obj', path,
                                     '--target', target, level, '-o', obj]))
                    data = obj.read_bytes()
                    machine = 62 if target == 'x86_64' else 183
                    require(len(data) >= 20 and data[:4] == b'\x7fELF' and
                            struct.unpack_from('<H', data, 18)[0] == machine,
                            f'{name}: incorrect {target} object')
                comparisons += 1
    # This positive control proves the byte comparison detects relevant changes.
    changed = out / 'different.jhc'
    changed.write_text(export('(uadd x 1)'))
    plain = out / 'identity-plain.jhc'
    require(success(command([*compiler, 'core', 'emit-mir', changed])) !=
            success(command([*compiler, 'core', 'emit-mir', plain])),
            'MIR comparison did not distinguish a runtime change')
    for name, (diagnostic, source) in INVALID.items():
        path = out / f'{name}.jhc'
        path.write_text(source)
        result = command([*compiler, 'core', 'emit-mir', path])
        require(result.returncode != 0 and diagnostic.encode() in result.stderr,
                f'{name}: wrong rejection {result.stderr!r}')
        require(not result.stdout, f'{name}: emitted partial MIR')
    print(f'erasure lowering: {comparisons} exact MIR twin comparisons; '
          f'{2 * comparisons} target objects; {len(INVALID)} diagnostic rejections; '
          'runtime-change control passed; no programs executed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-erasure-') as folder:
        test(shlex.split(args.compiler), Path(folder))


if __name__ == '__main__':
    main()
