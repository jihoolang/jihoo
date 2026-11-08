#!/usr/bin/env python3
"""Probe current Core.runtime_uses and Core.check on quantity control cases.

The source/control correspondence is hand-selected regression evidence, not a
verified translation. All compiler and probe processes have explicit timeouts
and failure checks; assertions are not used as acceptance guards.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import shlex
import tempfile
from core_certificate_process import ROOT, command, success
from core_typing_producer import require

# Expected count, full-kernel diagnostic (None means accepted), result type, body.
CASES = {
    'single': (1, None, 'I64', '(free b (int 0))'),
    'duplicate': (2, 'an owned value is used more than once', 'I64',
                  '(free b (free b (int 0)))'),
    'discard': (0, 'an owned value must be used', 'I64', '(int 0)'),
    'balanced': (1, None, 'I64',
                 '(if-lt 0 1 p (free b (int 1)) (free b (int 2)))'),
    'once': (1, None, 'I64', '(app (lam x I64 (free b x)) (int 2))'),
    'accumulator': (1, None, '(Buffer 1)',
                    '(fold 2 b (lam i U64 (lam0 p (Lt i 2) (lam acc (Buffer 1) acc))))'),
    'trap-before': (1, None, 'U64',
                    '(app (lam x U64 (free b x)) (uadd 18446744073709551615 1))'),
    'trap-after': (1, None, 'U64',
                   '(free b (uadd 18446744073709551615 1))'),
}
REJECTED = {
    'unbalanced': ('both branches must use an owned value alike', 'I64',
                   '(if-lt 0 1 p (free b (int 1)) (int 2))'),
    'closure': ('a function cannot capture an owned value', '(pi x I64 I64)',
                '(lam x I64 (free b x))'),
    'repeated-capture': ('a loop body runs many times', 'I64',
                        '(fold 2 (int 0) (lam i U64 (lam0 p (Lt i 2) (lam acc I64 (free b acc)))))'),
}


def source(result, body):
    return f'(def f (pi b (Buffer 1) {result}) (lam b (Buffer 1) {body}))\n'.encode()


def test(compiler, out):
    probe = out / 'quantity-probe'
    success(command([*compiler, 'build', '-O0', '-I', 'compiler',
                     'tests/core_quantity_probe.jh', '-o', probe], cwd=ROOT))
    for name, (count, diagnostic, result, body) in CASES.items():
        program = source(result, body)
        observed = success(command([probe, 'count'], program))
        require(observed == f'{count}\n'.encode(), f'{name}: wrong use count {observed!r}')
        checked = command([probe, 'check'], program)
        if diagnostic is None:
            require(success(checked) == observed, f'{name}: checking changed the count')
        else:
            require(checked.returncode != 0 and diagnostic.encode() in checked.stderr,
                    f'{name}: wrong kernel rejection {checked.stderr!r}')
    for name, (diagnostic, result, body) in REJECTED.items():
        rejected = command([probe, 'count'], source(result, body))
        require(rejected.returncode != 0 and diagnostic.encode() in rejected.stderr,
                f'{name}: wrong quantity rejection {rejected.stderr!r}')
    # Positive controls: branch, immediate call and accumulator above repair
    # the respective rejected unbalanced/captured/loop forms.
    print('quantity controls: 8 actual use counts, 6 kernel acceptances, '
          '2 linear-use rejections and 3 capture/branch rejections passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-quantity-') as folder:
        test(shlex.split(args.compiler), Path(folder))

if __name__ == '__main__':
    main()
