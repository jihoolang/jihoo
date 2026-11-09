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


# Mixed telescopes and genuine dependent lends: the returned owner name is an
# alias, not a fresh independent linear resource. Core validates that identity.
def lend(rest, reader='(index r 0 (decide-lt 0 1))', reader_type='I64'):
    return (f'(lend b (lam r (Ref (Buffer 1)) {reader}) '
            f'(lam x {reader_type} (lam returned (Buffer 1) {rest})))')

CASES.update({
    'unrestricted-unequal': (1, None, 'U64',
        '(app (lam x U64 (if-lt x 1 p (free b (uadd x x)) (free b x))) 0)'),
    'erased-slot': (1, None, 'I64', '(app (lam0 n U64 (free b (int 0))) 2)'),
    'mixed-telescope': (1, None, 'I64',
        '(app (lam n U64 (lam0 p (Lt n 3) (lam y I64 (free b (add y y))))) '
        '1 (decide-lt 1 3) (int 5))'),
    'erased-runtime-control': (1, None, 'U64',
        '(app (lam0 n U64 (free b 0)) 1)'),
    'erased-runtime-use': (1, 'erased value used at runtime', 'U64',
        '(app (lam0 n U64 (free b n)) 1)'),
    'lend-returned-name': (1, None, 'I64', lend('(free returned x)')),
    'lend-original-name': (1, None, 'I64', lend('(free b x)')),
    'lend-alternate-names': (1, None, 'I64',
        lend('(if-lt 0 1 p (free b x) (free returned x))')),
    'lend-under-local': (1, None, 'I64',
        lend('(app (lam z U64 (if-lt z 1 p (free b x) (free returned x))) 0)')),
    'lend-shadowed-slot': (1, None, 'I64',
        lend('(app (lam returned I64 (free b returned)) x)')),
    'lend-nested-alias': (1, None, 'I64', lend(
        '(lend returned (lam r (Ref (Buffer 1)) (index r 0 (decide-lt 0 1))) '
        '(lam y I64 (lam returned2 (Buffer 1) (free b (add x y)))))')),
    'lend-double-alias': (2, 'a lent owner is used exactly once after its lend', 'I64',
        lend('(free b (free returned x))')),
    'lend-discard-alias': (0, 'a lent owner is used exactly once after its lend', 'I64',
        lend('(int 0)')),
    'borrow-repeated-read': (1, None, 'I64', lend('(free returned x)',
        '(add (index r 0 (decide-lt 0 1)) (index r 0 (decide-lt 0 1)))')),
    'borrow-unequal-reads': (1, None, 'I64', lend('(free returned x)',
        '(if-lt 0 1 p (index r 0 (decide-lt 0 1)) '
        '(add (index r 0 (decide-lt 0 1)) (index r 0 (decide-lt 0 1))))')),
    'distinct-owner-discard': (1, 'an owned value must be used', 'I64',
        '(app (lam other (Buffer 1) (free b (int 0))) (alloc 1 (int 0)))'),
    'distinct-owners-consumed': (1, None, 'I64',
        '(app (lam other (Buffer 1) (free b (free other (int 0)))) (alloc 1 (int 0)))'),
    # Quantity one alone does not prove a borrowed result safe to return.
    'borrow-escape': (1, 'a borrow cannot outlive its lend', 'I64',
        lend('(free returned (int 0))', 'r', '(Ref (Buffer 1))')),
})


# Erasure/slot-compaction controls. These are implementation regressions, not a
# verified projection into Quantity.Erasure. The unannotated single/once cases
# above are positive controls for the same surviving owner demand.
CASES.update({
    'erase-two-proof-slots': (1, None, 'I64',
        '(app (lam0 p (Eq 1 1) (lam0 q (Lt 0 1) (free b (int 7)))) '
        '(refl 1) (decide-lt 0 1))'),
    'erase-around-local-owner': (1, None, 'I64',
        '(app (lam0 p (Eq 1 1) (app (lam local (Buffer 1) '
        '(app (lam0 q (Lt 0 1) (free local (free b (int 7)))) (decide-lt 0 1))) '
        '(alloc 1 (int 0)))) (refl 1))'),
    'erase-under-branch': (1, None, 'I64',
        '(app (lam0 p (Eq 1 1) (if-lt 0 1 q '
        '(free b (int 7)) (free b (int 8)))) (refl 1))'),
    'erase-trap-before': (1, None, 'U64',
        '(app (lam0 p (Eq 1 1) (app (lam x U64 (free b x)) '
        '(uadd 18446744073709551615 1))) (refl 1))'),
    'erase-trap-after': (1, None, 'U64',
        '(app (lam0 p (Eq 1 1) (free b (uadd 18446744073709551615 1))) (refl 1))'),
    'erase-cannot-hide-duplication': (2, 'an owned value is used more than once', 'I64',
        '(app (lam0 p (Eq 1 1) (free b (free b (int 7)))) (refl 1))'),
    'erase-cannot-hide-local-discard': (1, 'an owned value must be used', 'I64',
        '(app (lam0 p (Eq 1 1) (app (lam local (Buffer 1) (free b (int 7))) '
        '(alloc 1 (int 0)))) (refl 1))'),
})


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
    accepted = sum(diagnostic is None for _, diagnostic, _, _ in CASES.values())
    print(f'quantity controls: {len(CASES)} actual use counts, {accepted} kernel acceptances, '
          f'{len(CASES)-accepted} kernel rejections and {len(REJECTED)} capture/branch rejections passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-quantity-') as folder:
        test(shlex.split(args.compiler), Path(folder))

if __name__ == '__main__':
    main()
