#!/usr/bin/env python3
"""Compare actual checked Core binder domains with Lean-derived capabilities.

Normalization, family analysis and the observation driver are tested/trusted
boundaries. This is not an independent proof of Core.check or typed projection.
"""
import argparse
from pathlib import Path
import shlex
import tempfile
from core_certificate_process import ROOT, command, success
from core_typing_producer import require

DOMAINS = {
    'proof': (0, '(Lt 0 1)', ''),
    'proof-function': (0, '(pi n U64 (Eq n n))', ''),
    'proof-family': (0, 'Truth', '(inductive Truth 0 (truth Truth))\n'),
    'index': (1, 'U64', ''),
    'signed': (2, 'I64', ''),
    'array': (2, '(Array 2)', ''),
    'refinement': (2, '(Refine (lam n U64 (Lt 0 n)))', ''),
    'flat': (3, 'Flag', '(data Flag (No Flag) (Yes Flag))\n'),
    'recursive': (4, 'List', '(data List (Nil List) (Cons (pi rest List List)))\n'),
    'heap-field': (4, 'Box', '(data Box (Boxed (pi b (Buffer 1) Box)))\n'),
    'buffer': (5, '(Buffer 1)', ''),
    'back': (6, '(Back (Buffer 1) (lam x (Buffer 1) I64))', ''),
    'borrow': (7, '(Ref (Buffer 1))', ''),
    'function': (8, '(pi n U64 U64)', ''),
    'universe': (8, '(Type 0)', ''),
    'normalized-buffer': (5, '(app (lam A (Type 0) A) (Buffer 1))', ''),
}


def program(erased, domain, prefix, discard=False):
    suffix = '0' if erased else ''
    result, body = ('I64', '(int 0)') if erased or discard else (domain, 'x')
    return (prefix + f'(def target (pi{suffix} x {domain} {result}) '
            f'(lam{suffix} x {domain} {body}))\n').encode()


def test(compiler, out):
    table = {}
    for line in (ROOT / 'tests/core_binder_modes.txt').read_text().splitlines():
        erased, tag, mode, lend = map(int, line.split())
        require((erased, tag) not in table, 'duplicate capability fixture')
        table[erased, tag] = mode, lend
    require(set(table) == {(e, t) for e in range(2) for t in range(9)}, 'incomplete fixture')
    probe = out / 'binder-probe'
    success(command([*compiler, 'build', '-O0', '-I', 'compiler',
                     'tests/core_binder_probe.jh', '-o', probe], cwd=ROOT))
    accepted = rejected = drop_checks = 0
    for name, (tag, domain, prefix) in DOMAINS.items():
        for erased in (0, 1):
            mode, lend = table[erased, tag]
            observed = command([probe], program(erased, domain, prefix))
            if mode < 0:
                diagnostic = (b'proof binders must be erased' if not erased else
                              b'erased binders must be propositions, u64 or data')
                require(observed.returncode != 0 and not observed.stdout and diagnostic in observed.stderr,
                        f'{name}/{erased}: wrong erasure rejection {observed.stderr!r}')
                rejected += 1
                continue
            rows = [tuple(map(int, line.split())) for line in success(observed).splitlines()]
            require(len(rows) == 1 and rows[0][:2] == (erased, tag),
                    f'{name}/{erased}: wrong checked-domain observation {rows}')
            require((not erased and rows[0][2] == 1) == bool(lend),
                    f'{name}: lendability differs from actual Core.owned')
            accepted += 1
            if not erased:
                dropped = command([probe], program(erased, domain, prefix, discard=True))
                if mode == 1:
                    require(dropped.returncode != 0 and not dropped.stdout and b'an owned value must be used' in dropped.stderr,
                            f'{name}: linear domain incorrectly discardable {dropped.stderr!r}')
                else:
                    success(dropped)
                drop_checks += 1
    telescope = (b'(def target (pi n U64 (pi0 p (Lt n 1) (pi b (Buffer n) (Buffer n)))) '
                 b'(lam n U64 (lam0 p (Lt n 1) (lam b (Buffer n) b))))')
    require(success(command([probe], telescope)) == b'0 1 0\n1 0 0\n0 5 1\n',
            'dependent telescope lost original binding context')
    neutral = b'(def target (pi A (Type 0) (pi x A A)) (lam A (Type 0) (lam x A x)))'
    require(success(command([probe], neutral)) == b'0 8 0\n0 8 0\n',
            'neutral type-argument context was not retained')
    invalid_context = (b'(def target (pi b (Buffer 1) (pi0 bad (Buffer 1) (Buffer 1))) '
                       b'(lam b (Buffer 1) (lam0 bad (Buffer 1) b)))')
    invalid = command([probe], invalid_context)
    require(invalid.returncode != 0 and not invalid.stdout and
            b'erased binders must be propositions, u64 or data' in invalid.stderr,
            'invalid later binder leaked observations from the valid prefix')
    repaired_context = (b'(def target (pi b (Buffer 1) (pi0 n U64 (Buffer 1))) '
                        b'(lam b (Buffer 1) (lam0 n U64 b)))')
    require(success(command([probe], repaired_context)) == b'0 5 1\n1 1 0\n',
            'repaired complete-context control failed')
    # Neutral type variables are not a license to instantiate with owned types.
    plain_argument = (b'(def target (pi n U64 U64) (lam n U64 '
                      b'(app (lam A (Type 0) (lam x A x)) U64 n)))')
    require(success(command([probe], plain_argument)) == b'0 1 0\n',
            'first-order type-argument control failed')
    owned_argument = (b'(def target (pi b (Buffer 1) (Buffer 1)) (lam b (Buffer 1) '
                      b'(app (lam A (Type 0) (lam x A x)) (Buffer 1) b)))')
    forbidden = command([probe], owned_argument)
    require(forbidden.returncode != 0 and not forbidden.stdout and
            b'a type argument holds no buffer, heap data, borrow or function' in forbidden.stderr,
            f'owned type instantiation: wrong rejection {forbidden.stderr!r}')
    # A Back is linear but is not an owned value accepted by Lend.
    bad_lend = (b'(def target (pi x (Back (Buffer 1) (lam b (Buffer 1) I64)) I64) '
                b'(lam x (Back (Buffer 1) (lam b (Buffer 1) I64)) '
                b'(lend x (lam r I64 r) (lam y I64 (lam z I64 z)))))')
    rejected_lend = command([probe], bad_lend)
    require(rejected_lend.returncode != 0 and not rejected_lend.stdout and b'only an owned value is lent' in rejected_lend.stderr,
            f'Back incorrectly lent or wrong failure: {rejected_lend.stderr!r}')
    print(f'binder projection: {accepted} checked domains, {rejected} erasure rejections, '
          f'{drop_checks} discard checks, 2 dependent telescopes, a complete-context pair, a first-order argument pair and Back lend rejection passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-binder-') as folder:
        test(shlex.split(args.compiler), Path(folder))

if __name__ == '__main__':
    main()
