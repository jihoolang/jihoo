#!/usr/bin/env python3
"""Finite actual-Core/structural-control comparisons, not a refinement proof."""
import argparse
from pathlib import Path
import re
import shlex
import tempfile
from core_certificate_process import ROOT, command, success
from core_typing_producer import require


def parse(text):
    tokens = iter(re.findall(r'\(|\)|[^\s()]+', text))
    def node(token):
        if token == 'p':
            return ('p',)
        require(token == '(', 'bad control opening')
        tag = next(tokens)
        if tag == 'u':
            out = (tag, int(next(tokens)))
        elif tag == 's':
            out = (tag, node(next(tokens)), node(next(tokens)))
        elif tag == 'l':
            out = (tag, int(next(tokens)), int(next(tokens)), node(next(tokens)), node(next(tokens)))
        else:
            raise ValueError('unknown control tag')
        require(next(tokens) == ')', 'bad control closing')
        return out
    result = node(next(tokens))
    require(next(tokens, None) is None, 'trailing control')
    return result


def rename(c, mapping):
    if c[0] == 'p': return c
    if c[0] == 'u': return ('u', mapping(c[1]))
    if c[0] == 's': return ('s', rename(c[1], mapping), rename(c[2], mapping))
    require(c[0] == 'b', 'rename expects lowered scopes')
    return ('b', c[1], rename(c[2], lambda k: 0 if k == 0 else mapping(k-1)+1))


def demand(c, k):
    if c[0] == 'p': return 0
    if c[0] == 'u': return int(c[1] == k)
    if c[0] == 's': return demand(c[1], k) + demand(c[2], k)
    mode, body = c[1:]
    if mode in (0, 1):
        require(demand(body, 0) == mode, 'fresh result quantity mismatch')
    return demand(body, k+1)


def lower(c):
    if c[0] in ('p', 'u'): return c
    if c[0] == 's': return ('s', lower(c[1]), lower(c[2]))
    owner, mode, read, rest = c[1:]
    before = ('b', 3, lower(read))
    # Returned slot 0 aliases owner+1 under the still-live result binder.
    after = ('b', mode, rename(lower(rest), lambda k: owner+1 if k == 0 else k-1))
    require(demand(before, owner) == 0, 'reader consumed lent owner')
    require(demand(after, owner) == 1, 'continuation did not consume owner exactly once')
    return ('s', before, after)


def lend(rest, read='(index r 0 (decide-lt 0 1))', result='I64', owner='b'):
    return (f'(lend {owner} (lam r (Ref (Buffer 1)) {read}) '
            f'(lam x {result} (lam returned (Buffer 1) {rest})))')


def source(body):
    return f'(def target (pi b (Buffer 1) I64) (lam b (Buffer 1) {body}))'.encode()


CASES = {
    'returned': lend('(free returned x)'),
    'original': lend('(free b x)'),
    'borrow-original': lend('(free returned x)', '(index (borrow b) 0 (decide-lt 0 1))'),
    'read-twice': lend('(free returned x)', '(add (index r 0 (decide-lt 0 1)) (index r 0 (decide-lt 0 1)))'),
    'owned-result': lend('(free returned (free x (int 0)))', '(alloc 1 (int 7))', '(Buffer 1)'),
    'nested': lend('(lend returned (lam s (Ref (Buffer 1)) (index s 0 (decide-lt 0 1))) '
                   '(lam y I64 (lam back (Buffer 1) (free back (add x y)))))'),
}


def test(compiler, out):
    probe = out / 'lend-probe'
    success(command([*compiler, 'build', '-O0', '-I', 'compiler',
                     'tests/core_lend_projection_probe.jh', '-o', probe], cwd=ROOT))
    for name, body in CASES.items():
        data = source(body)
        lines = success(command([probe, '4096'], data)).decode().splitlines()
        control = lower(parse(lines[0]))
        counts = list(map(int, lines[1].split()))
        require(counts == [1] and demand(control, 0) == counts[0], f'{name}: Core/projected use mismatch')
        used = 4096 - int(lines[2])
        require(used > 0, 'projection did not debit work')
        exact = success(command([probe, str(used)], data)).decode().splitlines()
        require(exact[0] == lines[0] and exact[2] == '0', 'exact work budget failed')
        failed = command([probe, str(used-1)], data)
        require(failed.returncode != 0 and not failed.stdout and
                b'projection work limit reached' in failed.stderr, 'short work budget leaked partial result')
    # Both equal-typed original owners must retain distinct identities under scopes.
    two = (b'(def target (pi b (Buffer 1) (pi c (Buffer 1) I64)) '
           b'(lam b (Buffer 1) (lam c (Buffer 1) '
           + lend('(free returned (free c x))').encode() + b')))')
    lines = success(command([probe, '4096'], two)).decode().splitlines()
    require(list(map(int, lines[1].split())) == [1, 1], 'Core owner control failed')
    control = lower(parse(lines[0]))
    require([demand(control, k) for k in range(2)] == [1, 1], 'projection merged distinct owners')
    # These whole-Core-invalid programs must fail before producing any control.
    invalid = {
        'reader-consumes': (lend('(free returned x)', '(free b (int 0))'), b'an owned value is used more than once'),
        'double-owner': (lend('(free returned (free b x))'), b'exactly once'),
        'missing-owner': (lend('x'), b'exactly once'),
        'missing-result': (lend('(free returned (int 0))', '(alloc 1 (int 7))', '(Buffer 1)'), b'owned value must be used'),
    }
    valid = lend('(free returned x)')
    invalid.update({
        'wrong-reader-domain': (valid.replace('(Ref (Buffer 1))', '(Ref (Buffer 2))'),
                                b'a lend reads through a borrow of its owner'),
        'wrong-result-domain': (valid.replace('(lam x I64', '(lam x U64'),
                                b'a lend continues with the result and the owner'),
        'wrong-returned-domain': (valid.replace('(lam returned (Buffer 1)', '(lam returned (Buffer 2)'),
                                  b'a lend continues with the result and the owner'),
    })
    for name, (body, diagnostic) in invalid.items():
        failed = command([probe, '4096'], source(body))
        require(failed.returncode != 0 and not failed.stdout and diagnostic in failed.stderr,
                f'{name}: wrong rejection {failed.stderr!r}')
    excluded = {
        'branch': '(if-lt 0 1 p (free b (int 0)) (free b (int 0)))',
        'computed-owner': lend('(free returned x)', owner='(app (lam z (Buffer 1) z) b)'),
    }
    for name, body in excluded.items():
        require(success(command([probe, 'check'], source(body))) == b'checked\n', f'{name}: invalid positive control')
        failed = command([probe, '4096'], source(body))
        diagnostic = b'unsupported projection node' if name == 'branch' else b'non-variable lend owner'
        require(failed.returncode != 0 and not failed.stdout and diagnostic in failed.stderr,
                f'{name}: wrong exclusion {failed.stderr!r}')
    print('Lend projection: 7 checked programs, exact/short work budgets, 7 intended rejections and 2 checked exclusions passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-lend-projection-') as folder:
        test(shlex.split(args.compiler), Path(folder))

if __name__ == '__main__': main()
