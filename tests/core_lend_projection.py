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
        if tag in ('u', 'q'):
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


def lower(c, checked=True):
    if c[0] in ('p', 'u'): return c
    if c[0] == 'q': return ('p',)
    if c[0] == 's': return ('s', lower(c[1], checked), lower(c[2], checked))
    owner, mode, read, rest = c[1:]
    before = ('b', 3, lower(read, checked))
    # Returned slot 0 aliases owner+1 under the still-live result binder.
    after = ('b', mode, rename(lower(rest, checked), lambda k: owner+1 if k == 0 else k-1))
    if checked:
        require(demand(before, owner) == 0, 'reader consumed lent owner')
        require(demand(after, owner) == 1, 'continuation did not consume owner exactly once')
    return ('s', before, after)


def relabel(c, mapping):
    if c[0] == 'p': return c
    if c[0] == 'u':
        value = mapping(c[1])
        return ('p',) if value is None else ('u', value)
    if c[0] == 's': return ('s', relabel(c[1], mapping), relabel(c[2], mapping))
    require(c[0] == 'b', 'relabel expects projected scopes')
    def lifted(k):
        if k == 0: return 0
        value = mapping(k-1)
        return None if value is None else value+1
    return ('b', c[1], relabel(c[2], lifted))


def substitute_source(c, substitution):
    # Keep borrow pointer identity before erasing its quantity event. Equal
    # owner types must not make Borrow(otherOwner) an acceptable replacement.
    def lift(mapping):
        def apply(k):
            if k == 0: return ('u', 0)
            tag, value = mapping(k-1)
            return (tag, value+1)
        return apply
    if c[0] == 'p': return c
    if c[0] == 'u': return substitution(c[1])
    if c[0] == 'q':
        tag, value = substitution(c[1])
        require(tag == 'u', 'substituted borrow owner is not a variable')
        return ('q', value)
    if c[0] == 's': return ('s', substitute_source(c[1], substitution), substitute_source(c[2], substitution))
    require(c[0] == 'l', 'unexpected annotated source')
    tag, owner = substitution(c[1])
    require(tag == 'u', 'substituted Lend owner is not a variable')
    return ('l', owner, c[2], substitute_source(c[3], lift(substitution)),
            substitute_source(c[4], lift(lift(substitution))))


def substitution_case(probe, data):
    lines = success(command([probe, 'substitute'], data)).decode().splitlines()
    require(len(lines) == 7, 'incomplete substitution observation')
    owner = int(lines[0])
    # This compares the total quantity-annotated source projection from the new
    # commutation theorem. Guarded graph admission is tested separately above.
    raw_read, raw_read_after, raw_rest, raw_rest_after = [parse(row) for row in lines[1:5]]
    require(substitute_source(raw_read, lambda k: ('q', owner) if k == 0 else ('u', k-1)) == raw_read_after,
            'Core reader substitution changed borrow-owner identity or captured a slot')
    require(substitute_source(raw_rest, lambda k: ('u', owner+1) if k == 0 else ('u', k-1)) == raw_rest_after,
            'Core continuation substitution disagrees with annotated source substitution')
    read, read_after, rest, rest_after = [lower(row, checked=False) for row in
                                        (raw_read, raw_read_after, raw_rest, raw_rest_after)]
    expected_read = relabel(read, lambda k: None if k == 0 else k-1)
    expected_rest = rename(rest, lambda k: owner+1 if k == 0 else k-1)
    require(expected_read == read_after, 'Core borrow substitution disagrees with control projection')
    require(expected_rest == rest_after, 'Core returned-owner substitution captured a slot')
    read_counts = list(map(int, lines[5].split()))
    rest_counts = list(map(int, lines[6].split()))
    require([demand(read_after, k) for k in range(len(read_counts))] == read_counts,
            'transformed reader differs from actual Core.runtime_uses')
    require([demand(rest_after, k) for k in range(len(rest_counts))] == rest_counts,
            'transformed continuation differs from actual Core.runtime_uses')
    require(read_counts[owner] == 0 and rest_counts[owner+1] == 1,
            'substitution changed the lent-owner quantity obligation')


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
    for body in CASES.values():
        substitution_case(probe, source(body))
    substitution_case(probe, two)
    dependent = (b'(def target (pi n U64 (pi0 p (Lt 0 n) (pi b (Buffer n) I64))) '
                 b'(lam n U64 (lam0 p (Lt 0 n) (lam b (Buffer n) '
                 b'(lend b (lam r (Ref (Buffer n)) (int 0)) '
                 b'(lam x I64 (lam returned (Buffer n) (free returned x))))))))')
    substitution_case(probe, dependent)
    # A nested reader/continuation referring to the original outer name requires
    # the outer alias substitution before a nested local owner check.
    nested_original = CASES['nested'].replace('(free back (add x y))', '(free b (add x y))')
    substitution_case(probe, source(nested_original))
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
        for mode in ('4096', 'substitute'):
            failed = command([probe, mode], source(body))
            require(failed.returncode != 0 and not failed.stdout and diagnostic in failed.stderr,
                    f'{name}/{mode}: wrong rejection {failed.stderr!r}')
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
        failed = command([probe, 'substitute'], source(body))
        diagnostic = b'substitution requires a lend' if name == 'branch' else b'substitution requires a variable owner'
        require(failed.returncode != 0 and not failed.stdout and diagnostic in failed.stderr,
                f'{name}: substitution exclusion leaked output {failed.stderr!r}')
    print('Lend projection: 7 checked programs, exact/short work budgets, 7 intended rejections and 2 checked exclusions passed')
    print('Lend substitution: 9 whole-checked programs, both actual Core.substitute results and all contextual use counts matched')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-lend-projection-') as folder:
        test(shlex.split(args.compiler), Path(folder))

if __name__ == '__main__': main()
