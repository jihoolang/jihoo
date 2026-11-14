#!/usr/bin/env python3
"""Actual Core owner-return programs versus the unified exact-byte gate.

The receiver recomputes family storage metadata and checks every closed code
body's quantities. Mutations are synthetic; these fixtures are not a proof of
native execution, source IO fidelity or heap safety.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
from pathlib import Path
import shlex
import tempfile
from core_certificate_process import ROOT, command, success
from core_native_family_correspondence import Program
from core_typing_producer import require

CASES = {'back-type': ('(def value (Type 0) (Back (Buffer 2) (lam b (Buffer 2) U64)))', True, None),
 'back-proof-type': ('(def value (Type 0) (Back0 (Buffer 2) (lam b (Buffer 2) (Eq 0 0))))',
                     True,
                     None),
 'give-scalar': ('(def value (Back (Buffer 2) (lam b (Buffer 2) U64)) (give (lam b (Buffer 2) U64) '
                 '(alloc 2 (int 0)) 7))',
                 True,
                 None),
 'give-erased': ('(def value (Back0 (Buffer 2) (lam b (Buffer 2) (Eq 0 0))) (give0 (lam b (Buffer '
                 '2) (Eq 0 0)) (alloc 2 (int 0)) (refl 0)))',
                 True,
                 None),
 'back-package-id': ('(def value (pi z (Back (Buffer 2) (lam b (Buffer 2) U64)) (Back (Buffer 2) '
                     '(lam b (Buffer 2) U64))) (lam z (Back (Buffer 2) (lam b (Buffer 2) U64)) z))',
                     True,
                     None),
 'give-dependent-proof': ('(def value (Back0 (Buffer 2) (lam b (Buffer 2) (Eq (free b 0) (free b '
                          '0)))) (give0 (lam b (Buffer 2) (Eq (free b 0) (free b 0))) (alloc 2 '
                          '(int 0)) (refl (free (alloc 2 (int 0)) 0))))',
                          True,
                          None),
 'give-owned-result': ('(def value (Back (Buffer 2) (lam b (Buffer 2) (Buffer 3))) (give (lam b '
                       '(Buffer 2) (Buffer 3)) (alloc 2 (int 0)) (alloc 3 (int 0))))',
                       True,
                       None),
 'take-scalar': ('(def value U64 (take (give (lam b (Buffer 2) U64) (alloc 2 (int 0)) 7) (lam b '
                 '(Buffer 2) (lam a U64 (free b a)))))',
                 True,
                 None),
 'take-erased': ('(def value U64 (take (give0 (lam b (Buffer 2) (Eq 0 0)) (alloc 2 (int 0)) (refl '
                 '0)) (lam b (Buffer 2) (lam0 p (Eq 0 0) (free b 7)))))',
                 True,
                 None),
 'take-dependent-proof': ('(def value U64 (take (give0 (lam b (Buffer 2) (Eq (free b 0) (free b '
                          '0))) (alloc 2 (int 0)) (refl (free (alloc 2 (int 0)) 0))) (lam b '
                          '(Buffer 2) (lam0 p (Eq (free b 0) (free b 0)) (free b 7)))))',
                          True,
                          None),
 'take-owner-return': ('(def value (Buffer 2) (take (give (lam b (Buffer 2) U64) (alloc 2 (int 0)) '
                       '7) (lam b (Buffer 2) (lam a U64 b))))',
                       True,
                       None),
 'take-owned-result': ('(def value (Buffer 3) (take (give (lam b (Buffer 2) (Buffer 3)) (alloc 2 '
                       '(int 0)) (alloc 3 (int 0))) (lam b (Buffer 2) (lam c (Buffer 3) (free b '
                       'c)))))',
                       True,
                       None),
 'ghost-take-function-result': ('(def value (Eq (app (take (give (lam b (Buffer 2) U64) (alloc 2 '
                                '(int 0)) 7) (lam b (Buffer 2) (lam a U64 (free b (lam x U64 '
                                'x))))) 0) (app (take (give (lam b (Buffer 2) U64) (alloc 2 (int '
                                '0)) 7) (lam b (Buffer 2) (lam a U64 (free b (lam x U64 x))))) 0)) '
                                '(refl (app (take (give (lam b (Buffer 2) U64) (alloc 2 (int 0)) '
                                '7) (lam b (Buffer 2) (lam a U64 (free b (lam x U64 x))))) 0)))',
                                True,
                                None),
 'boxed-owner': ('(data Box (box (pi b (Buffer 2) Box))) (def value Box (take (give (lam b Box '
                 'U64) (box (alloc 2 (int 0))) 7) (lam b Box (lam a U64 b))))',
                 True,
                 None),
 'boxed-result': ('(data Box (box (pi b (Buffer 2) Box))) (def value Box (take (give (lam b '
                  '(Buffer 2) Box) (alloc 2 (int 0)) (box (alloc 2 (int 0)))) (lam b (Buffer 2) '
                  '(lam a Box (free b a)))))',
                  True,
                  None),
 'nonowned-back': ('(def value (Type 0) (Back U64 (lam b U64 U64)))',
                   False,
                   b'an owner given back'),
 'wrong-erasure': ('(def value (Type 0) (Back0 (Buffer 2) (lam b (Buffer 2) U64)))',
                   False,
                   b'only a proposition'),
 'wrong-nonerasure': ('(def value (Type 0) (Back (Buffer 2) (lam b (Buffer 2) (Eq 0 0))))',
                      False,
                      b'only a proposition'),
 'array-result': ('(def value (Type 0) (Back (Buffer 2) (lam b (Buffer 2) (Array 0))))',
                  False,
                  b'one representation'),
 'borrow-result': ('(def value (Type 0) (Back (Buffer 2) (lam b (Buffer 2) (Ref (Buffer 2)))))',
                   False,
                   b'one representation'),
 'function-result-motive': ('(def value (Type 0) (Back (Buffer 2) (lam b (Buffer 2) (pi a U64 '
                            'U64))))',
                            False,
                            b'one representation'),
 'flat-family-result': ('(data Bit (zero Bit) (one Bit)) (def value (Type 0) (Back (Buffer 2) (lam '
                        'b (Buffer 2) Bit)))',
                        False,
                        b'one representation'),
 'nonowned-give': ('(def value U64 (give (lam b U64 U64) 7 0))', False, b'an owner given back'),
 'wrong-give-result': ('(def value (Back (Buffer 2) (lam b (Buffer 2) U64)) (give (lam b (Buffer '
                       '2) U64) (alloc 2 (int 0)) (int 7)))',
                       False,
                       b'type mismatch'),
 'take-missing-lambda': ('(def value U64 (take (give (lam b (Buffer 2) U64) (alloc 2 (int 0)) 7) '
                         '(lam b (Buffer 2) (free b 7))))',
                         False,
                         b'take continues'),
 'take-wrong-erasure': ('(def value U64 (take (give0 (lam b (Buffer 2) (Eq 0 0)) (alloc 2 (int 0)) '
                        '(refl 0)) (lam b (Buffer 2) (lam p (Eq 0 0) (free b 7)))))',
                        False,
                        b"take's result is erased"),
 'take-wrong-owner': ('(def value U64 (take (give (lam b (Buffer 2) U64) (alloc 2 (int 0)) 7) (lam '
                      'b (Buffer 3) (lam a U64 (free b a)))))',
                      False,
                      b'take continues with the owner'),
 'take-wrong-result-domain': ('(def value U64 (take (give (lam b (Buffer 2) U64) (alloc 2 (int 0)) '
                              '7) (lam b (Buffer 2) (lam a I64 (free b 7)))))',
                              False,
                              b'take continues with the owner'),
 'take-function-result-code': ('(def value (pi x U64 U64) (take (give (lam b (Buffer 2) U64) '
                               '(alloc 2 (int 0)) 7) (lam b (Buffer 2) (lam a U64 (free b (lam x '
                               'U64 x))))))',
                               False,
                               b"continuation's result is not a function"),
 'take-owner-leak': ('(def value U64 (take (give (lam b (Buffer 2) U64) (alloc 2 (int 0)) 7) (lam '
                     'b (Buffer 2) (lam a U64 a))))',
                     False,
                     b'owned value must be used'),
 'take-owner-duplicate': ('(def value U64 (take (give (lam b (Buffer 2) U64) (alloc 2 (int 0)) 7) '
                          '(lam b (Buffer 2) (lam a U64 (free b (free b a))))))',
                          False,
                          b'owned value is used more than once'),
 'i64-result': ('(def value I64 (take (give (lam b (Buffer 2) I64) (alloc 2 (int 0)) (int 7)) (lam '
                'b (Buffer 2) (lam a I64 (free b a)))))',
                True,
                None),
 'refinement-result': ('(def value U64 (take (give (lam b (Buffer 2) (Refine (lam n U64 (Eq n '
                       'n)))) (alloc 2 (int 0)) (pack (lam n U64 (Eq n n)) 7 (refl 7))) (lam b '
                       '(Buffer 2) (lam a (Refine (lam n U64 (Eq n n))) (free b (witness a))))))',
                       True,
                       None),
 'nested-back-result': ('(def value (Back (Buffer 2) (lam b (Buffer 2) U64)) (take (give (lam b '
                        '(Buffer 2) (Back (Buffer 2) (lam b (Buffer 2) U64))) (alloc 2 (int 0)) '
                        '(give (lam b (Buffer 2) U64) (alloc 2 (int 0)) 7)) (lam b (Buffer 2) (lam '
                        'a (Back (Buffer 2) (lam b (Buffer 2) U64)) (free b a)))))',
                        True,
                        None),
 'linear-package-not-owned': ('(def value (Type 0) (Back (Back (Buffer 2) (lam b (Buffer 2) U64)) '
                              '(lam b (Back (Buffer 2) (lam b (Buffer 2) U64)) U64)))',
                              False,
                              b'an owner given back'),
 'take-owner-dependent-result-rejected': ('(def value (pi F (pi b (Buffer 2) (Type 0)) (pi0 p (Lt '
                                          '0 0) U64)) (lam F (pi b (Buffer 2) (Type 0)) (lam0 p '
                                          '(Lt 0 0) (take (give (lam b (Buffer 2) U64) (alloc 2 '
                                          '(int 0)) 7) (lam b (Buffer 2) (lam a U64 (free b '
                                          '(absurd (app F b) p))))))))',
                                          False,
                                          b"take's type depends on neither the owner nor its res"
                                          b'ult'),
 'take-result-dependent-result-rejected': ('(def value (pi F (pi a U64 (Type 0)) (pi0 p (Lt 0 0) '
                                           'U64)) (lam F (pi a U64 (Type 0)) (lam0 p (Lt 0 0) '
                                           '(take (give (lam b (Buffer 2) U64) (alloc 2 (int 0)) '
                                           '7) (lam b (Buffer 2) (lam a U64 (free b (absurd (app F '
                                           'a) p))))))))',
                                           False,
                                           b"take's type depends on neither the owner nor its res"
                                           b'ult')}

def run(compiler, checker, output, proofs, exporter=None):
    output.mkdir(parents=True, exist_ok=True)
    if exporter is None:
        exporter = output / 'core-native-snapshots'
        success(command([*compiler, 'build', '-O2', '-I', 'compiler',
                         'tests/core_native_snapshots.jh', '-o', exporter]))
    retained, observations, checks = {}, [], []

    def check(name, payload, admitted, origin):
        (output / f'{name}.snapshot').write_bytes(payload)
        result = command([*checker, '64', '128'], payload, cwd=proofs)
        (output / f'{name}.checker.stdout').write_bytes(result.stdout)
        (output / f'{name}.checker.stderr').write_bytes(result.stderr)
        require(result.returncode == (0 if admitted else 1),
                f'{name}: unified admission changed: {result.stderr!r}')
        if admitted:
            require(result.stdout == b'exact native unified program accepted\n',
                    f'{name}: missing acknowledgement')
        return {'case': name, 'origin': origin, 'admission': 'accept' if admitted else 'reject',
                'sha256': hashlib.sha256(payload).hexdigest()}

    for name, (source, native, diagnostic) in CASES.items():
        (output / f'{name}.core').write_text(source + '\n')
        result = command([exporter, 'families'], source.encode())
        (output / f'{name}.native.stderr').write_bytes(result.stderr)
        require((result.returncode == 0) == native,
                f'{name}: Core outcome changed: {result.stderr!r}')
        if diagnostic is not None:
            require(diagnostic in result.stderr,
                    f'{name}: wrong native rejection boundary: {result.stderr!r}')
        observations.append({'case': name, 'native': 'accept' if native else 'reject',
                             'source_sha256': hashlib.sha256(source.encode()).hexdigest()})
        if native:
            Program.read(result.stdout)
            retained[name] = result.stdout
            checks.append(check(name, result.stdout, True, 'actual Core.check'))

    def append(program, tag, fields=(), refs=()):
        index = len(program.nodes)
        program.nodes.append((tag, fields, refs))
        return index

    original = Program.read(retained['take-scalar'])
    ty, take = original.definitions[0]
    _, _, (value, continuation) = original.nodes[take]
    _, _, (owner_type, inner) = original.nodes[continuation]
    _, flag, (result_type, rest) = original.nodes[inner]
    _, _, (owner_var, result_var) = original.nodes[rest]

    leaked = copy.deepcopy(original)
    leaked.nodes[inner] = (45, flag, (result_type, result_var))
    checks.append(check('synthetic-take-owner-leak', leaked.encode(), False, 'synthetic'))

    doubled = copy.deepcopy(original)
    twice = append(doubled, 31, refs=(owner_var, rest))
    second = append(doubled, 45, flag, (result_type, twice))
    first = append(doubled, 45, (0,), (owner_type, second))
    selected = append(doubled, 37, refs=(value, first))
    doubled.definitions[0] = (ty, selected)
    checks.append(check('synthetic-take-owner-duplicate', doubled.encode(), False, 'synthetic'))

    wrong_owner = copy.deepcopy(original)
    three = append(wrong_owner, 47, (3,))
    buffer = append(wrong_owner, 27, refs=(three,))
    first = append(wrong_owner, 45, (0,), (buffer, inner))
    selected = append(wrong_owner, 37, refs=(value, first))
    wrong_owner.definitions[0] = (ty, selected)
    checks.append(check('synthetic-take-wrong-owner-domain', wrong_owner.encode(), False, 'synthetic'))

    erased = Program.read(retained['take-erased'])
    _, selected = erased.definitions[0]
    continuation = erased.nodes[selected][2][1]
    second = erased.nodes[continuation][2][1]
    tag, _, refs = erased.nodes[second]
    erased.nodes[second] = (tag, (0,), refs)
    checks.append(check('synthetic-take-forged-erasure', erased.encode(), False, 'synthetic'))

    wrong_give = Program.read(retained['give-erased'])
    _, selected = wrong_give.definitions[0]
    tag, _, refs = wrong_give.nodes[selected]
    wrong_give.nodes[selected] = (tag, (0,), refs)
    checks.append(check('synthetic-give-forged-erasure', wrong_give.encode(), False, 'synthetic'))

    borrowed_result = Program.read(retained['back-type'])
    ty, selected = borrowed_result.definitions[0]
    _, flag, (owner_type, motive) = borrowed_result.nodes[selected]
    _, motive_flag, (domain, _) = borrowed_result.nodes[motive]
    borrowed = append(borrowed_result, 33, refs=(owner_type,))
    motive = append(borrowed_result, 45, motive_flag, (domain, borrowed))
    selected = append(borrowed_result, 35, flag, (owner_type, motive))
    borrowed_result.definitions[0] = (ty, selected)
    checks.append(check('synthetic-back-borrow-representation', borrowed_result.encode(), False, 'synthetic'))

    flat = Program.read(retained['boxed-owner'])
    family = flat.families[0]
    old_constructor = family.constructors[0]
    _, _, (_, family_result) = flat.nodes[old_constructor]
    scalar = next(i for i, (tag, _, _) in enumerate(flat.nodes) if tag == 4)
    family.constructors[0] = append(flat, 44, (0,), (scalar, family_result))
    ty, selected = flat.definitions[0]
    value, continuation = flat.nodes[selected][2]
    _, give_flag, (motive, owned, result) = flat.nodes[value]
    _, con_payload, _ = flat.nodes[owned]
    zero = append(flat, 47, (0,))
    owned = append(flat, 12, con_payload, (zero,))
    value = append(flat, 36, give_flag, (motive, owned, result))
    selected = append(flat, 37, refs=(value, continuation))
    flat.definitions[0] = (ty, selected)
    checks.append(check('synthetic-family-boxed-forgery', flat.encode(), False, 'synthetic'))

    cyclic = Program.read(retained['give-scalar'])
    cyclic.nodes.append((17, (), (len(cyclic.nodes), len(cyclic.nodes))))
    checks.append(check('synthetic-unused-cycle', cyclic.encode(), False, 'synthetic'))
    checks.append(check('synthetic-trailing-byte', retained['give-scalar'] + b'\n', False, 'synthetic'))
    checks.append(check('synthetic-empty', b'', False, 'synthetic'))
    (output / 'manifest.json').write_text(json.dumps({
        'claim': 'regression evidence; native heap execution and source refinement are separate',
        'core_sha256': hashlib.sha256((ROOT / 'compiler/core.jh').read_bytes()).hexdigest(),
        'exporter_sha256': hashlib.sha256((ROOT / 'compiler/core_native_snapshot.jh').read_bytes()).hexdigest(),
        'cases': observations, 'checks': checks}, indent=2) + '\n')
    print(f'native owner-return correspondence: {len(observations)} source fixtures and '
          f'{len(checks)} exact-byte checks passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeUnifiedProgram.lean')
    parser.add_argument('--proofs', type=Path, default=ROOT / 'proofs')
    parser.add_argument('--exporter', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        run(shlex.split(args.compiler), shlex.split(args.checker), args.output.resolve(),
            args.proofs.resolve(), args.exporter)
    else:
        with tempfile.TemporaryDirectory(prefix='native-back-correspondence-') as directory:
            run(shlex.split(args.compiler), shlex.split(args.checker), Path(directory),
                args.proofs.resolve(), args.exporter)

if __name__ == '__main__':
    main()
