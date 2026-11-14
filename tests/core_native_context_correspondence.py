#!/usr/bin/env python3
"""Actual context/signature programs checked by the same unified native gate.

Kinds, erasures, owned signatures and family metadata come from the admitted
program. Synthetic mutations test the independent validator with canonical
backward arenas. Source/IO and native heap refinement remain separate obligations.
Run local compiler/checker jobs through scripts/proof-limits.sh.
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


CASES = {'generic-id': ('(def value (pi A (Type 0) (pi x A A)) (lam A (Type 0) (lam x A x)))', True),
 'generic-id-u64': ('(def value U64 (app (lam A (Type 0) (lam x A x)) U64 7))', True),
 'first-order-family-id': ('(def value (pi F (pi n U64 (Type 0)) (pi n U64 (pi x (app F n) (app F '
                           'n)))) (lam F (pi n U64 (Type 0)) (lam n U64 (lam x (app F n) x))))',
                           True),
 'first-order-family-array': ('(def value (Array 0) (app (lam F (pi n U64 (Type 0)) (lam n U64 '
                              '(lam x (app F n) x))) (lam n U64 (Array n)) 0 (array)))',
                              True),
 'unknown-scalar-callee': ('(def value (pi f (pi n U64 U64) U64) (lam f (pi n U64 U64) (app f 0)))',
                           True),
 'unknown-owned-callee': ('(def value (pi f (pi b (Buffer 2) (Buffer 2)) (pi b (Buffer 2) (Buffer '
                          '2))) (lam f (pi b (Buffer 2) (Buffer 2)) (lam b (Buffer 2) (app f b))))',
                          True),
 'owned-known-later-scalar': ('(def value U64 (app (lam b (Buffer 2) (lam n U64 (free b n))) '
                              '(alloc 2 (int 0)) 0))',
                              True),
 'unknown-dependent-erasures': ('(def value (pi f (pi0 n U64 (pi b (Buffer n) (Buffer n))) (Buffer '
                                '2)) (lam f (pi0 n U64 (pi b (Buffer n) (Buffer n))) (app f 2 '
                                '(alloc 2 (int 0)))))',
                                True),
 'unknown-generic-signature': ('(def value (pi f (pi A (Type 0) (pi x A A)) U64) (lam f (pi A '
                               '(Type 0) (pi x A A)) (app f U64 0)))',
                               True),
 'computed-callee-memory': ('(def value (Buffer 2) (app (free (alloc 1 (int 0)) (lam b (Buffer 2) '
                            'b)) (alloc 2 (int 0))))',
                            True),
 'scalar-factory': ('(def value (pi b (Buffer 2) (Buffer 2)) (app (lam n U64 (lam b (Buffer 2) b)) '
                    '0))',
                    True),
 'unknown-scalar-factory': ('(def value (pi f (pi n U64 (pi b (Buffer 2) (Buffer 2))) (pi b '
                            '(Buffer 2) (Buffer 2))) (lam f (pi n U64 (pi b (Buffer 2) (Buffer '
                            '2))) (app f 0)))',
                            True),
 'family-unplain-typed-index': ('(def value (pi F (pi n U64 (Type 0)) (pi h (pi A (Type 0) U64) '
                                '(pi x (app F (app h (Buffer 0))) (app F (app h (Buffer 0)))))) '
                                '(lam F (pi n U64 (Type 0)) (lam h (pi A (Type 0) U64) (lam x (app '
                                'F (app h (Buffer 0))) x))))',
                                True),
 'family-above-word-index': ('(def value (pi F (pi n U64 (Type 0)) (Type 0)) (lam F (pi n U64 '
                             '(Type 0)) (app F (uadd 18446744073709551615 18446744073709551615))))',
                             True),
 'owned-free-function': ('(def value (pi b (Buffer 2) U64) (lam b (Buffer 2) (free b 0)))', True),
 'partial-owner-capture': ('(def value (pi n U64 (Buffer 2)) (app (lam b (Buffer 2) (lam n U64 b)) '
                           '(alloc 2 (int 0))))',
                           False),
 'owner-leak': ('(def value (pi b (Buffer 2) U64) (lam b (Buffer 2) 0))', False),
 'owner-double': ('(def value (pi b (Buffer 2) (Buffer 2)) (lam b (Buffer 2) (free b b)))', False),
 'outer-owned-capture': ('(def value (pi b (Buffer 2) (pi n U64 (Buffer 2))) (lam b (Buffer 2) '
                         '(app (lam n U64 (lam m U64 b)) 0)))',
                         False),
 'owned-type-forgery': ('(def value (Buffer 2) (app (lam A (Type 0) (lam x A x)) (Buffer 2) (alloc '
                        '2 (int 0))))',
                        False),
 'higher-order-kind-argument': ('(def value U64 (app (lam F (pi A (Type 0) (Type 0)) 0) (lam A '
                                '(Type 0) U64)))',
                                False),
 'wrong-dependent-buffer': ('(def value (pi f (pi0 n U64 (pi b (Buffer n) (Buffer n))) (Buffer 2)) '
                            '(lam f (pi0 n U64 (pi b (Buffer n) (Buffer n))) (app f 3 (alloc 2 '
                            '(int 0)))))',
                            False),
 'owned-abstract-result': ('(def value (pi T (Type 0) (pi f (pi b (Buffer 2) T) (pi b (Buffer 2) '
                           'T))) (lam T (Type 0) (lam f (pi b (Buffer 2) T) (lam b (Buffer 2) (app '
                           'f b)))))',
                           True),
 'owned-indexed-abstract-result': ('(def value (pi F (pi n U64 (Type 0)) (pi n U64 (pi f (pi b '
                                   '(Buffer 2) (app F n)) (pi b (Buffer 2) (app F n))))) (lam F '
                                   '(pi n U64 (Type 0)) (lam n U64 (lam f (pi b (Buffer 2) (app F '
                                   'n)) (lam b (Buffer 2) (app f b))))))',
                                   True),
 'owned-indexed-unplain-result': ('(def value (pi F (pi n U64 (Type 0)) (pi h (pi A (Type 0) U64) '
                                  '(pi f (pi b (Buffer 2) (app F (app h (Buffer 0)))) (pi b '
                                  '(Buffer 2) (app F (app h (Buffer 0))))))) (lam F (pi n U64 '
                                  '(Type 0)) (lam h (pi A (Type 0) U64) (lam f (pi b (Buffer 2) '
                                  '(app F (app h (Buffer 0)))) (lam b (Buffer 2) (app f b))))))',
                                  True),
 'owned-unknown-factory-capture': ('(def value (pi f (pi b (Buffer 2) (pi n U64 (Buffer 2))) (pi n '
                                   'U64 (Buffer 2))) (lam f (pi b (Buffer 2) (pi n U64 (Buffer '
                                   '2))) (app f (alloc 2 (int 0)))))',
                                   False),
 'boxed-unknown-callee': ('(data Box (base (pi b (Buffer 2) Box)) (step (pi b Box Box))) (def '
                          'value (pi f (pi b Box Box) (pi b Box Box)) (lam f (pi b Box Box) (lam b '
                          'Box (app f b))))',
                          True),
 'boxed-known-callee': ('(data Box (base (pi b (Buffer 2) Box)) (step (pi b Box Box))) (def value '
                        '(pi b Box Box) (lam b Box (app (lam x Box x) b)))',
                        True),
 'flat-family-type-argument': ('(data Tag (tag Tag)) (def value Tag (app (lam A (Type 0) (lam x A '
                               'x)) Tag tag))',
                               True),
 'boxed-family-type-forgery': ('(data Box (base (pi b (Buffer 2) Box)) (step (pi b Box Box))) (def '
                               'value Box (app (lam A (Type 0) (lam x A x)) Box (base (alloc 2 '
                               '(int 0)))))',
                               False),
 'boxed-owner-leak': ('(data Box (base (pi b (Buffer 2) Box)) (step (pi b Box Box))) (def value '
                      '(pi b Box U64) (lam b Box 0))',
                      False),
 'global-generic-replay': ('(def id (pi A (Type 0) (pi x A A)) (lam A (Type 0) (lam x A x))) (def '
                           'value U64 (app id U64 7))',
                           True),
 'delta-kind-alias': ('(def Kind (Type 1) (Type 0)) (def id (pi A Kind (pi x A A)) (lam A Kind '
                      '(lam x A x))) (def value U64 (app id U64 7))',
                      True),
 'fold-unknown-owner-callee': ('(def value (pi f (pi b (Buffer 2) (Buffer 2)) (Buffer 2)) (lam f '
                               '(pi b (Buffer 2) (Buffer 2)) (fold 2 (alloc 2 (int 0)) (lam i U64 '
                               '(lam0 p (Lt i 2) (lam a (Buffer 2) (app f a)))))))',
                               True),
 'loop-unknown-owner-callee': ('(def value (pi f (pi b (Buffer 2) (Buffer 2)) (Buffer 2)) (lam f '
                               '(pi b (Buffer 2) (Buffer 2)) (loop 2 (lam k U64 (Buffer 2)) (alloc '
                               '2 (int 0)) (lam i U64 (lam0 p (Lt i 2) (lam a (Buffer 2) (app f '
                               'a)))))))',
                               True)}

NATIVE_DIAGNOSTICS = {
    'partial-owner-capture': b'partial application',
    'outer-owned-capture': b'cannot capture an owned value',
    'owned-unknown-factory-capture': b'partial application',
}


def run(compiler, checker, output, proofs, exporter=None):
    output.mkdir(parents=True, exist_ok=True)
    if exporter is None:
        exporter = output / 'core-native-snapshots'
        success(command([*compiler, 'build', '-O2', '-I', 'compiler',
                         'tests/core_native_snapshots.jh', '-o', exporter]))
    observations, checks, retained = [], [], {}

    def check(name, payload, admitted, origin):
        (output / f'{name}.snapshot').write_bytes(payload)
        result = command([*checker, '64', '128'], payload, cwd=proofs)
        (output / f'{name}.checker.stdout').write_bytes(result.stdout)
        (output / f'{name}.checker.stderr').write_bytes(result.stderr)
        require(result.returncode == (0 if admitted else 1),
                f'{name}: unified context admission changed: '
                f'{(result.stdout + result.stderr)!r}')
        if admitted:
            require(result.stdout == b'exact native unified program accepted\n',
                    f'{name}: missing exact-byte acknowledgement')
        checks.append({'case': name, 'origin': origin, 'accepted': admitted,
                       'sha256': hashlib.sha256(payload).hexdigest()})

    def mutation(name, program):
        require(all(ref < index for index, (_, _, refs) in enumerate(program.nodes)
                    for ref in refs), f'{name}: mutation must retain backward arena edges')
        check(name, program.encode(), False, 'synthetic')

    def append(program, tag, fields=(), refs=()):
        index = len(program.nodes)
        program.nodes.append((tag, fields, refs))
        return index

    for name, (source, accepted) in CASES.items():
        (output / f'{name}.core').write_text(source + '\n')
        result = command([exporter, 'families'], source.encode())
        (output / f'{name}.native.stderr').write_bytes(result.stderr)
        require(result.returncode == (0 if accepted else 1),
                f'{name}: native source outcome changed: {result.stderr!r}')
        if not accepted:
            require(result.stderr, f'{name}: missing native rejection diagnostic')
        if name in NATIVE_DIAGNOSTICS:
            require(NATIVE_DIAGNOSTICS[name] in result.stderr,
                    f'{name}: wrong native rejection boundary: {result.stderr!r}')
        observations.append({'case': name, 'native': accepted,
                             'source_sha256': hashlib.sha256(source.encode()).hexdigest()})
        if accepted:
            Program.read(result.stdout)
            retained[name] = result.stdout
            check(name, result.stdout, True, 'actual Core.check/require mixed program')

    owner = Program.read(retained['owned-free-function'])
    owner_type, owner_term = owner.definitions[-1]
    _, owner_flag, (owner_domain, free) = owner.nodes[owner_term]
    _, _, (variable, scalar_value) = owner.nodes[free]
    scalar_type = owner.nodes[owner_type][2][1]

    leak = copy.deepcopy(owner)
    leak.nodes[owner_term] = (45, owner_flag, (owner_domain, scalar_value))
    mutation('synthetic-owned-leak', leak)

    doubled = copy.deepcopy(owner)
    repeated = append(doubled, 31, refs=(variable, free))
    doubled.definitions[-1] = (owner_type,
                              append(doubled, 45, owner_flag, (owner_domain, repeated)))
    mutation('synthetic-owned-duplicate', doubled)

    # The Strict barrier separates a returned closure from the leading telescope.
    # This is a typed internal-tree mutation, not a source Strict fixture.
    captured = copy.deepcopy(owner)
    outer = append(captured, 0, (1,))
    inner = append(captured, 45, (0,), (scalar_type, outer))
    barrier = append(captured, 16, refs=(scalar_value, inner))
    captured_term = append(captured, 45, owner_flag, (owner_domain, barrier))
    inner_type = append(captured, 44, (0,), (scalar_type, owner_domain))
    captured_type = append(captured, 44, (0,), (owner_domain, inner_type))
    captured.definitions[-1] = (captured_type, captured_term)
    mutation('synthetic-owned-closure-capture', captured)

    # Remove the final scalar application from an otherwise accepted full call.
    # The owner-consuming prefix now returns a function that captures its owner.
    partial = Program.read(retained['owned-known-later-scalar'])
    scalar, whole_call = partial.definitions[-1]
    tag, _, (first_call, _) = partial.nodes[whole_call]
    require(tag == 46, 'partial-call source shape changed')
    result_type = append(partial, 44, (0,), (scalar, scalar))
    partial.definitions[-1] = (result_type, first_call)
    mutation('synthetic-owned-partial-capture', partial)

    lookup = copy.deepcopy(owner)
    lookup.nodes[variable] = (0, (99,), ())
    mutation('synthetic-forged-context-lookup', lookup)

    signature = Program.read(retained['unknown-scalar-callee'])
    signature_type, function_term = signature.definitions[-1]
    u64 = signature.nodes[signature_type][2][1]
    _, function_flags, (_, body) = signature.nodes[function_term]
    length = append(signature, 47, (2,))
    buffer = append(signature, 27, refs=(length,))
    forged_signature = append(signature, 44, (0,), (buffer, buffer))
    forged_term = append(signature, 45, function_flags, (forged_signature, body))
    forged_type = append(signature, 44, (0,), (forged_signature, u64))
    signature.definitions[-1] = (forged_type, forged_term)
    mutation('synthetic-forged-owned-signature', signature)

    erased = Program.read(retained['generic-id'])
    generic_type, generic_term = erased.definitions[-1]
    type_tag, _, type_refs = erased.nodes[generic_type]
    term_tag, _, term_refs = erased.nodes[generic_term]
    require(type_tag == 44 and term_tag == 45, 'generic source shape changed')
    erased.nodes[generic_type] = (type_tag, (1,), type_refs)
    erased.nodes[generic_term] = (term_tag, (1,), term_refs)
    mutation('synthetic-forged-kind-erasure', erased)

    absent = Program.read(retained['boxed-unknown-callee'])
    absent.families.clear()
    mutation('synthetic-removed-family-metadata', absent)
    arity = Program.read(retained['boxed-unknown-callee'])
    arity.families[0].arity = 1
    mutation('synthetic-forged-family-arity', arity)

    check('synthetic-trailing-byte', retained['generic-id'] + b'\n', False, 'synthetic')
    check('synthetic-empty-program', b'', False, 'synthetic')
    (output / 'manifest.json').write_text(json.dumps({
        'claim': 'same unified admission regression; native source/IO and heap refinement remain open',
        'core_sha256': hashlib.sha256((ROOT / 'compiler/core.jh').read_bytes()).hexdigest(),
        'exporter_sha256': hashlib.sha256((ROOT / 'compiler/core_native_snapshot.jh').read_bytes()).hexdigest(),
        'source_cases': observations, 'checks': checks,
    }, indent=2) + '\n')
    print(f'native context correspondence: {len(observations)} source fixtures and '
          f'{len(checks)} exact-byte checks passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeUnifiedProgram.lean')
    parser.add_argument('--exporter', type=Path)
    parser.add_argument('--proofs', type=Path, default=ROOT / 'proofs')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        run(shlex.split(args.compiler), shlex.split(args.checker), args.output.resolve(),
            args.proofs.resolve(), args.exporter.resolve() if args.exporter else None)
    else:
        with tempfile.TemporaryDirectory(prefix='native-context-correspondence-') as directory:
            run(shlex.split(args.compiler), shlex.split(args.checker), Path(directory),
                args.proofs.resolve(), args.exporter.resolve() if args.exporter else None)


if __name__ == '__main__':
    main()
