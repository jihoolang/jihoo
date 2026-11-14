#!/usr/bin/env python3
"""Actual mixed-program bytes checked by the unified typed environment kernel.

Native execution/IO refinement remains outside the pure admission theorem.
Run local compiler jobs through scripts/proof-limits.sh.
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
from core_native_family_correspondence import CASES as FAMILY_CASES, Program
from core_native_ownership_correspondence import CASES as OWNERSHIP_CASES
from core_typing_producer import require


CASES = {name: (source, native, native)
         for name, (source, native, _) in FAMILY_CASES.items()}
CASES.update({f'resource-{name}': (source, native, native)
              for name, (source, native) in OWNERSHIP_CASES.items()})
CASES.update({
    'boxed-global': ('(data Box (box (pi b (Buffer 2) Box))) '
                     '(def value Box (box (alloc 2 (int 0))))', True, True),
    'boxed-family-field': ('(data Box (box (pi b (Buffer 2) Box))) '
                           '(data Outer (outer (pi b Box Outer))) '
                           '(def value Outer (outer (box (alloc 2 (int 0)))))', True, True),
    'flat-family-global': ('(data A (a A)) (data B (b (pi x A B))) '
                           '(def value B (b a))', True, True),
    'recursive-value': ('(data Nat (zero Nat) (succ (pi n Nat Nat))) '
                         '(def value Nat (succ (succ zero)))', True, True),
    'dependent-buffer-value': ('(data Box 1 1 (box (pi0 n U64 (pi b (Buffer n) (Box n))))) '
                               '(def value (Box 2) (box 2 (alloc 2 (int 0))))', True, True),
    'later-global-uses-family-value': ('(data Bit (zero Bit) (one Bit)) '
                                      '(def first Bit one) (def second Bit first)', True, True),
    'family-between-values': ('(data A (a A)) (def first A a) '
                              '(data B (b (pi x A B))) (def second B (b first))', True, True),
})


def run(compiler, checker, output, exporter=None):
    output.mkdir(parents=True, exist_ok=True)
    if exporter is None:
        exporter = output / 'core-native-snapshots'
        success(command([*compiler, 'build', '-O2', '-I', 'compiler',
                         'tests/core_native_snapshots.jh', '-o', exporter]))
    observations, checks, retained = [], [], {}

    def check(name, payload, accepted, origin):
        (output / f'{name}.snapshot').write_bytes(payload)
        result = command([*checker, '64', '128'], payload, cwd=ROOT / 'proofs')
        (output / f'{name}.checker.stdout').write_bytes(result.stdout)
        (output / f'{name}.checker.stderr').write_bytes(result.stderr)
        require(result.returncode == (0 if accepted else 1),
                f'{name}: unified admission changed: {(result.stdout + result.stderr)!r}')
        if accepted:
            require(result.stdout == b'exact native unified program accepted\n',
                    f'{name}: missing exact-byte acknowledgement')
        return {'case': name, 'origin': origin, 'accepted': accepted,
                'sha256': hashlib.sha256(payload).hexdigest()}

    for name, (source, native, admitted) in CASES.items():
        (output / f'{name}.jhc').write_text(source + '\n')
        result = command([exporter, 'families'], source.encode())
        (output / f'{name}.native.stderr').write_bytes(result.stderr)
        require((result.returncode == 0) == native,
                f'{name}: native mixed program changed: {result.stderr!r}')
        observations.append({'case': name, 'native': native,
                             'source_sha256': hashlib.sha256(source.encode()).hexdigest()})
        if native:
            Program.read(result.stdout)
            retained[name] = result.stdout
            checks.append(check(name, result.stdout, admitted, 'actual Core exporter'))
        else:
            require(result.stderr, f'{name}: missing native rejection diagnostic')

    # Mutate independently of the producer: no native checker approval is assumed.
    owner = Program.read(retained['resource-owned-fn'])
    ty, term = owner.definitions[-1]
    _, flags, (domain, body) = owner.nodes[term]
    _, _, (_, result) = owner.nodes[body]
    leaked = copy.deepcopy(owner)
    leaked.nodes[term] = (45, flags, (domain, result))
    checks.append(check('mutated-owned-leak', leaked.encode(), False, 'synthetic'))
    duplicated = copy.deepcopy(owner)
    variable = owner.nodes[body][2][0]
    extra = len(duplicated.nodes)
    duplicated.nodes.append((31, (), (variable, body)))
    duplicated.definitions[-1] = (ty, len(duplicated.nodes))
    duplicated.nodes.append((45, flags, (domain, extra)))
    require(all(ref < i for i, (_, _, refs) in enumerate(duplicated.nodes) for ref in refs),
            'duplicate-use mutation must retain backward arena edges')
    checks.append(check('mutated-owned-duplicate', duplicated.encode(), False, 'synthetic'))

    dependent = Program.read(retained['dependent-buffer-value'])
    wrong_length = copy.deepcopy(dependent)
    # Change allocation length only, preserving the dependent declared result.
    allocation = next(i for i, (tag, _, _) in enumerate(wrong_length.nodes) if tag == 28)
    tag, payload, (_, init) = wrong_length.nodes[allocation]
    three = len(wrong_length.nodes)
    wrong_length.nodes.append((47, (3,), ()))
    replacement = len(wrong_length.nodes)
    wrong_length.nodes.append((tag, payload, (three, init)))
    # Rebuild affected ancestors in topological order so this is a typing
    # mutation, not an accidental invalid forward edge in the arena.
    redirects = {allocation: replacement}
    for index, (op, fields, refs) in enumerate(dependent.nodes):
        if index == allocation:
            continue
        rewritten = tuple(redirects.get(ref, ref) for ref in refs)
        if rewritten != refs:
            redirects[index] = len(wrong_length.nodes)
            wrong_length.nodes.append((op, fields, rewritten))
    wrong_length.definitions = [(redirects.get(t, t), redirects.get(v, v))
                                for t, v in wrong_length.definitions]
    for family in wrong_length.families:
        family.constructors = [redirects.get(root, root) for root in family.constructors]
    require(all(ref < i for i, (_, _, refs) in enumerate(wrong_length.nodes) for ref in refs),
            'length mutation must retain backward arena edges')
    checks.append(check('mutated-dependent-buffer-length', wrong_length.encode(), False, 'synthetic'))
    no_signature = Program.read(retained['boxed-global'])
    no_signature.families.clear()
    checks.append(check('mutated-missing-family', no_signature.encode(), False, 'synthetic'))
    cyclic = Program.read(retained['boxed-global'])
    cyclic.nodes.append((17, (), (len(cyclic.nodes), len(cyclic.nodes))))
    checks.append(check('mutated-unused-cycle', cyclic.encode(), False, 'synthetic'))
    checks.append(check('mutated-trailing-byte', retained['boxed-global'] + b'\n', False, 'synthetic'))
    checks.append(check('mutated-empty', b'', False, 'synthetic'))
    (output / 'manifest.json').write_text(json.dumps({
        'claim': 'exact-byte regression evidence; native source operational refinement remains open',
        'core_sha256': hashlib.sha256((ROOT / 'compiler/core.jh').read_bytes()).hexdigest(),
        'exporter_sha256': hashlib.sha256((ROOT / 'compiler/core_native_snapshot.jh').read_bytes()).hexdigest(),
        'cases': observations, 'checks': checks}, indent=2) + '\n')
    print(f'native unified correspondence: {len(observations)} source fixtures and '
          f'{len(checks)} exact-byte checks passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeUnifiedProgram.lean')
    parser.add_argument('--exporter', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        run(shlex.split(args.compiler), shlex.split(args.checker), args.output.resolve(), args.exporter)
    else:
        with tempfile.TemporaryDirectory(prefix='native-unified-correspondence-') as directory:
            run(shlex.split(args.compiler), shlex.split(args.checker), Path(directory), args.exporter)


if __name__ == '__main__':
    main()
