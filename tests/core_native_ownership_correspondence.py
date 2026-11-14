#!/usr/bin/env python3
"""Actual Core buffer snapshots checked by closed resource-gated admission.

Observations retain full arenas. Synthetic mutations separately test ownership,
mode authority, typed buffer lengths and graph validity. This is regression
evidence, not a theorem about native IO, heap execution or source refinement.
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
from core_native_kernel_correspondence import Snapshot
from core_typing_producer import require

CASES = {'alloc': ('(def value (Buffer 2) (alloc 2 (int 0)))', True),
 'store': ('(def value (Buffer 2) (store (alloc 2 (int 0)) 0 (int 9) (decide-lt 0 2)))', True),
 'free': ('(def value U64 (free (alloc 2 (int 0)) 7))', True),
 'owned-fn': ('(def value (pi b (Buffer 2) U64) (lam b (Buffer 2) (free b 7)))', True),
 'buffer-id': ('(def value (pi b (Buffer 2) (Buffer 2)) (lam b (Buffer 2) b))', True),
 'load': ('(def value I64 (load (alloc 2 (int 0)) 0 (decide-lt 0 2) (lam x I64 (lam b (Buffer 2) '
          '(free b x)))))',
          True),
 'load-owner-before-index': ('(def value (pi n U64 (pi b (Buffer n) (pi i U64 (pi0 p (Lt i n) I64)))) '
                      '(lam n U64 (lam b (Buffer n) (lam i U64 (lam0 p (Lt i n) (load b i p (lam x '
                      'I64 (lam again (Buffer n) (free again x)))))))))',
                      True),
 'borrowed-index': ('(def value (pi r (Ref (Buffer 2)) I64) (lam r (Ref (Buffer 2)) (index r 0 '
                    '(decide-lt 0 2))))',
                    True),
 'ref-formation': ('(def value (Type 0) (Ref (Buffer 2)))', True),
 'ghost-borrow-deref': ('(def value (Eq (free (deref (borrow (alloc 2 (int 0)))) 0) (free (deref '
                        '(borrow (alloc 2 (int 0)))) 0)) (refl (free (deref (borrow (alloc 2 (int '
                        '0)))) 0)))',
                        True),
 'wrong-ref': ('(def value (Type 0) (Ref U64))', False),
 'runtime-borrow': ('(def value (Ref (Buffer 2)) (borrow (alloc 2 (int 0))))', False),
 'runtime-deref': ('(def value (Buffer 2) (deref (borrow (alloc 2 (int 0)))))', False),
 'load-function': ('(def value (pi y U64 U64) (load (alloc 2 (int 0)) 0 (decide-lt 0 2) (lam x I64 '
                   '(lam b (Buffer 2) (free b (lam y U64 y))))))',
                   False),
 'load-wrong-buffer': ('(def value I64 (load (alloc 2 (int 0)) 0 (decide-lt 0 2) (lam x I64 (lam b '
                       '(Buffer 3) (free b x)))))',
                       False),
 'leak': ('(def value (pi b (Buffer 2) U64) (lam b (Buffer 2) 7))', False),
 'double': ('(def value (pi b (Buffer 2) U64) (lam b (Buffer 2) (free b (free b 7))))', False)}
CASES['load-open-length'] = (
    '(def value (pi n U64 (pi i U64 (pi0 p (Lt i n) (pi b (Buffer n) I64)))) '
    '(lam n U64 (lam i U64 (lam0 p (Lt i n) (lam b (Buffer n) '
    '(load b i p (lam x I64 (lam again (Buffer n) (free again x)))))))))', True)
CASES['two-owners-later-scalar'] = (
    '(def value (pi b (Buffer 2) (pi c (Buffer 2) (pi x U64 U64))) '
    '(lam b (Buffer 2) (lam c (Buffer 2) (lam x U64 (free b (free c x))))))', True)
CASES['owner-first-later-scalar'] = (
    '(def value (pi b (Buffer 2) (pi x U64 U64)) '
    '(lam b (Buffer 2) (lam x U64 (free b x))))', True)
CASES['captured-owner'] = (
    '(def value (pi b (Buffer 2) (pi x U64 (Buffer 2))) '
    '(lam b (Buffer 2) (free (alloc 0 (int 0)) (lam x U64 b))))', False)
CASES['partial-owned-capture'] = (
    '(def value (pi x U64 (Buffer 2)) '
    '(app (lam b (Buffer 2) (lam x U64 b)) (alloc 2 (int 0))))', False)

NATIVE_DIAGNOSTICS = {'captured-owner': b'cannot capture an owned value',
                      'partial-owned-capture': b'partial application'}


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
                f'{name}: resource admission changed: {result.stderr!r}')
        if admitted:
            require(result.stdout == b'exact resource-gated native declaration accepted\n',
                    f'{name}: missing acknowledgement')
        return {'case': name, 'origin': origin,
                'admission': 'accept' if admitted else 'reject',
                'sha256': hashlib.sha256(payload).hexdigest()}

    for name, (source, native) in CASES.items():
        (output / f'{name}.core').write_text(source + '\n')
        result = command([exporter, 'code-require'], source.encode())
        (output / f'{name}.native.stderr').write_bytes(result.stderr)
        require((result.returncode == 0) == native,
                f'{name}: Core outcome changed: {result.stderr!r}')
        if name in NATIVE_DIAGNOSTICS:
            require(NATIVE_DIAGNOSTICS[name] in result.stderr,
                    f'{name}: wrong native rejection boundary: {result.stderr!r}')
        observations.append({'case': name, 'native': 'accept' if native else 'reject',
                             'source_sha256': hashlib.sha256(source.encode()).hexdigest()})
        if native:
            Snapshot.read(result.stdout)
            retained[name] = result.stdout
            checks.append(check(name, result.stdout, True, 'actual Core.check/require'))

    owned = Snapshot.read(retained['owned-fn'])
    _, flag, (domain, free) = owned.nodes[owned.term]
    _, _, (variable, result) = owned.nodes[free]
    leaked = copy.deepcopy(owned)
    leaked.nodes[leaked.term] = (45, flag, (domain, result))
    checks.append(check('synthetic-owner-leak', leaked.encode(), False, 'synthetic'))
    leaked.ghost = 1
    checks.append(check('synthetic-ghost-forgery', leaked.encode(), False, 'synthetic'))

    doubled = copy.deepcopy(owned)
    double = len(doubled.nodes)
    doubled.nodes.append((31, (), (variable, free)))
    doubled.term = len(doubled.nodes)
    doubled.nodes.append((45, flag, (domain, double)))
    checks.append(check('synthetic-owner-duplicate', doubled.encode(), False, 'synthetic'))

    captured = copy.deepcopy(owned)
    scalar = captured.nodes[captured.type][2][1]
    outer = len(captured.nodes)
    captured.nodes.append((0, (1,), ()))
    inner = len(captured.nodes)
    captured.nodes.append((45, (0,), (scalar, outer)))
    barrier = len(captured.nodes)
    captured.nodes.append((16, (), (result, inner)))
    captured.term = len(captured.nodes)
    captured.nodes.append((45, (0,), (domain, barrier)))
    inner_type = len(captured.nodes)
    captured.nodes.append((44, (0,), (scalar, domain)))
    captured.type = len(captured.nodes)
    captured.nodes.append((44, (0,), (domain, inner_type)))
    checks.append(check('synthetic-owner-capture', captured.encode(), False, 'synthetic'))

    load = Snapshot.read(retained['load'])
    _, _, (buffer, index, proof, continuation) = load.nodes[load.term]
    _, _, (value_type, again) = load.nodes[continuation]
    _, _, (_, rest) = load.nodes[again]
    three = len(load.nodes)
    load.nodes.append((47, (3,), ()))
    wrong_buffer = len(load.nodes)
    load.nodes.append((27, (), (three,)))
    wrong_again = len(load.nodes)
    load.nodes.append((45, (0,), (wrong_buffer, rest)))
    wrong_continuation = len(load.nodes)
    load.nodes.append((45, (0,), (value_type, wrong_again)))
    load.term = len(load.nodes)
    load.nodes.append((29, (), (buffer, index, proof, wrong_continuation)))
    checks.append(check('synthetic-load-buffer-length', load.encode(), False, 'synthetic'))

    cyclic = Snapshot.read(retained['alloc'])
    cyclic.nodes.append((17, (), (len(cyclic.nodes), len(cyclic.nodes))))
    checks.append(check('synthetic-unused-cycle', cyclic.encode(), False, 'synthetic'))
    checks.append(check('synthetic-trailing-byte', retained['alloc'] + b'\n', False, 'synthetic'))
    checks.append(check('synthetic-empty', b'', False, 'synthetic'))
    (output / 'manifest.json').write_text(json.dumps({
        'claim': 'source regression evidence; native execution and heap refinement remain separate',
        'core_sha256': hashlib.sha256((ROOT / 'compiler/core.jh').read_bytes()).hexdigest(),
        'exporter_sha256': hashlib.sha256((ROOT / 'compiler/core_native_snapshot.jh').read_bytes()).hexdigest(),
        'cases': observations, 'checks': checks}, indent=2) + '\n')
    print(f'native ownership correspondence: {len(observations)} source fixtures and '
          f'{len(checks)} exact-byte checks passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeOwnership.lean')
    parser.add_argument('--proofs', type=Path, default=ROOT / 'proofs')
    parser.add_argument('--exporter', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        run(shlex.split(args.compiler), shlex.split(args.checker), args.output.resolve(),
            args.proofs.resolve(), args.exporter)
    else:
        with tempfile.TemporaryDirectory(prefix='native-ownership-correspondence-') as directory:
            run(shlex.split(args.compiler), shlex.split(args.checker), Path(directory),
                args.proofs.resolve(), args.exporter)

if __name__ == '__main__':
    main()
