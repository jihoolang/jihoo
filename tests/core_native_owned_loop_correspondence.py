#!/usr/bin/env python3
"""Actual native owned iterations checked by the unified declaration gate.

The retained count is the original bound in all callback annotations. Unknown
step callees use actual context-indexed signature replay. No loop unrolling or
native heap refinement theorem is supplied by this regression runner.
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

CASES = {'fold-buffer-store': ('(def value (Buffer 2) (fold 2 (alloc 2 (int 0)) (lam i U64 (lam0 p (Lt i '
                       '2) (lam a (Buffer 2) (store a i (int 7) p))))))',
                       True,
                       True,
                       None),
 'fold-buffer-free-alloc': ('(def value (Buffer 2) (fold 2 (alloc 2 (int 0)) (lam i U64 (lam0 p '
                            '(Lt i 2) (lam a (Buffer 2) (free a (alloc 2 (int 0))))))))',
                            True,
                            True,
                            None),
 'loop-buffer-store': ('(def value (Buffer 2) (loop 2 (lam k U64 (Buffer 2)) (alloc 2 (int 0)) '
                       '(lam i U64 (lam0 p (Lt i 2) (lam a (Buffer 2) (store a i (int 7) p))))))',
                       True,
                       True,
                       None),
 'loop-buffer-free-alloc': ('(def value (Buffer 2) (loop 2 (lam k U64 (Buffer 2)) (alloc 2 (int '
                            '0)) (lam i U64 (lam0 p (Lt i 2) (lam a (Buffer 2) (free a (alloc 2 '
                            '(int 0))))))))',
                            True,
                            True,
                            None),
 'loop-growing-buffer-alias-annotation': ('(def value (Buffer 2) (loop 2 (lam k U64 (Buffer k)) '
                                          '(alloc 0 (int 0)) (lam i U64 (lam0 p (Lt i 2) (lam a '
                                          '(app (lam k U64 (Buffer k)) i) (free a (alloc (uadd i '
                                          '1) (int 0))))))))',
                                          True,
                                          True,
                                          None),
 'fold-open-count-original-bound': ('(def value (pi n U64 (Buffer n)) (lam n U64 (fold n (alloc n '
                                    '(int 0)) (lam i U64 (lam0 p (Lt i n) (lam a (Buffer n) (store '
                                    'a i (int 7) p)))))))',
                                    True,
                                    True,
                                    None),
 'loop-indexed-buffer-acu': ('(def value (pi n U64 (Buffer (uadd n 2))) (lam n U64 (loop 2 (lam k '
                             'U64 (Buffer (uadd n k))) (alloc n (int 0)) (lam i U64 (lam0 p (Lt i '
                             '2) (lam a (Buffer (uadd n i)) (free a (alloc (uadd (uadd n i) 1) '
                             '(int 0)))))))))',
                             True,
                             True,
                             None),
 'fold-boxed-accumulator': ('(data Box (base (pi b (Buffer 2) Box)) (step (pi b Box Box))) (def '
                            'value Box (fold 2 (base (alloc 2 (int 0))) (lam i U64 (lam0 p (Lt i '
                            '2) (lam a Box (step a))))))',
                            True,
                            True,
                            None),
 'loop-boxed-accumulator': ('(data Box (base (pi b (Buffer 2) Box)) (step (pi b Box Box))) (def '
                            'value Box (loop 2 (lam k U64 Box) (base (alloc 2 (int 0))) (lam i U64 '
                            '(lam0 p (Lt i 2) (lam a Box (step a))))))',
                            True,
                            True,
                            None),
 'fold-i64-memory-body': ('(def value I64 (fold 2 (int 0) (lam i U64 (lam0 p (Lt i 2) (lam a I64 '
                          '(free (alloc 1 (int 0)) (add a (int 1))))))))',
                          True,
                          True,
                          None),
 'loop-u64-memory-body': ('(def value U64 (loop 2 (lam k U64 U64) 0 (lam i U64 (lam0 p (Lt i 2) '
                          '(lam a U64 (free (alloc 1 (int 0)) (uadd a 1)))))))',
                          True,
                          True,
                          None),
 'fold-pure-function-factory': ('(def value (Buffer 2) (fold 2 (alloc 2 (int 0)) (app (lam ignored '
                                'U64 (lam i U64 (lam0 p (Lt i 2) (lam a (Buffer 2) a)))) 0)))',
                                True,
                                True,
                                None),
 'loop-pure-function-factory': ('(def value (Buffer 2) (loop 2 (lam k U64 (Buffer 2)) (alloc 2 '
                                '(int 0)) (app (lam ignored U64 (lam i U64 (lam0 p (Lt i 2) (lam a '
                                '(Buffer 2) a)))) 0)))',
                                True,
                                True,
                                None),
 'fold-function-parameter': ('(def value (pi f (pi i U64 (pi0 p (Lt i 2) (pi a (Buffer 2) (Buffer '
                             '2)))) (Buffer 2)) (lam f (pi i U64 (pi0 p (Lt i 2) (pi a (Buffer 2) '
                             '(Buffer 2)))) (fold 2 (alloc 2 (int 0)) f)))',
                             True,
                             True,
                             None),
 'loop-function-parameter': ('(def value (pi f (pi i U64 (pi0 p (Lt i 2) (pi a (Buffer 2) (Buffer '
                             '2)))) (Buffer 2)) (lam f (pi i U64 (pi0 p (Lt i 2) (pi a (Buffer 2) '
                             '(Buffer 2)))) (loop 2 (lam k U64 (Buffer 2)) (alloc 2 (int 0)) f)))',
                             True,
                             True,
                             None),
 'fold-zero-owned': ('(def value (Buffer 2) (fold 0 (alloc 2 (int 0)) (lam i U64 (lam0 p (Lt i 0) '
                     '(lam a (Buffer 2) a)))))',
                     True,
                     True,
                     None),
 'loop-zero-owned': ('(def value (Buffer 2) (loop 0 (lam k U64 (Buffer 2)) (alloc 2 (int 0)) (lam '
                     'i U64 (lam0 p (Lt i 0) (lam a (Buffer 2) a)))))',
                     True,
                     True,
                     None),
 'fold-original-bound-mismatch': ('(def value (Buffer 2) (fold 2 (alloc 2 (int 0)) (lam i U64 '
                                  '(lam0 p (Lt i 1) (lam a (Buffer 2) a)))))',
                                  False,
                                  False,
                                  b'type mismatch'),
 'fold-unsigned-accumulator': ('(def value U64 (fold 2 0 (lam i U64 (lam0 p (Lt i 2) (lam a U64 '
                               'a)))))',
                               False,
                               False,
                               b'loop accumulator is an i64 or an owned value'),
 'loop-array-accumulator': ('(def value (Array 0) (loop 2 (lam k U64 (Array 0)) (array) (lam i U64 '
                            '(lam0 p (Lt i 2) (lam a (Array 0) a)))))',
                            False,
                            False,
                            b'scalar, a refinement or an owned value'),
 'fold-body-owner-leak': ('(def value (Buffer 2) (fold 2 (alloc 2 (int 0)) (lam i U64 (lam0 p (Lt '
                          'i 2) (lam a (Buffer 2) (alloc 2 (int 0)))))))',
                          False,
                          False,
                          b'owned value must be used'),
 'loop-body-owner-duplicate': ('(def value (Buffer 2) (loop 2 (lam k U64 (Buffer 2)) (alloc 2 (int '
                               '0)) (lam i U64 (lam0 p (Lt i 2) (lam a (Buffer 2) (free a (free a '
                               '(alloc 2 (int 0)))))))))',
                               False,
                               False,
                               b'owned value is used more than once'),
 'fold-outer-owner-capture': ('(def value (pi b (Buffer 2) (Buffer 2)) (lam b (Buffer 2) (fold 2 '
                              '(alloc 2 (int 0)) (lam i U64 (lam0 p (Lt i 2) (lam a (Buffer 2) '
                              '(free b a)))))))',
                              False,
                              False,
                              b'loop body runs many times'),
 'loop-outer-owner-capture': ('(def value (pi b (Buffer 2) (Buffer 2)) (lam b (Buffer 2) (loop 2 '
                              '(lam k U64 (Buffer 2)) (alloc 2 (int 0)) (lam i U64 (lam0 p (Lt i '
                              '2) (lam a (Buffer 2) (free b a)))))))',
                              False,
                              False,
                              b'loop body runs many times'),
 'fold-effectful-function-expression': ('(def value (Buffer 2) (fold 2 (alloc 2 (int 0)) (free '
                                        '(alloc 1 (int 0)) (lam i U64 (lam0 p (Lt i 2) (lam a '
                                        '(Buffer 2) a))))))',
                                        False,
                                        False,
                                        b'loop body that touches memory'),
 'loop-effectful-function-expression': ('(def value (Buffer 2) (loop 2 (lam k U64 (Buffer 2)) '
                                        '(alloc 2 (int 0)) (free (alloc 1 (int 0)) (lam i U64 '
                                        '(lam0 p (Lt i 2) (lam a (Buffer 2) a))))))',
                                        False,
                                        False,
                                        b'loop body that touches memory'),
 'unknown-step-call-replayed': ('(def value (pi f (pi b (Buffer 2) (Buffer 2)) (Buffer 2)) (lam f '
                                '(pi b (Buffer 2) (Buffer 2)) (fold 2 (alloc 2 (int 0)) (lam i U64 '
                                '(lam0 p (Lt i 2) (lam a (Buffer 2) (app f a)))))))',
                                True,
                                True,
                                None),
 'outer-owner-consumed-before-loop': ('(def value (pi b (Buffer 2) (Buffer 2)) (lam b (Buffer 2) '
                                      '(free b (loop 2 (lam k U64 (Buffer 2)) (alloc 2 (int 0)) '
                                      '(lam i U64 (lam0 p (Lt i 2) (lam a (Buffer 2) a)))))))',
                                      True,
                                      True,
                                      None)}

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
                f'{name}: owned iteration admission changed: {result.stderr!r}')
        if admitted:
            require(result.stdout == b'exact native unified program accepted\n',
                    f'{name}: missing acknowledgement')
        return {'case': name, 'origin': origin, 'admission': 'accept' if admitted else 'reject',
                'sha256': hashlib.sha256(payload).hexdigest()}

    for name, (source, native, admitted, diagnostic) in CASES.items():
        (output / f'{name}.core').write_text(source + '\n')
        result = command([exporter, 'families'], source.encode())
        (output / f'{name}.native.stderr').write_bytes(result.stderr)
        require((result.returncode == 0) == native,
                f'{name}: Core outcome changed: {result.stderr!r}')
        if diagnostic is not None:
            require(diagnostic in result.stderr,
                    f'{name}: wrong native rejection boundary: {result.stderr!r}')
        observations.append({'case': name, 'native': 'accept' if native else 'reject',
                             'admission': 'accept' if admitted else 'reject',
                             'source_sha256': hashlib.sha256(source.encode()).hexdigest()})
        if native:
            Program.read(result.stdout)
            retained[name] = result.stdout
            checks.append(check(name, result.stdout, admitted, 'actual Core.check'))

    def append(program, tag, fields=(), refs=()):
        index = len(program.nodes)
        program.nodes.append((tag, fields, refs))
        return index

    original = Program.read(retained['fold-buffer-free-alloc'])
    ty, fold = original.definitions[0]
    _, _, (count, initial, first) = original.nodes[fold]
    _, first_flag, (index_type, second) = original.nodes[first]
    _, second_flag, (proof_type, third) = original.nodes[second]
    _, third_flag, (accumulator_type, rest) = original.nodes[third]
    _, _, (accumulator_var, fresh) = original.nodes[rest]

    def replace_body(program, body):
        third = append(program, 45, third_flag, (accumulator_type, body))
        second = append(program, 45, second_flag, (proof_type, third))
        first = append(program, 45, first_flag, (index_type, second))
        fold = append(program, 15, refs=(count, initial, first))
        program.definitions[0] = (ty, fold)

    leaked = copy.deepcopy(original)
    replace_body(leaked, fresh)
    checks.append(check('synthetic-accumulator-leak', leaked.encode(), False, 'synthetic'))
    doubled = copy.deepcopy(original)
    twice = append(doubled, 31, refs=(accumulator_var, rest))
    replace_body(doubled, twice)
    checks.append(check('synthetic-accumulator-duplicate', doubled.encode(), False, 'synthetic'))

    wrong_bound = copy.deepcopy(original)
    # Mutate the declared proof bound without changing the fold's actual count.
    _, _, (index_var, _) = wrong_bound.nodes[proof_type]
    one = append(wrong_bound, 47, (1,))
    narrowed = append(wrong_bound, 7, refs=(index_var, one))
    second = append(wrong_bound, 45, second_flag, (narrowed, third))
    first = append(wrong_bound, 45, first_flag, (index_type, second))
    selected = append(wrong_bound, 15, refs=(count, initial, first))
    wrong_bound.definitions[0] = (ty, selected)
    checks.append(check('synthetic-changing-original-bound', wrong_bound.encode(), False, 'synthetic'))

    effectful = copy.deepcopy(original)
    # A memory effect that produces the callback is outside its three lambdas.
    produced = append(effectful, 31, refs=(initial, original.nodes[fold][2][2]))
    selected = append(effectful, 15, refs=(count, initial, produced))
    effectful.definitions[0] = (ty, selected)
    checks.append(check('synthetic-effectful-function-expression', effectful.encode(), False, 'synthetic'))

    cyclic = copy.deepcopy(original)
    cyclic.nodes.append((17, (), (len(cyclic.nodes), len(cyclic.nodes))))
    checks.append(check('synthetic-unused-cycle', cyclic.encode(), False, 'synthetic'))
    checks.append(check('synthetic-trailing-byte', retained['fold-buffer-store'] + b'\n', False, 'synthetic'))
    checks.append(check('synthetic-empty', b'', False, 'synthetic'))
    (output / 'manifest.json').write_text(json.dumps({
        'claim': 'regression evidence; native heap execution and source refinement remain separate',
        'unknown_call_policy': 'actual context-indexed signature replay derives runtime erasures and protects owner-consuming partial calls',
        'core_sha256': hashlib.sha256((ROOT / 'compiler/core.jh').read_bytes()).hexdigest(),
        'exporter_sha256': hashlib.sha256((ROOT / 'compiler/core_native_snapshot.jh').read_bytes()).hexdigest(),
        'cases': observations, 'checks': checks}, indent=2) + '\n')
    print(f'native owned iteration correspondence: {len(observations)} source fixtures and '
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
        with tempfile.TemporaryDirectory(prefix='native-owned-loop-correspondence-') as directory:
            run(shlex.split(args.compiler), shlex.split(args.checker), Path(directory),
                args.proofs.resolve(), args.exporter)

if __name__ == '__main__':
    main()
