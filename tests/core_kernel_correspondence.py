#!/usr/bin/env python3
"""Native/raw-checker regression correspondence, not a translation theorem.

Builds the existing snapshot exporter against this checkout's compiler/core.jh.
Every accepted case feeds its exact retained native snapshot to the Lean raw
checker. No derivation certificate or Python inference implementation is used.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shlex
import shutil
import tempfile

from core_certificate_process import ROOT, command, success
from core_typing_producer import Snapshot, encode_numbers, graph_tokens, require

# Expected outcomes differ deliberately at the documented subset boundary.
CASES = {
    'literal': ('(def value U64 7)', True, True),
    'unsigned-max': ('(def value U64 18446744073709551615)', True, True),
    'signed-min': ('(def value I64 (int -9223372036854775808))', True, True),
    'erased-index-gap': ('(def value (pi0 n U64 (Eq n n)) (lam0 n U64 (refl n)))', True, False),
    'signed': ('(def value I64 (int -7))', True, True),
    'dependent': ('(def value (Eq 7 7) (app (lam n U64 (refl n)) 7))', True, True),
    'nested-capture': (
        '(def value (pi x U64 (pi y U64 (Eq x x))) '
        '(lam x U64 (app (lam n U64 (lam y U64 (refl n))) x)))', True, True),
    'addition': ('(def value U64 (uadd 1 2))', True, True),
    'wrong-argument': ('(def value U64 (app (lam x U64 x) (int -7)))', False, False),
    'false-evidence': ('(def value (Eq 0 1) (refl 0))', False, False),
    'arithmetic-conversion': ('(def value (Eq (uadd 0 1) 1) (refl 1))', True, True),
    'array': ('(def value (Array 1) (array (int -7)))', True, True),
    'empty-array': ('(def value (Array 0) (array))', True, True),
    'computed-array-length': ('(def value (Array (uadd 1 1)) (array (int -7) (int 9)))', True, True),
    'beta-conversion': ('(def value (Eq (app (lam n U64 n) 7) 7) (refl 7))', True, True),
    'converted-argument': (
        '(def value U64 (app (lam0 p (Eq (uadd 0 1) 1) 7) (refl 1)))', True, True),
    'less-evidence': ('(def value (Lt 0 2) (decide-lt 0 2))', True, True),
    'zero-evidence': ('(def value (Lt 0 (uadd 7 1)) (zero-le 7))', True, True),
    'subtract': ('(def value U64 (usub 5 2 (decide-lt 2 6)))', True, True),
    'array-read': ('(def value I64 (index (array (int -7) (int 9)) 1 (decide-lt 1 2)))', True, True),
    'computed-index': (
        '(def value I64 (index (array (int -7) (int 9)) (uadd 0 1) (decide-lt 1 2)))', True, True),
    'dependent-array': (
        '(def value (Array 2) '
        '(app (app (lam n U64 (lam xs (Array n) xs)) (uadd 1 1)) '
        '(array (int -7) (int 9))))', True, True),
    'dependent-reader': (
        '(def value I64 '
        '(app (app (app (lam n U64 (lam xs (Array n) '
        '(lam0 p (Lt 0 n) (index xs 0 p)))) 2) '
        '(array (int -7) (int 9))) (decide-lt 0 2)))', True, True),
    'wrong-index-proof': (
        '(def value I64 (index (array (int -7) (int 9)) 2 (decide-lt 1 2)))', False, False),
    'wrong-array-length': (
        '(def value (Array 1) (array (int -7) (int 9)))', False, False),
    'subtract-underflow': ('(def value U64 (usub 1 2 (decide-lt 0 1)))', False, False),
}


def run(compiler, checker, output):
    output.mkdir(parents=True, exist_ok=True)
    exporter = output / 'core-typing-snapshots'
    success(command([*compiler, 'build', '-O2', '-I', 'compiler',
                     'tests/core_typing_snapshots.jh', '-o', exporter]))
    observations = []
    additional = []
    retained = {}

    def check_payload(name, payload, accepted, *, fuel='64', diagnostic=None):
        (output / f'{name}.snapshot').write_bytes(payload)
        result = command([*checker, fuel], payload, cwd=ROOT / 'proofs')
        require(result.returncode == (0 if accepted else 1),
                f'{name}: unexpected checker outcome: {result.stderr!r}')
        if diagnostic is not None:
            require(diagnostic in result.stderr,
                    f'{name}: rejection did not reach expected boundary: {result.stderr!r}')
        additional.append({'case': name, 'fuel': int(fuel),
                           'raw': 'accept' if accepted else 'reject',
                           'snapshot_sha256': hashlib.sha256(payload).hexdigest()})

    for name, (source, native_ok, raw_ok) in CASES.items():
        (output / f'{name}.core').write_text(source + '\n')
        result = command([exporter, 'require'], source.encode())
        require((result.returncode == 0) == native_ok, f'{name}: native outcome changed: {result.stderr!r}')
        require(result.returncode in (0, 1), f'{name}: native process crashed')
        if not native_ok:
            require(b'type mismatch' in result.stderr, f'{name}: unexpected rejection: {result.stderr!r}')
            observations.append({'case': name, 'native': 'reject', 'raw': 'not run'})
            continue
        payload = result.stdout
        retained[name] = payload
        Snapshot.read(payload)  # Existing canonical bounded decoder, no typing search.
        (output / f'{name}.snapshot').write_bytes(payload)
        checked = command([*checker, '64'], payload, cwd=ROOT / 'proofs')
        require(checked.returncode == (0 if raw_ok else 1),
                f'{name}: raw outcome changed: {checked.stderr!r}')
        if not raw_ok:
            require(b'raw inference differs or rejects' in checked.stderr,
                    f'{name}: rejection did not reach raw checker: {checked.stderr!r}')
        observations.append({'case': name, 'native': 'accept',
                             'raw': 'accept' if raw_ok else 'reject',
                             'snapshot_sha256': hashlib.sha256(payload).hexdigest()})

    # Test raw inference against the actual inferred result, not only the declared
    # type accepted by native conversion. Each call retains its own complete arena.
    for name in ('dependent', 'nested-capture', 'dependent-array', 'dependent-reader'):
        source = CASES[name][0]
        payload = success(command([exporter, 'infer'], source.encode()))
        Snapshot.read(payload)
        check_payload(f'{name}.inferred', payload, True)

    for fuel in ('0', '1'):
        check_payload(f'fuel-{fuel}', retained['dependent'], False, fuel=fuel,
                      diagnostic=b'raw inference differs or rejects')
    # Corrupt the selected type while preserving canonical bytes and valid graph.
    original = Snapshot.read(retained['dependent'])
    wrong_type = next(i for i, n in enumerate(original.graph) if n == (3,))
    mutation = encode_numbers([3, original.term, wrong_type, *graph_tokens(original.graph)])
    Snapshot.read(mutation)
    check_payload('wrong-type-root', mutation, False,
                  diagnostic=b'raw inference differs or rejects')

    # Preserve the exact native evidence term and all original graph nodes, but
    # select an appended, well-formed false proposition. The bounded canonical
    # parser accepts these graphs; only actual type checking rejects them.
    eq_graph = [*original.graph, (1, 7), (1, 8)]
    eq_type = len(eq_graph)
    eq_graph.append((7, eq_type - 2, eq_type - 1))
    false_eq = encode_numbers([3, original.term, eq_type, *graph_tokens(eq_graph)])
    Snapshot.read(false_eq)
    check_payload('false-equality-mutation', false_eq, False,
                  diagnostic=b'raw inference differs or rejects')

    bound = Snapshot.read(retained['less-evidence'])
    lt_graph = [*bound.graph, (1, 0)]
    lt_type = len(lt_graph)
    lt_graph.append((6, lt_type - 1, lt_type - 1))
    false_lt = encode_numbers([3, bound.term, lt_type, *graph_tokens(lt_graph)])
    Snapshot.read(false_lt)
    check_payload('false-bound-mutation', false_lt, False,
                  diagnostic=b'raw inference differs or rejects')

    for name, term_root, type_root in (
            ('invalid-term-root', len(original.graph), original.type),
            ('invalid-type-root', original.term, len(original.graph))):
        payload = encode_numbers([3, term_root, type_root, *graph_tokens(original.graph)])
        check_payload(name, payload, False, diagnostic=b'raw inference differs or rejects')

    # Neither selected root refers to this new node. Whole-graph validation must
    # nevertheless reject its self edge instead of considering only the roots.
    bad_graph = [*original.graph, (5, len(original.graph))]
    payload = encode_numbers([3, original.term, original.type, *graph_tokens(bad_graph)])
    check_payload('unreachable-self-edge', payload, False,
                  diagnostic=b'raw inference differs or rejects')

    check_payload('trailing-newline', retained['literal'] + b'\n', False)
    check_payload('empty-snapshot', b'', False)
    # Nix source-only builds have neither .git metadata nor necessarily git.
    revision = None
    if (ROOT / ".git").exists() and shutil.which("git") is not None:
        result = command(["git", "rev-parse", "HEAD"], cwd=ROOT)
        if result.returncode == 0:
            revision = result.stdout.decode().strip()
    manifest = {
        'claim': 'regression evidence only; native parser/exporter/build/IO remain trusted',
        'core_sha256': hashlib.sha256((ROOT / 'compiler/core.jh').read_bytes()).hexdigest(),
        'exporter_sha256': hashlib.sha256((ROOT / 'compiler/core_snapshot.jh').read_bytes()).hexdigest(),
        'commit': revision,
        'cases': observations,
        'additional_checks': additional,
    }
    (output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(f'kernel correspondence: {len(CASES)} native fixtures and '
          f'{len(additional)} additional checks passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--checker', default='lake env lean -DwarningAsError=true --run CheckKernelInference.lean')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        run(shlex.split(args.compiler), shlex.split(args.checker), args.output.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='kernel-correspondence-') as output:
            run(shlex.split(args.compiler), shlex.split(args.checker), Path(output))


if __name__ == '__main__':
    main()
