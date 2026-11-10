#!/usr/bin/env python3
"""Production dual-check operation, protocol and bounded subprocess regressions."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('verified_core_tool', ROOT / 'scripts/verified_core.py')
v = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def reject(action, label):
    try:
        action()
    except (v.Rejected, OSError):
        return
    raise RuntimeError('accepted ' + label)


def process_tests():
    py = sys.executable
    def run(code, payload=b'', **kwargs):
        return v.bounded_process([py, '-c', code], payload, **kwargs)
    require(run('import sys; sys.stdout.buffer.write(sys.stdin.buffer.read())', b'payload') == b'payload', 'echo')
    require(run('import sys; sys.stdout.write("a"*16)', output_limit=16) == b'a'*16, 'exact bound')
    reject(lambda: run('import sys; sys.stdout.write("a"*17)', output_limit=16), 'stdout budget')
    reject(lambda: run('import sys; sys.stderr.write("a"*65537)'), 'stderr budget')
    reject(lambda: run('import sys; print("valid"); sys.exit(1)'), 'nonzero valid output')
    reject(lambda: run('import time; time.sleep(2)', timeout=.05), 'timeout')
    reject(lambda: v.bounded_process(['/nonexistent/verified-core-tool'], b''), 'missing executable')
    # Descendants retaining output pipes must not evade the deadline.
    reject(lambda: run('import os,time; p=os.fork(); time.sleep(2) if p==0 else None', timeout=.05), 'descendant pipes')
    # Simultaneous large input and both output pipes must not deadlock.
    require(len(run('import sys; x=sys.stdin.buffer.read(); sys.stderr.write("e"*60000); sys.stdout.buffer.write(x)',
                    b'x'*200000)) == 200000, 'pipe deadlock')


def orchestration_tests():
    source = b'original source'
    snapshot = b'canonical snapshot'
    calls = []
    def runner(argv, data, **kwargs):
        calls.append((argv, data))
        return snapshot if len(calls) == 1 else v.PROTOCOL + data + b'\n'
    result = v.verify(source, '/trusted/exporter', runner=runner)
    require(calls[0] == (['/trusted/exporter'], source), 'source identity')
    require(calls[1][1] is snapshot, 'snapshot reread')
    require(result['source_sha256'] == hashlib.sha256(source).hexdigest(), 'source digest')
    require(result['snapshot_sha256'] == hashlib.sha256(snapshot).hexdigest(), 'snapshot digest')
    for reply in (b'accepted', b'', v.PROTOCOL + b'other' + b'\n',
                  v.PROTOCOL + snapshot + b'\nextra', v.PROTOCOL + snapshot):
        counter = [0]
        def wrong(argv, data, **kwargs):
            counter[0] += 1
            return snapshot if counter[0] == 1 else reply
        reject(lambda: v.verify(source, 'exporter', runner=wrong), 'malformed or stale protocol')
    def fail(*args, **kwargs):
        raise v.Rejected('failure')
    reject(lambda: v.verify(source, 'exporter', runner=fail), 'producer failure')
    for failure in (v.Rejected('verifier failed'), FileNotFoundError('verifier missing')):
        stages = []
        def verifier_failure(argv, data, **kwargs):
            stages.append(data)
            if len(stages) == 1:
                return snapshot
            raise failure
        reject(lambda: v.verify(source, 'exporter', runner=verifier_failure), 'verifier failure')
        require(len(stages) == 2, 'failure skipped independent verifier')
    reject(lambda: v.verify(b'x'*(v.SOURCE_LIMIT+1), 'exporter', runner=fail), 'source budget')
    reject(lambda: v.verify(source, 'exporter', runner=lambda *a, **kw: b''), 'empty snapshot')
    # The source pathname can change after it is read without changing what is certified.
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / 'input.core'
        path.write_bytes(source)
        retained = path.read_bytes()
        def change(argv, data, **kwargs):
            if data == source:
                path.write_bytes(b'replacement')
                return snapshot
            return v.PROTOCOL + data + b'\n'
        got = v.verify(retained, 'exporter', runner=change)
        require(got['source_sha256'] == hashlib.sha256(source).hexdigest(), 'changed source misbound')


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--compiler', required=True)
    args = p.parse_args()
    process_tests()
    orchestration_tests()
    with tempfile.TemporaryDirectory(prefix='verified-core-') as tmp:
        exporter = Path(tmp) / 'exporter'
        build = subprocess.run([args.compiler, 'build', '-O0', '-I', 'compiler',
                                'compiler/verified_core_snapshot.jh', '-o', str(exporter)], cwd=ROOT,
                               capture_output=True, timeout=180)
        require(build.returncode == 0, build.stderr.decode(errors='replace'))
        from core_proof_functions import VALID
        accepted = 0
        for name, source in {**VALID, 'literal': '(def literal (Eq 7 7) (refl 7))'}.items():
            result = v.verify(source.encode(), exporter)
            require(result['status'] == 'verified-subset', name)
            accepted += 1
        for name, source in {
            'non-atomic-index': '(def x (Eq 2 2) (app (lam n U64 (refl n)) (uadd 1 1)))',
            'erased-natural': '(def x (pi0 n U64 (Eq n n)) (lam0 n U64 (refl n)))',
            'convertible-request': '(def x (Eq (uadd 1 1) 2) (refl 2))',
            'false-eq': '(def x (Eq 7 8) (refl 7))',
            'multiple': '(def x (Eq 7 7) (refl 7)) (def y (Eq 7 7) (refl 7))',
            'parse': 'not core',
        }.items():
            reject(lambda: v.verify(source.encode(), exporter), name)
        # Exercise public CLI: JSON only after successful independent admission.
        cli = [sys.executable, ROOT / 'scripts/verified_core.py', '--exporter', exporter, '-']
        good = subprocess.run(list(map(str, cli)), input=b'(def x (Eq 7 7) (refl 7))', capture_output=True, cwd=ROOT, timeout=180)
        require(good.returncode == 0 and json.loads(good.stdout)['status'] == 'verified-subset', 'CLI success')
        bad = subprocess.run(list(map(str, cli)), input=b'(def x (Eq 7 8) (refl 7))', capture_output=True, cwd=ROOT, timeout=180)
        require(bad.returncode != 0 and not bad.stdout, 'CLI fail open')
        # Real verifier rejects tampered and malformed retained graphs.
        from core_typing_producer import Snapshot, encode_numbers, graph_tokens
        wire = v.bounded_process([exporter], b'(def x (Eq 7 7) (refl 7))')
        snap = Snapshot.read(wire)
        mutations = [wire + b';', wire[:-1], encode_numbers([3, snap.term, snap.term, *graph_tokens(snap.graph)]),
                     encode_numbers([3, snap.term, snap.type, *graph_tokens(snap.graph + [(5, len(snap.graph))])])]
        for mutation in mutations:
            reject(lambda: v.bounded_process(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', 'VerifyCore.lean'],
                                           mutation, cwd=ROOT/'proofs'), 'graph tamper')
    print(f'verified Core: {accepted} real positives; unsupported/false inputs, protocol, byte identity, budgets and subprocess failures checked')


if __name__ == '__main__':
    main()
