#!/usr/bin/env python3
"""Check producer control flow under optimization; fake processes are not semantic oracles.

Real-Core/Lean suites separately exercise authentic accepted and rejected artifacts.
This matrix isolates every subprocess boundary, including intermediate prefixes.
"""
from contextlib import ExitStack, redirect_stderr, redirect_stdout
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from unittest.mock import patch

import core_artifact_replay as artifact
import core_certificate_process as process
import core_checked_normalization as normal
import core_head_normalization as head
import core_typed_beta_replay as beta
import core_type_index_normalization as index
import core_typing_certificates as typing
from core_typing_producer import Unsupported, encode_numbers, graph_tokens, produce


def check(condition, message):
    if not condition:
        raise RuntimeError(message)


def snapshot(graph, term, ty):
    return encode_numbers([3, term, ty, *graph_tokens(graph)])


GRAPH = [(3,), (0, 0), (9, 0, 0, 1), (1, 7), (10, 2, 3)]
HEAD_BEFORE, HEAD_AFTER = snapshot(GRAPH, 4, 0), snapshot(GRAPH, 3, 0)
TYPE_GRAPH = [*GRAPH, (6, 4, 3), (13, 3)]
TYPE_BEFORE = snapshot(TYPE_GRAPH, 6, 5)
TYPE_AFTER = snapshot([*TYPE_GRAPH, (6, 3, 3)], 6, 7)
STAGES = {
    'artifact': ['input', 'driver', 'output'],
    'beta': ['input', 'driver', 'output'],
    'head': ['input', 'driver', 'head-prefix', 'head-final'],
    'index': ['input', 'head-final', 'type-prefix', 'driver', 'type-step', 'type-final'],
}


def case(kind, failure, error=None, cli=False):
    stages = STAGES[kind]
    before, after = (TYPE_BEFORE, TYPE_AFTER) if kind == 'index' else (HEAD_BEFORE, HEAD_AFTER)
    calls, seen = [], []
    def command(argv, payload=None, **kwargs):
        argv = list(map(str, argv))
        if Path(argv[0]).name == 'driver':
            stage = 'driver'
            check(payload == before, f'{kind}: changed retained input')
        elif '--snapshot' in argv:
            stage = 'input'
        elif 'head-checker' in argv or 'CheckNormalization.lean' in argv:
            stage = 'head-prefix' if '--prefix' in argv else 'head-final'
        elif 'type-checker' in argv:
            stage = ('type-step' if 'driver' in calls else 'type-prefix') if '--prefix' in argv else 'type-final'
        else:
            stage = 'input' if not calls else 'output'
        calls.append(stage)
        if failure == stage and error:
            raise error
        output = after if kind == 'artifact' else after + b'\nrecord'
        return subprocess.CompletedProcess(argv, -9 if stage == failure else 0,
                                           output if stage == 'driver' else b'accepted', b'rejected')
    with ExitStack() as stack:
        for module in (artifact, beta, head, index):
            stack.enter_context(patch.object(module, 'command', command))
        if cli:
            module = head if kind == 'head' else index
            with tempfile.TemporaryDirectory() as folder:
                p, t = Path(folder) / 'snapshot', Path(folder) / 'typing'
                p.write_bytes(before); t.write_bytes(b'typing')
                args = [module.__file__, '--generate', str(p), str(t), '--driver', 'driver',
                        '--checker', 'head-checker' if kind == 'head' else 'type-checker']
                if kind == 'index':
                    args += ['--claim', 'eq', '7', '7']
                stream = io.TextIOWrapper(io.BytesIO(), encoding='utf-8')
                with patch.object(sys, 'argv', args), redirect_stdout(stream), redirect_stderr(io.StringIO()):
                    status = module.main()
                stream.flush(); output = stream.buffer.getvalue()
                check(status == (1 if failure else 0), f'{kind} CLI status: {status}')
                expected = index.TypeNormalizer('', []).bundle(before, before, after, b'typing', [], [b'record']) if kind == 'index' else b'\n'.join([before, after, b'typing', head.chain_bytes([b'record'])])
                check(output == (b'' if failure else expected), f'{kind} CLI publication')
        else:
            if kind == 'artifact':
                producer = artifact.Replay(['artifact-checker'], 'driver')
                run = lambda: producer.checked(before, 'shift', 1)
            elif kind == 'beta':
                producer = beta.Replay(['typing-checker'], ['beta-checker'], 'driver')
                run = lambda: producer.checked(before, b'typing', [], consumer=seen.append)
            elif kind == 'head':
                producer = head.Normalizer('driver', ['head-checker'])
                run = lambda: producer.generate(before, b'typing', consumer=seen.append)
            else:
                producer = index.TypeNormalizer('driver', ['type-checker'])
                run = lambda: producer.generate(before, b'typing', claim=['eq', '7', '7'], consumer=seen.append)
            try:
                run()
            except (Unsupported, OSError, subprocess.TimeoutExpired):
                check(failure is not None, f'{kind} positive control rejected')
            else:
                check(failure is None, f'{kind} accepted failure at {failure}')
            published = producer.validated if kind == 'artifact' else producer.published
            check(published == (0 if failure else 1), f'{kind} publication counter')
            if kind != 'artifact':
                check(len(seen) == (0 if failure else 1), f'{kind} consumer called on failure')
    expected_calls = stages[:stages.index(failure)+1] if failure else stages
    check(calls == expected_calls, f'{kind} executed past {failure}: {calls} != {expected_calls}')


def child():
    # All subprocess callers share the same non-asserting status policy.
    for module in (typing, beta, head, index, normal):
        check(module.success is process.success, f'{module.__name__} bypasses common guard')
    check(artifact.require is process.success, 'artifact guard diverged')
    for kind, stages in STAGES.items():
        case(kind, None)
        for stage in stages:
            case(kind, stage)
            case(kind, stage, OSError('unavailable executable'))
            case(kind, stage, subprocess.TimeoutExpired('checker', 180))
        if kind in ('head', 'index'):
            case(kind, None, cli=True)
            for stage in stages:
                case(kind, stage, cli=True)
    # The host-side exact graph/root association is also an executable gate.
    original = snapshot([(3,), (1, 7), (3,), (18,)], 1, 0)
    typing.association(original, produce(original))
    for alternate in (snapshot([(3,), (1, 7), (3,), (18,)], 1, 2),
                      snapshot([(3,), (1, 7), (3,), (19, 0)], 1, 0)):
        try:
            typing.association(original, produce(alternate))
        except Unsupported:
            pass
        else:
            raise RuntimeError('substituted exact snapshot association accepted')


def main():
    if '--child' in sys.argv:
        child()
        return
    for flags, optimize in (([], '0'), (['-O'], '0'), ([], '1'), ([], '2')):
        result = subprocess.run([sys.executable, *flags, __file__, '--child'],
                                env=dict(os.environ, PYTHONOPTIMIZE=optimize), capture_output=True, timeout=60)
        check(result.returncode == 0, result.stderr.decode(errors='replace'))
    print('certificate producer gates: 4 optimization modes; artifact/beta/head/type subprocess failures, '
          'timeouts and launch errors; prefix reuse and CLI publication blocked; exact association checked')


if __name__ == '__main__':
    main()
