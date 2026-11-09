#!/usr/bin/env python3
"""Inspect fresh MIR parameter allocation through the actual current lowerer."""
import argparse
from pathlib import Path
import shlex
import tempfile
from core_capture_environment import program
from core_certificate_process import ROOT, command, success
from core_typing_producer import require


def test(compiler, probe, out):
    if probe is None:
        probe = out / 'call-entry-probe'
        success(command([*compiler, 'build', '-O0', '-I', 'compiler',
                         'tests/core_call_entry_probe.jh', '-o', probe], cwd=ROOT))
    reports = []
    for ghost in (False, True):
        path = out / f'entry-{ghost}.jh'
        path.write_text(program(ghost))
        for target in ('x86_64', 'aarch64'):
            report = success(command([probe, path, target])).decode().strip().split('\t')
            require(len(report) == 4 and report[0] == 'entry-layout', f'invalid report: {report!r}')
            functions, calls, parameters = map(int, report[1:])
            require(functions >= 8 and calls >= functions and parameters > functions,
                    f'vacuous generated function inspection: {report!r}')
            reports.append((functions, calls, parameters))
    mutations = {
        'init-return': 'read of uninitialized local',
        'init-read': 'read of uninitialized local',
        'init-self': 'read of uninitialized local',
        'init-pointer': 'read of uninitialized local',
        'init-index': 'read of uninitialized local',
        'init-aggregate': 'read of uninitialized local',
        'init-call': 'read of uninitialized local',
        'init-join': 'read of uninitialized local',
        'init-loop': 'read of uninitialized local',
        'init-work-limit': 'initialization work limit reached',
        'init-state-limit': 'initialization state limit reached',
        'local-type': 'invalid runtime type',
        'builtin-type': 'invalid builtin types',
        'cyclic-type': 'invalid runtime type',
        'assignment-type': 'assignment type mismatch',
        'operand-local': 'invalid operand local',
        'dereference': 'dereference of nonpointer',
        'field': 'field of nontuple',
        'index-local': 'invalid array index local',
        'constant-type': 'integer constant type mismatch',
        'constant-range': 'integer constant out of range',
        'binary-type': 'binary operand type mismatch',
        'cast-type': 'invalid numeric cast',
        'offset-type': 'offset of nonpointer',
        'aggregate-count': 'aggregate arity mismatch',
        'aggregate-type': 'aggregate operand type mismatch',
        'goto': 'invalid control-flow target',
        'pending': 'unfinished or unsupported terminator',
        'assert-type': 'invalid assertion type',
        'switch-duplicate': 'duplicate switch case',
        'switch-bool': 'invalid boolean case',
        'switch-target': 'invalid control-flow target',
        'call-type': 'call operand type mismatch',
        'negative-count': 'invalid argument count',
        'count': 'invalid argument count',
        'return-kind': 'invalid return local',
        'return-type': 'invalid return local',
        'parameter-kind': 'invalid parameter local',
        'parameter-type': 'invalid parameter local',
        'late-argument': 'unexpected frame local',
        'pass': 'invalid parameter signature',
        'variadic': 'invalid parameter signature',
        'callee': 'invalid callee',
        'missing-operand': 'call argument count mismatch',
        'extra-operand': 'call argument count mismatch',
        'destination': 'invalid call destination',
        'indirect': 'expected direct call',
        'projection': 'invalid call destination',
        'result-type': 'call result type mismatch',
        'continuation': 'invalid call continuation',
    }
    for mutation, diagnostic in mutations.items():
        rejected = command([probe, path, 'x86_64', mutation])
        require(rejected.returncode != 0 and not rejected.stdout and
                ('core MIR: ' + diagnostic).encode() in rejected.stderr,
                f'{mutation}: wrong rejection: {rejected.stderr!r}')
    controls = ('straight', 'index', 'unreachable', 'call', 'join', 'loop', 'work')
    for control in controls:
        accepted = success(command([probe, path, 'x86_64', 'init-valid-' + control]))
        require(accepted.strip() == b'initialization control accepted',
                f'initialization positive control failed: {control}')
    require(all(report == reports[0] for report in reports),
            f'ghosts or target changed call-entry layout: {reports!r}')
    # A type-invalid input must not produce any successful partial report.
    invalid = out / 'invalid.jh'
    invalid.write_text('#![dependent_core]\nexport fn bad(n: erased(u64)) -> u64 { n }\n')
    rejected = command([probe, invalid, 'x86_64'])
    require(rejected.returncode != 0 and not rejected.stdout and
            b'erased value used at runtime' in rejected.stderr,
            f'wrong invalid-input rejection: {rejected.stderr!r}')
    # A valid but nonrecursive input is rejected by the observation harness,
    # preventing a vacuous all-functions check from passing.
    empty = out / 'nonrecursive.jh'
    empty.write_text('#![dependent_core]\nexport fn good(n: u64) -> u64 { n }\n')
    rejected = command([probe, empty, 'x86_64'])
    require(rejected.returncode != 0 and not rejected.stdout and
            b'no generated recursion observed' in rejected.stderr,
            'nonrecursive control did not reject')
    print(f'call entry: 4 current-lowerer inspections {reports[0]}; '
          f'contiguous typed parameters and call arities passed; {len(mutations)} MIR mutations; 7 initialization controls; 2 negative controls')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--probe', type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-entry-') as folder:
        test(shlex.split(args.compiler), args.probe, Path(folder))


if __name__ == '__main__':
    main()
