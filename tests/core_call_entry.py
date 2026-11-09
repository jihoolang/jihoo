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
          'contiguous typed parameters and call arities passed; 2 negative controls')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--probe', type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-entry-') as folder:
        test(shlex.split(args.compiler), args.probe, Path(folder))


if __name__ == '__main__':
    main()
