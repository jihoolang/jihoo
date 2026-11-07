#!/usr/bin/env python3
"""Regression: all producer subprocess gates survive -O and PYTHONOPTIMIZE."""
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile
import core_checked_normalization as normal


def check(condition, message):
    if not condition:
        raise RuntimeError(message)


def child():
    # Plausible stdout on failure must never allow downstream use or publication.
    for failed_stage in ('input', 'driver', 'output', None):
        calls, seen = [], []
        def command(argv, payload=None, **kwargs):
            stage = 'driver' if argv[0] == 'driver' else ('input' if '--input' in argv else 'output')
            calls.append(stage)
            return subprocess.CompletedProcess(argv, 1 if stage == failed_stage else 0,
                                               b'after\nrecord' if stage == 'driver' else b'accepted', b'rejected')
        old = normal.command
        normal.command = command
        producer = normal.CheckedNormalizer('driver', ['checker'])
        try:
            try:
                result = producer.generate(b'before', b'typing', consumer=seen.append)
            except normal.Unsupported:
                check(failed_stage is not None, 'successful control rejected')
            else:
                check(failed_stage is None, f'{failed_stage} failure accepted')
                check(result == (b'after', b'record'), 'control result changed')
            expected = ['input'] if failed_stage == 'input' else ['input', 'driver'] if failed_stage == 'driver' else ['input', 'driver', 'output']
            check(calls == expected, f'downstream execution after {failed_stage}: {calls}')
            check(producer.invoked == (0 if failed_stage == 'input' else 1), 'invocation count')
            check(producer.published == (0 if failed_stage else 1), 'publication count')
            check(seen == ([] if failed_stage else [b'before\nafter\ntyping\nrecord']), 'consumer called after rejection')
        finally:
            normal.command = old
    # Exercise the public CLI as well: exit 1, empty stdout, no driver after input rejection.
    with tempfile.TemporaryDirectory() as folder:
        root = Path(folder)
        before, typing, marker = root / 'before', root / 'typing', root / 'called'
        before.write_bytes(b'before'); typing.write_bytes(b'typing')
        checker, driver = root / 'checker.py', root / 'driver'
        checker.write_text('import os,sys\nstage="input" if "--input" in sys.argv else "output"\nprint("accepted")\nsys.exit(int(os.environ["FAIL_STAGE"] == stage))\n')
        driver.write_text(f'#!{sys.executable}\nimport os,sys\nfrom pathlib import Path\nPath({str(marker)!r}).write_text("called")\nprint("after\\nrecord", end="")\nsys.exit(int(os.environ["FAIL_STAGE"] == "driver"))\n')
        driver.chmod(0o755)
        for stage in ('input', 'driver', 'output', 'none'):
            marker.unlink(missing_ok=True)
            env = dict(os.environ, FAIL_STAGE=stage, PYTHONOPTIMIZE=str(sys.flags.optimize))
            result = subprocess.run([sys.executable, str(Path(normal.__file__)), '--generate', str(before), str(typing),
                                     '--driver', str(driver), '--checker', shlex.join([sys.executable, str(checker)])],
                                    env=env, capture_output=True, timeout=30)
            check(result.returncode == (0 if stage == 'none' else 1), f'CLI status {stage}: {result}')
            check(result.stdout == (b'before\nafter\ntyping\nrecord' if stage == 'none' else b''), f'CLI published {stage}')
            check(marker.exists() == (stage != 'input'), f'CLI driver invoked after {stage}')


def main():
    if '--child' in sys.argv:
        child()
        return
    for flags, optimize in (([], '0'), (['-O'], '0'), ([], '1'), ([], '2')):
        result = subprocess.run([sys.executable, *flags, __file__, '--child'],
                                env=dict(os.environ, PYTHONOPTIMIZE=optimize), capture_output=True, timeout=60)
        check(result.returncode == 0, result.stderr.decode(errors='replace'))
    print('producer gates: normal, -O, PYTHONOPTIMIZE=1/2; input/driver/output failures blocked; positive controls passed')


if __name__ == '__main__':
    main()
