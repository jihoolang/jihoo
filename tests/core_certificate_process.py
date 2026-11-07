"""Subprocess boundary for untrusted certificate producers.

Exit status checks are runtime guards, never removable Python assertions.
Semantic authority remains with the invoked Lean validators.
"""
from pathlib import Path
import subprocess

from core_typing_producer import Unsupported

ROOT = Path(__file__).resolve().parents[1]


def command(argv, payload=None, *, cwd=ROOT):
    return subprocess.run(list(map(str, argv)), input=payload, capture_output=True,
                          cwd=cwd, timeout=180)


def success(result):
    if result.returncode != 0:
        raise Unsupported(f'command failed ({result.returncode}): {result.args}: '
                          f'{result.stderr.decode(errors="replace")}')
    return result.stdout
