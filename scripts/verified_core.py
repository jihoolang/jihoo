#!/usr/bin/env python3
"""Explicit fail-closed dual checking for the documented mixed-proof Core subset.

The native exporter and Lean toolchain are trusted executables. Neither ordinary
Core acceptance nor this IO adapter is itself a refinement theorem.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import selectors
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
SOURCE_LIMIT = 1024 * 1024
SNAPSHOT_LIMIT = 8 * 1024 * 1024
ERROR_LIMIT = 64 * 1024
PROTOCOL = b"jihoo-verified-core-v1\n"


class Rejected(Exception):
    pass


def bounded_process(argv, payload, *, cwd=ROOT, timeout=180, output_limit=SNAPSHOT_LIMIT):
    """Bound both output pipes while feeding stdin; kill the process group on failure.

    A producer that exits unsuccessfully with valid stdout is still rejected.
    Deadlines also cover descendants keeping pipes open after the leader exits.
    """
    output = bytearray()
    errors = bytearray()
    deadline = time.monotonic() + timeout
    with subprocess.Popen(list(map(str, argv)), stdin=subprocess.PIPE,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          cwd=cwd, start_new_session=True) as proc:
        try:
            with selectors.DefaultSelector() as sel:
                for stream in (proc.stdin, proc.stdout, proc.stderr):
                    os.set_blocking(stream.fileno(), False)
                if payload:
                    sel.register(proc.stdin, selectors.EVENT_WRITE, 'input')
                else:
                    proc.stdin.close()
                sel.register(proc.stdout, selectors.EVENT_READ, 'output')
                sel.register(proc.stderr, selectors.EVENT_READ, 'errors')
                offset = 0
                while sel.get_map():
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        raise Rejected('subprocess deadline exceeded')
                    for key, _ in sel.select(min(remaining, 0.1)):
                        stream = key.fileobj
                        if key.data == 'input':
                            try:
                                offset += os.write(stream.fileno(), payload[offset:offset + 65536])
                            except BrokenPipeError:
                                offset = len(payload)
                            if offset == len(payload):
                                sel.unregister(stream)
                                stream.close()
                        else:
                            target = output if key.data == 'output' else errors
                            limit = output_limit if key.data == 'output' else ERROR_LIMIT
                            chunk = os.read(stream.fileno(), min(65536, limit + 1 - len(target)))
                            if not chunk:
                                sel.unregister(stream)
                                stream.close()
                            else:
                                if len(target) + len(chunk) > limit:
                                    raise Rejected(f'{key.data} limit exceeded')
                                target.extend(chunk)
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    raise Rejected('subprocess deadline exceeded')
                try:
                    status = proc.wait(timeout=remaining)
                except subprocess.TimeoutExpired as exc:
                    raise Rejected('subprocess deadline exceeded') from exc
                if status != 0:
                    raise Rejected(f'subprocess exited {status}: '
                                   + errors.decode('utf-8', errors='replace'))
                return bytes(output)
        finally:
            # No producer/verifier descendants may survive this operation,
            # including after an apparently successful leader exit.
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.wait()


def verify(source, exporter, *, runner=bounded_process):
    if len(source) > SOURCE_LIMIT:
        raise Rejected('source exceeds 1 MiB')
    # Read the source once in main; producer receives the retained value, not a
    # mutable source pathname. The producer always selects the requested type.
    snapshot = runner([exporter], source, output_limit=SNAPSHOT_LIMIT)
    if not snapshot or len(snapshot) > SNAPSHOT_LIMIT:
        raise Rejected('invalid snapshot size')
    response = runner(['lake', 'env', 'lean', '-DwarningAsError=true', '--run',
                       'VerifyCore.lean'], snapshot, cwd=ROOT / 'proofs',
                      output_limit=SNAPSHOT_LIMIT + len(PROTOCOL) + 1)
    if response != PROTOCOL + snapshot + b'\n':
        raise Rejected('verifier response does not exactly bind the retained snapshot')
    # Only now may a success result exist. Hashes are byte association, not a
    # claim that native parsing/export is formally refined or authenticated.
    return {'status': 'verified-subset', 'schema': 1,
            'source_sha256': hashlib.sha256(source).hexdigest(),
            'snapshot_sha256': hashlib.sha256(snapshot).hexdigest(),
            'scope': 'closed-mixed-proof-v1'}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exporter', required=True,
                        help='trusted compiler/verified_core_snapshot.jh binary from this checkout')
    parser.add_argument('source', help='one textual Core declaration, or - for stdin')
    args = parser.parse_args(argv)
    try:
        if args.source == '-':
            source = sys.stdin.buffer.read(SOURCE_LIMIT + 1)
        else:
            with open(args.source, 'rb') as stream:
                source = stream.read(SOURCE_LIMIT + 1)
        result = verify(source, str(Path(args.exporter).resolve()))
        print(json.dumps(result, sort_keys=True))
        return 0
    except (Rejected, OSError, ValueError) as error:
        print(f'verified Core rejected: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
