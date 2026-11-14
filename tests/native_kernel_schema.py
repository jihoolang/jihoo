#!/usr/bin/env python3
"""Check full Lean constructor/binder metadata against the actual native source.

This catches interface drift. It is not a semantic refinement proof for source
execution or a typing oracle. The expected fields come from the source enum;
actual arities and binder increments come from executed Lean definitions.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import shlex
import subprocess

ROOT = Path(__file__).resolve().parents[1]
# Native scalar payload fields rather than graph references. Vector fields are
# graph references; their lengths are represented explicitly in Lean Op.
SCALARS = {
    'Var': {0}, 'Global': {0}, 'Universe': {0}, 'Ind': {0},
    'Con': {0, 1}, 'Elim': {0}, 'Arith': {0}, 'Drop': {0},
    'Back': {0}, 'Give': {0}, 'View': {0, 1}, 'Case': {0},
    'Pi': {0}, 'Lam': {0}, 'Natural': {0}, 'Integer': {0},
}
BINDERS = {'Pi': 1, 'Lam': 1, 'IfLt': 2, 'IfEq': 2}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def comma_fields(text):
    fields, start, depth = [], 0, 0
    for index, char in enumerate(text):
        if char == '(':
            depth += 1
        elif char == ')':
            depth -= 1
        elif char == ',' and depth == 0:
            fields.append(text[start:index].strip())
            start = index + 1
    if text[start:].strip():
        fields.append(text[start:].strip())
    return fields


def source_constructors(source):
    body = source.split('pub enum Term {', 1)[1].split('\n}', 1)[0]
    body = re.sub(r'//[^\n]*', '', body)
    rows = []
    for match in re.finditer(r'^    ([A-Z][A-Za-z0-9]*)(?:\((.*)\))?\s*$', body, re.M):
        rows.append((match[1], comma_fields(match[2] or '')))
    require(len(rows) >= 54, f'truncated native enum: {len(rows)}')
    require(set(SCALARS) <= {name for name, _ in rows}, 'unknown scalar schema entry')
    return rows


def validate(root, emitted):
    source = (root / 'compiler/core.jh').read_text()
    constructors = source_constructors(source)
    actual = {}
    for line in emitted.splitlines():
        fields = line.split('\t')
        require(len(fields) == 5, f'invalid metadata row: {line!r}')
        count, name, tag, arity = int(fields[0]), fields[1], int(fields[2]), int(fields[3])
        binders = [int(value) for value in fields[4].split(',')] if fields[4] else []
        key = count, name
        require(key not in actual, f'duplicate metadata: {key}')
        actual[key] = tag, arity, binders
    require(len(actual) == 3 * len(constructors), 'incomplete or extra Lean constructor metadata')
    for count in (0, 1, 3):
        for tag, (name, fields) in enumerate(constructors):
            arity = sum(count if field == 'Vec(u32)' else 1
                        for index, field in enumerate(fields)
                        if index not in SCALARS.get(name, set()))
            binders = [int(index == BINDERS.get(name)) for index in range(arity)]
            require(actual.get((count, name)) == (tag, arity, binders),
                    f'{name}, count {count}: expected {(tag, arity, binders)}, '
                    f'got {actual.get((count, name))}')
    # Every implicit binder must actually increment cutoff in Core.transform.
    transform = source.split('    fn transform(', 1)[1].split('    fn transform_all(', 1)[0]
    branches = re.split(r'^            (?=[A-Z][A-Za-z0-9]*\()', transform, flags=re.M)
    increments = set()
    for branch in branches[1:]:
        name = branch.split('(', 1)[0]
        calls = re.findall(r'self\.transform\((\w+),\s*cutoff\s*\+\s*1,', branch)
        if calls:
            increments.add(name)
            require(calls == (['b'] if name in ('Pi', 'Lam') else ['yes']),
                    f'unexpected binder transform in {name}: {calls}')
    require(increments == set(BINDERS), f'native binder cases changed: {increments}')
    print(f'native schema: all {len(constructors)} constructors, three vector lengths, '
          f'and {len(increments)} binder cases match')


def validate_wire(native, lean):
    require(native == lean, 'native/Lean node bytes differ')
    require(len(native.splitlines()) == 162, 'incomplete native node serializer coverage')
    print('native wire: 162 constructor/vector cases match the proved canonical encoder')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--metadata', type=Path)
    parser.add_argument('--emitter', default='lake env lean -DwarningAsError=true --run EmitNativeSchema.lean')
    parser.add_argument('--native-writer', type=Path)
    parser.add_argument('--wire-emitter', default='lake env lean -DwarningAsError=true --run EmitNativeWireNodes.lean')
    args = parser.parse_args()
    if args.metadata:
        emitted = args.metadata.read_text()
    else:
        result = subprocess.run(shlex.split(args.emitter), cwd=ROOT / 'proofs',
                                capture_output=True, text=True, timeout=180)
        require(result.returncode == 0, result.stderr)
        emitted = result.stdout
    validate(ROOT, emitted)
    if args.native_writer:
        native = subprocess.run([str(args.native_writer.resolve())], capture_output=True, timeout=180)
        require(native.returncode == 0, native.stderr)
        lean = subprocess.run(shlex.split(args.wire_emitter), cwd=ROOT / 'proofs',
                              capture_output=True, timeout=180)
        require(lean.returncode == 0, lean.stderr)
        validate_wire(native.stdout, lean.stdout)


if __name__ == '__main__':
    main()
