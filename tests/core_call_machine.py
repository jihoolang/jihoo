#!/usr/bin/env python3
"""Kernel-check interprocedural initialization of actual Core observations.

Whole-local/constant call arguments only. Constants are opaque tokens; external
calls and non-call instructions retain the arbitrary-operation boundary.
"""
import argparse
import copy
from pathlib import Path
import re
import shlex
import subprocess
import tempfile
from core_capture_environment import program
from core_certificate_process import ROOT, command, success
from core_initialization_proof import decode, nums
from core_typing_producer import require


def parse(payload):
    require(len(payload) <= 8_000_000, 'call export too large')
    base, controls = [], {}
    function = block = None
    work = 0
    for line in payload.decode('ascii').splitlines():
        fields = line.split('\t')
        if fields[0] == 'function':
            function, block = int(fields[1]), None
        elif fields[0] == 'facts':
            block = int(fields[1])
        if fields[0] != 'control':
            base.append(line)
            continue
        require(function is not None and block is not None and (function, block) not in controls,
                'invalid control association')
        require(len(fields) in (2, 6), 'invalid control record')
        if fields[1] == 'call':
            require(len(fields) == 6, 'invalid call record')
            require(all(re.fullmatch(r'0|[1-9][0-9]{0,4}', v) for v in fields[2:5]),
                    'invalid call ID')
            args = fields[5].split(',') if fields[5] else []
            require(all(re.fullmatch(r'[vc](?:0|[1-9][0-9]{0,4})', a) for a in args),
                    'invalid call argument')
            control = ('call', *map(int, fields[2:5]), args)
            work += len(args) + 1
            require(work <= 500_000, 'call metadata work limit exceeded')
        else:
            require(len(fields) == 2 and fields[1] in ('return', 'atomic'), 'unknown control')
            control = (fields[1],)
        controls[function, block] = control
    functions = decode(('\n'.join(base) + '\n').encode())
    expected = {(f['id'], i) for f in functions for i in range(len(f['blocks']))}
    require(set(controls) == expected, 'missing or extra control metadata')
    for f in functions:
        for i, b in enumerate(f['blocks']):
            b['control'] = controls[f['id'], i]
    return functions


def lower(functions):
    require(max(f['id'] for f in functions) < 128, 'function table limit exceeded')
    result = []
    by_id = {f['id']: f for f in functions}
    total = 0
    for ident in range(max(by_id) + 1):
        if ident not in by_id:
            # Native external IDs are never entered as machine calls. Their
            # call actions remain atomic; placeholders preserve original IDs.
            result.append(dict(parameters=0, unit_return=False, code=['(0, .stop)'], facts=[[]]))
            continue
        f = by_id[ident]
        starts, count = [], 0
        for b in f['blocks']:
            require(b['actions'], 'missing terminal action')
            starts.append(count)
            count += len(b['actions']) + (b['control'][0] == 'atomic')
        total += count
        require(total <= 50000, 'expanded instruction limit exceeded')
        code, facts = [], []
        for bi, b in enumerate(f['blocks']):
            state = copy.deepcopy(f['facts'][bi])
            control = b['control']
            prefix = b['actions'] if control[0] == 'atomic' else b['actions'][:-1]
            for reads, writes in prefix:
                pc = len(code)
                code.append(f'({pc}, .action ⟨{nums(reads)}, {nums(writes)}⟩ {pc + 1})')
                facts.append(state)
                state = None if state is None else writes + state
            pc = len(code)
            facts.append(state)
            if control[0] == 'call':
                _, target, dest, next_block, args = control
                require(target in by_id and len(args) == by_id[target]['parameters'],
                        'call target or arity mismatch')
                reads = [int(a[1:]) for a in args if a.startswith('v')]
                require(b['actions'][-1] == (reads, [dest]) and b['successors'] == [next_block],
                        'call metadata disagrees with native action')
                encoded = '[' + ','.join(('.slot ' + a[1:]) if a.startswith('v') else ('.constant ' + a[1:])
                                         for a in args) + ']'
                code.append(f'({pc}, .call {target} {encoded} {dest} {starts[next_block]})')
            elif control[0] == 'return':
                require(b['actions'][-1] == ([0], []) and not b['successors'],
                        'return metadata disagrees with native action')
                code.append(f'({pc}, .ret)')
            else:
                targets = [starts[t] for t in b['successors']]
                code.append(f'({pc}, .branch [] {nums(targets)})' if targets else f'({pc}, .stop)')
        result.append(dict(parameters=f['parameters'], unit_return=f['unit_return'], code=code, facts=facts))
    return result


def definition(functions):
    entries = []
    for f in functions:
        facts = '[' + ','.join('none' if x is None else 'some ' + nums(x) for x in f['facts']) + ']'
        entries.append(f'⟨{f["parameters"]}, {str(f["unit_return"]).lower()}, '
                       '[' + ','.join(f['code']) + f'], fun pc => ({facts} : List (Option Facts))[pc]?.join⟩')
    return 'def observed : Program := [' + ','.join(entries) + ']\n'


def test(compiler, probe, folder):
    if probe is None:
        probe = folder / 'call-machine-probe'
        success(command([*compiler, 'build', '-O0', '-I', 'compiler',
                         'tests/core_call_entry_probe.jh', '-o', probe], cwd=ROOT))
    exports = []
    for ghost in (False, True):
        path = folder / f'calls-{ghost}.jh'
        path.write_text(program(ghost))
        for target in ('x86_64', 'aarch64'):
            exports.append(parse(success(command([probe, path, target, 'call-certificate']))))
    require(all(x == exports[0] for x in exports), 'call observer changed with ghosts/target')
    observed = exports[0]
    calls = [(f, i) for f in observed for i, b in enumerate(f['blocks']) if b['control'][0] == 'call']
    require(len(calls) >= 8, 'vacuous internal-call observation')
    # Keep valid graph structure while mutating only call handoff metadata.
    for field in (1, 2, 3, 4):
        altered = copy.deepcopy(observed)
        fid, bi = calls[0][0]['id'], calls[0][1]
        block = next(f for f in altered if f['id'] == fid)['blocks'][bi]
        control = list(block['control'])
        if field == 1:
            control[field] = 99999
        elif field in (2, 3):
            control[field] += 1
        else:
            control[field] = control[field] + ['c0']
        block['control'] = tuple(control)
        try:
            lower(altered)
        except ValueError as error:
            require(str(error) in ('call target or arity mismatch', 'call metadata disagrees with native action'),
                    'metadata mutation rejected for wrong reason')
        else:
            require(False, 'changed handoff accepted')
    functions = lower(observed)
    source = ('import Jihoo.InitializationCalls\nopen Jihoo.Initialization Jihoo.Initialization.Calls\n'
              'set_option maxRecDepth 100000\nset_option maxHeartbeats 20000000\n' + definition(functions) +
              'theorem accepted : validate observed = true := by decide\n'
              'theorem safe {α : Type} (unit : α) (constants : Nat → α) '
              '(fid : Nat) (f : Function) (args : List α) (state : State α) '
              '(hf : observed[fid]? = some f) (arity : args.length = f.parameters) '
              '(reach : Reaches observed unit constants (.active fid 0 (f.entry unit args) []) state) : '
              'state ≠ .uninitialized := no_uninitialized (validate_sound accepted) hf arity reach\n'
              '#print axioms accepted\n#print axioms safe\n')
    success(subprocess.run(['lake', 'build', 'Jihoo.InitializationCalls'], cwd=ROOT / 'proofs',
                           capture_output=True, timeout=180))
    path = folder / 'NativeCalls.lean'
    path.write_text(source)
    checked = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', path],
                             cwd=ROOT / 'proofs', capture_output=True, timeout=300)
    require(checked.returncode == 0, f'Lean call check failed: {checked.stdout!r} {checked.stderr!r}')
    output = checked.stdout.decode()
    entries = re.findall(r'depends on axioms: \[([^\]]*)\]', output)
    require(len(entries) + output.count('does not depend on any axioms') == 2, 'missing call proof audit')
    for entry in entries:
        require(set(filter(None, re.split(r'[,\s]+', entry))) <= {'propext', 'Quot.sound', 'Classical.choice'},
                'unexpected call proof axiom')
    print(f'call machine: 4 native exports, {len(observed)} functions, {len(calls)} internal calls; '
          f'{sum(len(f["code"]) for f in functions)} instructions kernel-checked; '
          'recursive stack safety and 4 metadata rejections')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--probe', type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-calls-') as folder:
        test(shlex.split(args.compiler), args.probe, Path(folder))


if __name__ == '__main__':
    main()
