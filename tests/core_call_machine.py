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


def lower(functions, *, fact_budget=500_000):
    # Charge every materialized snapshot, including repeated references and
    # copies with no new writes. This budget is shared across all functions.
    def spend_facts(count):
        nonlocal fact_budget
        require(count <= fact_budget, 'expanded fact storage limit exceeded')
        fact_budget -= count

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
            incoming = f['facts'][bi]
            if incoming is not None:
                spend_facts(len(incoming))
            state = copy.deepcopy(incoming)
            control = b['control']
            prefix = b['actions'] if control[0] == 'atomic' else b['actions'][:-1]
            for reads, writes in prefix:
                pc = len(code)
                code.append(f'({pc}, .action ⟨{nums(reads)}, {nums(writes)}⟩ {pc + 1})')
                facts.append(state)
                if state is not None:
                    spend_facts(len(writes) + len(state))
                    state = writes + state
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


def resource_controls():
    def fixture(actions, initial=None, ident=0):
        return dict(id=ident, parameters=0, unit_return=False,
                    facts=[[] if initial is None else initial],
                    blocks=[dict(actions=actions, control=('atomic',), successors=[])])

    def rejected(functions, budget=500_000):
        try:
            lower(functions, fact_budget=budget)
        except ValueError as error:
            require(str(error) == 'expanded fact storage limit exceeded',
                    'fact budget rejected for the wrong reason')
        else:
            require(False, 'fact expansion exceeded its cumulative budget')

    # Three repeated writes retain snapshots of sizes 0, 1, 2, 3. Count every
    # retained occurrence even when input objects are shared.
    action = ([], [1])
    tiny = fixture([action] * 3)
    accepted = lower([tiny], fact_budget=6)
    require([len(x) for x in accepted[0]['facts']] == [0, 1, 2, 3],
            'exact-budget positive control changed snapshots')
    rejected([tiny], 5)
    definition(accepted, fact_budget=6)
    try:
        definition(accepted, fact_budget=5)
    except ValueError as error:
        require(str(error) == 'serialized fact storage limit exceeded',
                'serialization budget rejected for the wrong reason')
    else:
        require(False, 'serialization exceeded its cumulative budget')

    class NoSerialize(list):
        def __iter__(self):
            raise AssertionError('budget checked after fact serialization')

    try:
        definition([dict(facts=[NoSerialize([1, 2])])], fact_budget=1)
    except ValueError as error:
        require(str(error) == 'serialized fact storage limit exceeded',
                'serialization preflight rejected for the wrong reason')
    else:
        require(False, 'serialization preflight did not reject')
    rejected([fixture([action] * 2), fixture([action] * 2, ident=1)], 5)
    blocks = fixture([action] * 2)
    blocks['blocks'] *= 2
    blocks['facts'] = [[], []]
    rejected([blocks], 5)
    # Even unchanged snapshots incur copying/retention cost.
    repeated = fixture([([], [])] * 2, initial=[1, 2])
    lower([repeated], fact_budget=6)
    rejected([repeated], 5)
    # This compact graph is far below both input-cell and instruction limits,
    # but would expand to 1,125,750 fact cells without the new cumulative cap.
    rejected([fixture([action] * 1500)])

    class NoCopy(list):
        def __deepcopy__(self, memo):
            raise AssertionError('budget checked after incoming allocation')

    rejected([fixture([action], initial=NoCopy([1, 2]))], 1)

    class Writes(list):
        additions = 0

        def __add__(self, other):
            self.additions += 1
            require(self.additions <= 2, 'budget checked after concatenation')
            return super().__add__(other)

    writes = Writes([1])
    rejected([fixture([([], writes)] * 3)], 5)
    require(writes.additions == 2, 'concatenation guard was not exercised')
    unreachable = fixture([action] * 3)
    unreachable['facts'] = [None]
    require(lower([unreachable], fact_budget=0)[0]['facts'] == [None] * 4,
            'unreachable facts unexpectedly allocated cells')


def definition(functions, *, fact_budget=500_000):
    # Recheck before producing Lean strings, even if a caller bypasses lower().
    for function in functions:
        for facts in function['facts']:
            if facts is not None:
                require(len(facts) <= fact_budget, 'serialized fact storage limit exceeded')
                fact_budget -= len(facts)
    entries = []
    for f in functions:
        facts = '[' + ','.join('none' if x is None else 'some ' + nums(x) for x in f['facts']) + ']'
        entries.append(f'⟨{f["parameters"]}, {str(f["unit_return"]).lower()}, '
                       '[' + ','.join(f['code']) + f'], fun pc => ({facts} : List (Option Facts))[pc]?.join⟩')
    return 'def observed : Program := [' + ','.join(entries) + ']\n'


def test(compiler, probe, folder):
    resource_controls()
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
          'recursive stack safety, 4 metadata rejections and cumulative fact-budget controls')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--probe', type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-calls-') as folder:
        test(shlex.split(args.compiler), args.probe, Path(folder))


if __name__ == '__main__':
    main()
