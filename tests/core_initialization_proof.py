#!/usr/bin/env python3
"""Kernel-check initialization invariants exported from actual Core lowering.

The native solver and this observer share the production read/write projection.
Projection fidelity and compiler/runtime refinement remain trusted, not proved.
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
from core_typing_producer import require


def decode(payload):
    require(len(payload) <= 8_000_000, 'initialization export too large')
    functions = []
    seen = set()
    current = None
    cells = 0

    def number(text):
        require(bool(re.fullmatch(r'0|[1-9][0-9]{0,5}', text)), 'invalid natural number')
        value = int(text)
        require(value <= 65535, 'fixture ID limit exceeded')
        return value

    def numbers(text):
        nonlocal cells
        result = [] if text == '' else [number(x) for x in text.split(',')]
        cells += len(result)
        require(cells <= 500_000, 'fixture work limit exceeded')
        return result

    for line in payload.decode('ascii').rstrip('\n').splitlines():
        fields = line.split('\t')
        kind = fields[0]
        if kind == 'function':
            require(len(fields) == 4 and current is None, 'invalid function boundary')
            ident = number(fields[1])
            require(ident not in seen and len(functions) < 128, 'duplicate/excess functions')
            seen.add(ident)
            require(fields[3] in ('0', '1'), 'invalid return representation')
            current = {'id': ident, 'parameters': number(fields[2]),
                       'unit_return': fields[3] == '1', 'blocks': [], 'facts': []}
        elif kind == 'initial':
            require(current is not None and len(fields) == 2 and 'initial' not in current,
                    'invalid initial facts')
            current['initial'] = numbers(fields[1])
            expected = ([0] if current['unit_return'] else []) + list(range(1, current['parameters'] + 1))
            require(current['initial'] == expected, 'initial facts disagree with authentic frame')
        elif kind == 'facts':
            require(current is not None and 'initial' in current and len(fields) == 3,
                    'invalid block facts')
            blocks = current['blocks']
            require(number(fields[1]) == len(blocks) and len(blocks) < 4096 and
                    (not blocks or 'successors' in blocks[-1]), 'nonsequential block')
            facts = None if fields[2] == '-' else numbers(fields[2])
            require(facts is None or facts == sorted(set(facts)), 'noncanonical facts')
            current['facts'].append(facts)
            blocks.append({'actions': []})
        elif kind in ('action', 'successors'):
            require(current is not None and current['blocks'], 'missing block')
            blocks = current['blocks']
            require(len(fields) == (4 if kind == 'action' else 3) and
                    number(fields[1]) == len(blocks) - 1 and
                    'successors' not in blocks[-1], 'invalid block contents')
            if kind == 'action':
                require(len(blocks[-1]['actions']) < 65536, 'too many actions')
                blocks[-1]['actions'].append((numbers(fields[2]), numbers(fields[3])))
            else:
                blocks[-1]['successors'] = numbers(fields[2])
        elif kind == 'end':
            require(len(fields) == 1 and current is not None and current['blocks'] and
                    'successors' in current['blocks'][-1], 'incomplete function')
            require(all(0 <= target < len(current['blocks']) for b in current['blocks']
                        for target in b['successors']), 'invalid successor')
            functions.append(current)
            current = None
        else:
            require(False, 'unknown export record')
    require(current is None and functions, 'incomplete or empty export')
    return functions


def nums(values):
    return '[' + ','.join(map(str, values)) + ']'


def lean_definition(name, function, accepted):
    blocks = []
    for i, block in enumerate(function['blocks']):
        actions = ','.join('⟨' + nums(r) + ',' + nums(w) + '⟩'
                           for r, w in block['actions'])
        blocks.append(f'({i}, ⟨[{actions}], {nums(block["successors"])}⟩)')
    facts = ','.join('none' if f is None else 'some ' + nums(f) for f in function['facts'])
    source = (f'def {name}_g : Graph := [' + ','.join(blocks) + ']\n' +
              f'def {name}_initial : Facts := {nums(function["initial"])}\n' +
              f'def {name}_cert : Certificate := fun n => '
              f'([{facts}] : List (Option Facts))[n]?.join\n')
    if accepted:
        source += (f'theorem {name} (pc : Nat) (state : Facts) (b : Block) '
                   f'(reach : Reach {name}_g {name}_initial pc state) '
                   f'(member : (pc, b) ∈ {name}_g) : Safe b.actions state :=\n'
                   f'  accepted_reads_safe (cert := {name}_cert) (by decide) reach member\n')
    else:
        source += (f'theorem {name} : check {name}_g {name}_initial {name}_cert = false '
                   ':= by decide\n')
    source += f'#print axioms {name}\n'
    if accepted:
        result_arg = '(unitValue : α) ' if function['unit_return'] else ''
        result = '(some unitValue)' if function['unit_return'] else 'none'
        source += (
            f'theorem {name}_frame {{α : Type}} (arguments : List α) {result_arg}'
            f'(arity : arguments.length = {function["parameters"]}) '
            '(operation : Store.Operation α) (pc : Nat) (memory : Store.Memory α) (b : Block) '
            f'(reach : Store.ValueReach {name}_g (Store.enter {result} arguments) pc memory) '
            f'(member : (pc, b) ∈ {name}_g) : '
            'Store.execute operation b.actions memory ≠ .uninitialized := by\n'
            f'  have entry : Store.entryFacts {result} arguments = {name}_initial := by\n'
            '    simp only [Store.entryFacts, arity]\n'
            '    rfl\n'
            f'  apply Store.accepted_frame_no_uninitialized (cert := {name}_cert) _ reach member\n'
            '  rw [entry]\n'
            '  decide\n'
            f'#print axioms {name}_frame\n')
    return source


def test(compiler, probe, folder):
    if probe is None:
        probe = folder / 'initialization-probe'
        success(command([*compiler, 'build', '-O0', '-I', 'compiler',
                         'tests/core_call_entry_probe.jh', '-o', probe], cwd=ROOT))
    exports = []
    payloads = []
    for ghost in (False, True):
        path = folder / f'initialization-{ghost}.jh'
        path.write_text(program(ghost))
        for target in ('x86_64', 'aarch64'):
            payload = success(command([probe, path, target, 'init-certificate']))
            payloads.append(payload)
            exports.append(decode(payload))
    require(all(export == exports[0] for export in exports),
            'target or ghosts changed production initialization projection/facts')
    # Keep graph/facts intact while changing only authentic frame descriptors.
    lines = payloads[0].decode('ascii').splitlines()
    first = next(i for i, line in enumerate(lines) if line.startswith('function\t'))
    for field in (2, 3):
        changed = lines.copy()
        descriptor = changed[first].split('\t')
        descriptor[field] = str(int(descriptor[field]) + 1) if field == 2 else str(1 - int(descriptor[field]))
        changed[first] = '\t'.join(descriptor)
        try:
            decode(('\n'.join(changed) + '\n').encode('ascii'))
        except ValueError as error:
            require(str(error) == 'initial facts disagree with authentic frame',
                    'frame mutation failed for the wrong reason')
        else:
            require(False, 'changed frame descriptor was accepted')
    functions = exports[0]
    require(len(functions) >= 8, 'vacuous native graph export')
    source = ('import Jihoo.InitializationStore\nopen Jihoo.Initialization\n'
              'set_option maxRecDepth 100000\nset_option maxHeartbeats 20000000\n')
    for i, function in enumerate(functions):
        source += lean_definition(f'native_cfg_{i}', function, True)
    base = next(f for f in functions if any(target != 0 and f['facts'][target] is not None
                                            for b in f['blocks'] for target in b['successors']))
    tampered = []
    bad = copy.deepcopy(base)
    bad['facts'][0] = None
    tampered.append(bad)
    fresh = 1 + max([*base['initial'], *(x for f in base['facts'] if f is not None for x in f)])
    bad = copy.deepcopy(base)
    bad['facts'][0].append(fresh)
    tampered.append(bad)
    bad = copy.deepcopy(base)
    target = next(t for b in base['blocks'] for t in b['successors']
                  if t != 0 and base['facts'][t] is not None)
    bad['facts'][target] = None
    tampered.append(bad)
    bad = copy.deepcopy(base)
    bad['blocks'][0]['actions'].insert(0, ([fresh], [fresh]))
    tampered.append(bad)
    for i, bad in enumerate(tampered):
        source += lean_definition(f'rejected_cfg_{i}', bad, False)
    success(subprocess.run(['lake', 'build', 'Jihoo.InitializationStore'], cwd=ROOT / 'proofs',
                           capture_output=True, timeout=180))
    path = folder / 'NativeInitialization.lean'
    path.write_text(source)
    result = success(subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', path],
                                    cwd=ROOT / 'proofs', capture_output=True, timeout=300)).decode()
    entries = re.findall(r'depends on axioms: \[([^\]]*)\]', result)
    closed = re.findall(r'does not depend on any axioms', result)
    require(len(entries) + len(closed) == 2 * len(functions) + len(tampered), 'missing proof audit')
    for entry in entries:
        require(set(filter(None, re.split(r'[,\s]+', entry))) <=
                {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected proof axiom')
    count = sum(len(f['blocks']) for f in functions)
    print(f'initialization proof bridge: 4 native exports; {len(functions)} functions, '
          f'{count} blocks; kernel-checked all-path safety, concrete local-read fault exclusion, '
          f'and {len(tampered)} graph / 2 frame tamper rejections')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--probe', type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-initialization-proof-') as folder:
        test(shlex.split(args.compiler), args.probe, Path(folder))


if __name__ == '__main__':
    main()
