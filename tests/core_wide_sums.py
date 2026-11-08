"""Ghost sums beyond U64 preserve conversion without weakening runtime traps."""
import json

MAX = (1 << 64) - 1
PREFIX = '#![dependent_core]\nimport dependent.range\n'
PROGRAM = PREFIX + f'''
fn commutes(n: u64) -> Eq(n + {MAX} + 1, 1 + {MAX} + n) {{ refl(n + {MAX} + 1) }}
fn grouped(n: u64) -> Eq(({MAX} + n) + (2 + {MAX}), (n + 2) + ({MAX} + {MAX})) {{ refl(({MAX} + n) + (2 + {MAX})) }}
fn closed(i: u64, p: erased(Lt(i, {MAX}))) -> Lt(i, {MAX}) {{
    range.offset_lt({MAX}, 0, {MAX}, i, lt_add(0, 1, {MAX}, decide_lt(0, 1)), p)
}}
fn cancelled() -> Eq(sub({MAX} + 1, {MAX} + 1, lt_add(0, 1, {MAX} + 1, decide_lt(0, 1))), 0) {{ refl(0) }}
export fn unchanged(n: u64) -> u64 {{ let p = commutes(n); let q = grouped(n); let r = cancelled(); n }}
fn main() -> i64 {{ let p = closed(0, decide_lt(0, {MAX})); let q = commutes({MAX}); 17 }}
'''
INVALID = {
    'wrap': f'fn bad() -> Eq({MAX} + 1, 0) {{ refl({MAX} + 1) }}',
    'adjacent': f'fn bad() -> Eq({MAX} + 1, {MAX} + 2) {{ refl({MAX} + 1) }}',
    'false-order': f'fn bad(i: u64, p: erased(Lt(i, {MAX}))) -> Lt(i, 0) {{ range.offset_lt({MAX}, 0, {MAX}, i, lt_add(0, 1, {MAX}, decide_lt(0, 1)), p) }}',
    'invalid-cancel-proof': f'fn bad() -> Eq(sub({MAX} + 1, {MAX} + 1, decide_lt(0, 1)), 0) {{ refl(0) }}',
    'hidden-proof': f'fn bad() -> Eq(sub({MAX} + 1, {MAX} + 1, decide_lt(0, 1)) + 1, 1) {{ refl(1) }}',
}


def validate_wide_sums(compiler, root, temporary, environment, run):
    def command(action, path, *args, success=True, env=environment):
        return run([compiler, action, str(path), *args], success=success, env=env)

    source = temporary / 'wide-sums.jh'
    source.write_text(PROGRAM)
    command('check', source)
    for level in ('-O0', '-O2'):
        assert command('run', source, level, success=False).returncode == 17
    runtime = temporary / 'wide-runtime.jh'
    runtime.write_text(PROGRAM.split('fn main()')[0])
    reference = temporary / 'wide-reference.jh'
    reference.write_text('#![dependent_core]\nexport fn unchanged(n: u64) -> u64 { n }')
    assert command('emit-mir', runtime, '--lib').stdout == command('emit-mir', reference, '--lib').stdout
    formatted = temporary / 'wide-formatted.jh'
    formatted.write_text(command('fmt', source).stdout)
    assert command('fmt', formatted).stdout == formatted.read_text()
    assert command('emit-mir', formatted).stdout == command('emit-mir', source).stdout
    for target, machine in (('x86_64', 62), ('aarch64', 183)):
        for level in ('-O0', '-O2'):
            obj = temporary / f'wide-{target}{level}.o'
            command('emit-obj', runtime, '--lib', '--target', target, level, '-o', str(obj))
            data = obj.read_bytes()
            assert data.startswith(b'\x7fELF') and int.from_bytes(data[18:20], 'little') == machine
    for name, expression in {
        'addition': f'{MAX} + 1',
        'reordered': f'1 + {MAX}',
        'cancelled': f'sub({MAX} + 1, {MAX} + 1, lt_add(0, 1, {MAX} + 1, decide_lt(0, 1)))',
    }.items():
        trap = temporary / f'wide-trap-{name}.jh'
        trap.write_text(PREFIX + f'fn main() -> i64 {{ let unused: u64 = {expression}; 0 }}')
        for level in ('-O0', '-O2'):
            assert command('run', trap, level, success=False).returncode == 132

    # Every rejection has a runtime export and a successful harness control.
    # Disabling optional checks must not bypass the mandatory core checker.
    flags = ('--lib', '--release', '--no-verify', '--error-format=json')
    unchecked = {**environment, 'JIHOO_NO_ELAB': '1'}
    control = temporary / 'wide-control.jh'
    control.write_text(PREFIX + f'fn good() -> Eq({MAX} + 1, 1 + {MAX}) {{ refl({MAX} + 1) }}\n'
                       'export fn positive_anchor() -> i64 { 0 }')
    obj = temporary / 'wide-control.o'
    command('emit-obj', control, *flags, '-o', str(obj), env=unchecked)
    assert obj.read_bytes().startswith(b'\x7fELF')
    for name, body in INVALID.items():
        bad = temporary / f'wide-{name}.jh'
        bad.write_text(PREFIX + body + '\nexport fn positive_anchor() -> i64 { 0 }')
        obj = temporary / f'wide-{name}.o'
        for action, opts in (('check', ()), ('emit-obj', ('-o', str(obj)))):
            result = command(action, bad, *flags, *opts, success=False, env=unchecked)
            errors = [d for d in json.loads(result.stderr)['diagnostics'] if d['severity'] == 'error']
            assert result.returncode == 1 and len(errors) == 1, (name, result.stderr)
            assert errors[0]['message'] == 'core: type mismatch', (name, result.stderr)
        assert not obj.exists()
    print(f'wide ghost sums: range endpoint, commutativity/association, exact erasure, both targets, '
          f'O0/O2 traps and {len(INVALID)} exact false-proof rejections passed')
