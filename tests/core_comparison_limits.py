"""Structural comparison exhaustion must stop both checking and object emission."""
import json


def comparison_fixture(width):
    def balanced(xs):
        if len(xs) == 1:
            return xs[0]
        middle = len(xs) // 2
        return f'(uadd {balanced(xs[:middle])} {balanced(xs[middle:])})'
    atoms = []
    for i in reversed(range(width)):
        atom = str(i)
        for _ in range(32):
            atom = f'(app f {atom})'
        atoms.append(atom)
    term = balanced(atoms)
    return (f'(def proof (pi f (pi x U64 U64) (Eq {term} {term})) '
            f'(lam f (pi x U64 U64) (refl {term})))\n'
            '(export anchor I64 (int 0))\n')


def validate_comparison_limits(compiler, root, temporary, environment, run):
    control = temporary / 'comparison-control.jhc'
    control.write_text(comparison_fixture(64))
    oversized = temporary / 'comparison-budget.jhc'
    oversized.write_text(comparison_fixture(80))
    flags = ('--error-format=json',)
    env = {**environment, 'JIHOO_NO_ELAB': '1'}

    def command(action, path, *args, success=True):
        return run([compiler, 'core', action, str(path), *flags, *args], success=success, env=env)

    command('check', control)
    for target, machine in (('x86_64', 62), ('aarch64', 183)):
        for level in ('-O0', '-O2'):
            obj = temporary / f'comparison-control-{target}{level}.o'
            command('emit-obj', control, '--target', target, level, '-o', str(obj))
            data = obj.read_bytes()
            assert data[:4] == b'\x7fELF' and int.from_bytes(data[18:20], 'little') == machine
    for action in ('check', 'emit-obj'):
        for level in ('-O0', '-O2'):
            obj = temporary / f'comparison-rejected-{action}{level}.o'
            extra = ('-o', str(obj)) if action == 'emit-obj' else ()
            result = command(action, oversized, level, *extra, success=False)
            errors = [d for d in json.loads(result.stderr)['diagnostics'] if d['severity'] == 'error']
            assert result.returncode == 1 and len(errors) == 1, result.stderr
            assert errors[0]['message'] == 'core: checking step limit reached', result.stderr
            assert not obj.exists(), 'resource exhaustion must not publish an object'
    print('core comparison limits: both-target positive controls, exact budget diagnostics and no object after exhaustion passed')
