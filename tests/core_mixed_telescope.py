#!/usr/bin/env python3
"""Check mixed natural/proof binders; no object emission or execution.

These are executable-checker regressions, not a refinement proof connecting its
judgment to Indexed.Mixed. Every negative has a nearby accepted control.
"""
import argparse
from pathlib import Path
import subprocess
import tempfile

VALID = {
    'interleaved': '''(def mixed
      (pi n U64 (pi0 p (Eq n n) (pi m U64 (pi0 q (Lt m (uadd n 1)) (Eq n n)))))
      (lam n U64 (lam0 p (Eq n n) (lam m U64
        (lam0 q (Lt m (uadd n 1)) p)))))''',
    'proof-discharge': '''(def mixed (pi n U64 (pi m U64 (Eq n n)))
      (lam n U64 (app (lam0 p (Eq n n) (lam m U64 p)) (refl n))))''',
    'scalar-discharge': '''(def mixed (pi m U64 (Eq 7 7))
      (app (lam n U64 (lam m U64 (refl n))) 7))''',
    'both-discharge': '''(def mixed (Eq 7 7)
      (app (lam n U64 (app (lam0 p (Eq n n) (lam m U64 p)) (refl n))) 7 9))''',
    'bound-assumption': '''(def mixed (pi n U64 (pi m U64 (pi0 p (Lt m n) (Lt m n))))
      (lam n U64 (lam m U64 (lam0 p (Lt m n) p))))''',
    'bound-discharge': '''(def mixed (Lt 2 4)
      (app (lam n U64 (lam m U64 (lam0 p (Lt m n) p))) 4 2 (decide-lt 2 4)))''',
    'universal-proof': '''(def mixed
      (pi n U64 (pi0 p (pi m U64 (Eq n n)) (Eq n n)))
      (lam n U64 (lam0 p (pi m U64 (Eq n n)) (app p 9))))''',
}
INVALID = {
    'captured-scalar': VALID['scalar-discharge'].replace('(Eq 7 7)', '(Eq m m)'),
    'captured-proof': VALID['proof-discharge'].replace('(pi m U64 (Eq n n))', '(pi m U64 (Eq m m))'),
    'wrong-bound-proof': VALID['bound-discharge'].replace('(decide-lt 2 4)', '(decide-lt 1 4)'),
    'forward-reference': '''(def mixed (pi n U64 (pi0 p (Eq m m) (pi m U64 (Eq n n))))
      (lam n U64 (lam0 p (Eq n n) (lam m U64 p))))''',
    'missing-proof': '(def mixed (Eq 0 0) missing)',
    'false-equality': '(def mixed (Eq 0 1) (refl 0))',
    'false-bound': '(def mixed (Lt 0 0) (decide-lt 0 0))',
}


DIAGNOSTICS = {
    'forward-reference': b'core: unknown name or invalid U64 literal: m',
    'missing-proof': b'core: unknown name or invalid U64 literal: missing',
    'false-bound': b'core: decide-lt needs a true closed inequality',
}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--compiler', required=True)
    args = parser.parse_args()
    fixture = (Path(__file__).resolve().parent / 'core_preserves/lean-mixed-telescope.jhc').read_text()
    declarations = [line for line in fixture.splitlines() if line.startswith('(def ')]
    if len(declarations) != 3:
        raise RuntimeError('expected exactly three Lean-generated mixed declarations')
    earlier, recent, universal = declarations
    valid_cases = dict(VALID)
    valid_cases['generated-mixed'] = fixture
    valid_cases['generated-instantiation'] = fixture + '\n(def instantiated (Eq 4 4) (app mixed_earlier 4 (refl 4) 2 (decide-lt 2 4)))\n(def bound_instantiated (Lt 2 4) (app mixed_recent 4 (refl 4) 2 (decide-lt 2 4)))\n'
    invalid_cases = dict(INVALID)
    mutations = {
        'generated-scalar-capture': (earlier, ' x1)))))', ' x2)))))'),
        'generated-proof-swap': (recent, ' x3)))))', ' x1)))))'),
        'generated-reversed-annotation': (recent, '(lam0 x3 (Lt x2 x0)', '(lam0 x3 (Lt x0 x2)'),
        'generated-universal-capture': (universal, '(app x1 7)', '(refl x2)'),
    }
    for name, (source, old, new) in mutations.items():
        if source.count(old) != 1:
            raise RuntimeError(f'{name}: mutation no longer identifies exactly one location')
        invalid_cases[name] = source.replace(old, new)
    with tempfile.TemporaryDirectory(prefix='jihoo-mixed-') as tmp:
        for valid, cases in ((True, valid_cases), (False, invalid_cases)):
            for name, source in cases.items():
                path = Path(tmp) / (name + '.jhc')
                path.write_text(source)
                operations = ('check', 'preserves') if valid else ('check',)
                for operation in operations:
                    result = subprocess.run([args.compiler, 'core', operation, str(path)],
                                            capture_output=True, timeout=60)
                    if (result.returncode == 0) != valid:
                        raise RuntimeError(f'{name}/{operation}: {result.returncode}: {result.stderr!r}')
                    if not valid and DIAGNOSTICS.get(name, b'core: type mismatch') not in result.stderr:
                        raise RuntimeError(f'{name}: missing core diagnostic: {result.stderr!r}')
    print(f'mixed telescope: {len(valid_cases)} check/preservation controls, {len(invalid_cases)} rejections; no input executed')


if __name__ == '__main__':
    main()
