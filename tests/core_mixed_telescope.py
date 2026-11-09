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
    with tempfile.TemporaryDirectory(prefix='jihoo-mixed-') as tmp:
        for valid, cases in ((True, VALID), (False, INVALID)):
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
    print(f'mixed telescope: {len(VALID)} check/preservation controls, {len(INVALID)} rejections; no input executed')


if __name__ == '__main__':
    main()
