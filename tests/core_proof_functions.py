#!/usr/bin/env python3
"""Actual Core controls for mixed proof functions; no input is executed."""
import argparse
from pathlib import Path
import subprocess
import tempfile

VALID = {
    'retain': '''(def retain (pi n U64 (pi0 p (Eq n n) (pi m U64 (Eq n n))))
      (lam n U64 (lam0 p (Eq n n) (lam m U64 p))))''',
    'higher': '''(def higher
      (pi n U64 (pi0 f (pi0 p (Eq n n) (Eq n n)) (pi0 q (Eq n n) (Eq n n))))
      (lam n U64 (lam0 f (pi0 p (Eq n n) (Eq n n))
        (lam0 q (Eq n n) (app f q)))))''',
    'universal': '''(def universal
      (pi0 p (pi n U64 (Eq n n)) (pi m U64 (Eq m m)))
      (lam0 p (pi n U64 (Eq n n)) (lam m U64 (app p m))))''',
    'proof-beta': '''(def beta (pi n U64 (pi m U64 (Eq n n)))
      (lam n U64 (app (lam0 p (Eq n n) (lam m U64 p)) (refl n))))''',
    'both-beta': '''(def beta (pi m U64 (Eq 7 7))
      (app (lam n U64 (app (lam0 p (Eq n n) (lam m U64 p)) (refl n))) 7))''',
    'proof-capture': '''(def capture
      (pi0 f (pi0 p (Eq 0 0) (Eq 0 0)) (pi0 q (Eq 0 0) (Eq 0 0)))
      (lam0 f (pi0 p (Eq 0 0) (Eq 0 0))
        (app (lam0 g (pi0 p (Eq 0 0) (Eq 0 0))
          (lam0 q (Eq 0 0) (app g q))) f)))''',
    'bound-function': '''(def bound
      (pi n U64 (pi m U64 (pi0 p (Lt m n) (Lt m n))))
      (lam n U64 (lam m U64 (lam0 p (Lt m n) p))))''',
    'zero-le': '''(def bound (pi n U64 (Lt 0 (uadd n 1))) (lam n U64 (zero-le n)))''',
}
INVALID = {
    'scalar-capture': VALID['retain'].replace('(pi m U64 (Eq n n))', '(pi m U64 (Eq m m))'),
    'substitution-capture': VALID['both-beta'].replace('(pi m U64 (Eq 7 7))', '(pi m U64 (Eq m m))'),
    'wrong-proof-argument': '''(def bad (Eq 0 1)
      (app (lam0 p (Eq 0 1) p) (refl 0)))''',
    'wrong-bound-argument': '''(def bad (Lt 2 4)
      (app (lam0 p (Lt 2 4) p) (decide-lt 1 4)))''',
    'false-bound': '(def bad (Lt 0 0) (decide-lt 0 0))',
    'missing-proof': '(def bad (Eq 0 0) missing)',
    'forward-index': '''(def bad (pi n U64 (pi0 p (Eq m m) (pi m U64 (Eq m m))))
      (lam n U64 (lam0 p (Eq n n) (lam m U64 p))))''',
}
DIAGNOSTICS = {
    'false-bound': b'core: decide-lt needs a true closed inequality',
    'missing-proof': b'core: unknown name or invalid U64 literal: missing',
    'forward-index': b'core: unknown name or invalid U64 literal: m',
}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--compiler', required=True)
    args = parser.parse_args()
    fixture = (Path(__file__).resolve().parent / 'core_preserves/lean-mixed-proof-translation.jhc').read_text()
    declarations = [line for line in fixture.splitlines() if line.startswith('(def ')]
    if len(declarations) != 6:
        raise RuntimeError('expected six proved generated declarations')
    valid_cases = dict(VALID)
    invalid_cases = dict(INVALID)
    for i, source in enumerate(declarations):
        valid_cases[f'generated-{i}'] = source
    mutations = {
        'translated-scalar-capture': (0, '(lam x2 U64 x1)', '(lam x2 U64 (refl x2))'),
        'translated-function-result': (1, '(app x1 x2)', 'x1'),
        'translated-universal-capture': (2, '(app x0 x1)', '(app x0 7)'),
        'translated-wrong-proof': (3, '(refl 7)', '(refl 8)'),
        'translated-false-bound': (4, '(zero-le x0)', '(decide-lt 0 0)'),
        'translated-erasure': (0, '(lam0 x1 (Eq x0 x0)', '(lam x1 (Eq x0 x0)'),
    }
    for name, (i, old, new) in mutations.items():
        if declarations[i].count(old) != 1:
            raise RuntimeError(f'{name}: mutation must target one occurrence')
        invalid_cases[name] = declarations[i].replace(old, new)
    DIAGNOSTICS['translated-false-bound'] = b'core: decide-lt needs a true closed inequality'
    DIAGNOSTICS['translated-erasure'] = b'core: proof binders must be erased'
    with tempfile.TemporaryDirectory(prefix='jihoo-proof-functions-') as tmp:
        for accepted, cases in ((True, valid_cases), (False, invalid_cases)):
            for name, source in cases.items():
                path = Path(tmp) / (name + '.jhc')
                path.write_text(source)
                for operation in (('check', 'preserves') if accepted else ('check',)):
                    r = subprocess.run([args.compiler, 'core', operation, str(path)],
                                       capture_output=True, timeout=60)
                    if (r.returncode == 0) != accepted:
                        raise RuntimeError(f'{name}/{operation}: {r.returncode}: {r.stderr!r}')
                    if not accepted and DIAGNOSTICS.get(name, b'core: type mismatch') not in r.stderr:
                        raise RuntimeError(f'{name}: wrong diagnostic: {r.stderr!r}')
    print('mixed proof functions: 14 check/preserves controls, 13 exact-diagnostic rejections; no input executed')


if __name__ == '__main__':
    main()
