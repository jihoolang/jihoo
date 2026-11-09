#!/usr/bin/env python3
"""Runtime family-kind admission; no rejected source is ever executed."""
import argparse
from pathlib import Path
import shlex
import tempfile
from core_certificate_process import ROOT, command, success
from core_typing_producer import require

KIND_ERROR = b'a runtime type family takes only u64 indices'
PLAIN_ERROR = b'a type argument holds no buffer, heap data, borrow or function'


def target(body, domain='(Buffer 1)'):
    return f'(def target (pi b {domain} I64) (lam b {domain} {body}))'.encode()


def family_value(kind, value):
    return target(f'(free b (app (lam F {kind} (int 0)) {value}))')


REPRO = target('''(app
 (lam F (pi A (Type 0) (Type 0))
  (lam h (pi x (app F (Buffer 1)) I64)
   (lam x (app F (Buffer 1)) (add (app h x) (app h x)))))
 (lam A (Type 0) A)
 (lam x (Buffer 1) (free x (int 0))) b)''')

VALID = {
    'monomorphic': target('(free b (app (lam A (Type 0) (lam x A (int 0))) U64 7))'),
    'u64-index': family_value('(pi n U64 (Type 0))', '(lam n U64 (Array n))'),
    'erased-u64-index': family_value('(pi0 n U64 (Type 0))', '(lam0 n U64 (Array n))'),
    'two-indices': family_value('(pi n U64 (pi m U64 (Type 0)))', '(lam n U64 (lam m U64 (Array (uadd n m))))'),
    'normalized-index-domain': family_value('(pi n (app (lam A (Type 0) A) U64) (Type 0))', '(lam n U64 U64)'),
    'ghost-type-computation': target('(free b (int 0))', '(app (lam A (Type 0) A) (Buffer 1))'),
    'used-u64-family': target('''(free b (app
      (lam F (pi n U64 (Type 0))
       (lam h (pi x (app F 0) I64)
        (lam x (app F 0) (add (app h x) (app h x)))))
      (lam n U64 U64) (lam x U64 (int 0)) 0))'''),
    'forward-u64-family': target('''(free b (app
      (lam F (pi n U64 (Type 0)) (app (lam G (pi n U64 (Type 0)) (int 0)) F))
      (lam n U64 (Array n))))'''),
}
INVALID = {
    'owner-instantiation': (REPRO, KIND_ERROR),
    'single-use-higher-kind': (REPRO.replace(b'(add (app h x) (app h x))', b'(app h x)'), KIND_ERROR),
    # Conservatively rejected even when this particular result is harmless.
    'constant-higher-kind': (family_value('(pi A (Type 0) (Type 0))', '(lam A (Type 0) U64)'), KIND_ERROR),
    'signed-index': (family_value('(pi n I64 (Type 0))', '(lam n I64 U64)'), KIND_ERROR),
    'higher-family-index': (family_value('(pi G (pi n U64 (Type 0)) (Type 0))', '(lam G (pi n U64 (Type 0)) (app G 0))'), KIND_ERROR),
    # No lambda argument exists here: admission must inspect the expected kind.
    'neutral-forward': (b'(def target (pi F (pi A (Type 0) (Type 0)) I64) '
                        b'(lam F (pi A (Type 0) (Type 0)) (app (lam G (pi A (Type 0) (Type 0)) (int 0)) F)))', KIND_ERROR),
    'buffer-family-result': (family_value('(pi n U64 (Type 0))', '(lam n U64 (Buffer n))'), PLAIN_ERROR),
    'function-family-result': (family_value('(pi n U64 (Type 0))', '(lam n U64 (pi x U64 U64))'), PLAIN_ERROR),
    'direct-owned-type': (target('(app (lam A (Type 0) (lam x A (int 0))) (Buffer 1) b)'), PLAIN_ERROR),
}


def test(compiler, out):
    probe = out / 'family-probe'
    success(command([*compiler, 'build', '-O0', '-I', 'compiler',
                     'tests/core_type_family_probe.jh', '-o', probe], cwd=ROOT))
    for name, data in VALID.items():
        observed = success(command([probe], data))
        require(observed == b'1 1\n', f'{name}: runtime normalization changed owned use or typing: {observed!r}')
        path = out / (name + '.jhc')
        # Buffer-parameter helpers are not exported by textual Core. A closed
        # scalar entry point makes object emission a meaningful positive control.
        # It is compiled only; this suite never runs it.
        path.write_bytes(data + b'\n(export entry (pi n U64 I64) (lam n U64 (app target (alloc 1 (int 7)))))\n')
        success(command([*compiler, 'core', 'check', path]))
        # Artifact controls prove codegen is genuinely reachable for this harness.
        for level in ('-O0', '-O2'):
            obj = out / (name + level + '.o')
            success(command([*compiler, 'core', 'emit-obj', path, level, '-o', obj]))
            require(obj.is_file() and obj.stat().st_size > 0, 'missing positive-control object')
    for name, (data, diagnostic) in INVALID.items():
        rejected = command([probe], data)
        require(rejected.returncode != 0 and not rejected.stdout and diagnostic in rejected.stderr,
                f'{name}: wrong probe rejection {rejected.stderr!r}')
        path = out / (name + '.jhc')
        # Buffer-parameter helpers are not exported by textual Core. A closed
        # scalar entry point makes object emission a meaningful positive control.
        # It is compiled only; this suite never runs it.
        path.write_bytes(data + b'\n(export entry (pi n U64 I64) (lam n U64 (app target (alloc 1 (int 7)))))\n')
        rejected = command([*compiler, 'core', 'check', path])
        require(rejected.returncode != 0 and diagnostic in rejected.stderr, f'{name}: wrong checker rejection')
        for level in ('-O0', '-O2'):
            obj = out / (name + level + '.o')
            rejected = command([*compiler, 'core', 'emit-obj', path, level, '-o', obj])
            require(rejected.returncode != 0 and diagnostic in rejected.stderr and not obj.exists(),
                    f'{name}: codegen did not fail closed at {level}: {rejected.stderr!r}')
    print(f'type-family safety: {len(VALID)} preserved/compiled controls, {len(INVALID)} exact-diagnostic rejections at check/O0/O2; no input executed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-family-safety-') as directory:
        test(shlex.split(args.compiler), Path(directory))

if __name__ == '__main__': main()
