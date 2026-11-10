#!/usr/bin/env python3
"""Core function IDs must retain distinct, authentic backend symbols.

Compile-only regressions: never execute allocator-shadowing programs. This is
implementation evidence, not a proof of the native linker or foreign allocator.
"""
import argparse
from pathlib import Path
import shlex
import tempfile
from core_certificate_process import ROOT, command, success
from core_typing_producer import require


def test(compiler, folder):
    source = '#![dependent_core]\nexport fn NAME(n: u64) -> u64 { n }\n'
    heap = 'export fn test(n: u64) -> i64 { free(alloc(n, 7), 5) }\n'
    cases = []
    for name in ('malloc', '__jihoo_dependent_main', '__jihoo_core_recursion_3', '__jihoo_core_drop_3'):
        cases.append((name, '.jh', source.replace('NAME', name) + heap, True))
    for name in ('malloc', 'free', '__jihoo_dependent_main', '__jihoo_core_recursion_3', '__jihoo_core_drop_3'):
        cases.append(('raw-' + name, '.jhc',
                      f'(export {name} (pi n U64 U64) (lam n U64 n))\n'
                      '(export test (pi n U64 I64) (lam n U64 (free (alloc n (int 7)) (int 5))))\n', True))
    # Reservation is consistent even before a later translation unit uses heap.
    cases.append(('no-heap', '.jh', source.replace('NAME', 'malloc'), True))
    cases.append(('entry-collision', '.jh', source.replace('NAME', '__jihoo_dependent_main') +
                  'fn main() -> i64 { 0 }\n', False))
    # Imported exports share the same global symbol namespace.
    module = folder / 'foreign.jh'
    module.write_text(source.replace('NAME', 'malloc'))
    cases.append(('imported', '.jh', '#![dependent_core]\nimport foreign\n' + heap, True))
    checks = 0
    for name, suffix, text, library in cases:
        path = folder / (name + suffix)
        path.write_text(text)
        for target in ('x86_64', 'aarch64'):
            for level in ('-O0', '-O2'):
                obj = folder / f'{name}-{target}-{level}.o'
                options = ['--lib'] if library and suffix == '.jh' else []
                frontend = ['core'] if suffix == '.jhc' else []
                result = command([*compiler, *frontend, 'emit-obj', path, *options, '--target', target,
                                  level, '-o', obj], cwd=ROOT)
                require(result.returncode != 0 and not obj.exists() and
                        (b'core: reserved dependent_core name' if name in ('__jihoo_dependent_main', 'entry-collision')
                         else b'core MIR: reserved runtime export symbol') in result.stderr,
                        f'{name}: wrong rejection: {result.stderr!r}')
                checks += 1
    # Private source names do not become external symbols. Near-prefix exports
    # remain legal, and ordinary heap/entry lowering remains operational.
    controls = {
        'private': '#![dependent_core]\nfn malloc(n: u64) -> u64 { n }\n' +
                   'export fn allocation(n: u64) -> i64 { free(alloc(malloc(n), 7), 5) }\n',
        'near': source.replace('NAME', 'malloc_value') + heap,
        'entry': '#![dependent_core]\nfn main() -> i64 { free(alloc(1, 7), 0) }\n',
    }
    objects = 0
    for name, text in controls.items():
        path = folder / (name + '.jh')
        path.write_text(text)
        for target in ('x86_64', 'aarch64'):
            for level in ('-O0', '-O2'):
                obj = folder / f'valid-{name}-{target}-{level}.o'
                options = [] if name == 'entry' else ['--lib']
                success(command([*compiler, 'emit-obj', path, *options, '--target', target,
                                 level, '-o', obj], cwd=ROOT))
                require(obj.exists() and obj.stat().st_size > 0, 'positive control emitted no object')
                objects += 1
    print(f'Core symbols: {checks} exact compile-only rejections; {objects} positive objects; '
          'source/raw/imported/entry namespaces, both targets and O0/O2')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='jihoo-symbols-') as folder:
        test(shlex.split(args.compiler), Path(folder))


if __name__ == '__main__':
    main()
