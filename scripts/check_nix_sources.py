#!/usr/bin/env python3
"""Evaluate source-isolation mutations, without building or changing the checkout.

Usage: python3 scripts/check_nix_sources.py --offline
       python3 scripts/check_nix_sources.py --nix /path/to/nix-wrapper --offline

The wrapper must accept normal Nix arguments. Both supported systems are checked
by default; pass --system for a single CI matrix entry. --offline requires an
already cached flake input. This is intentionally not a flake check: recursively evaluating the flake inside its checks is avoided.
"""
import argparse
from contextlib import contextmanager
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

SYSTEMS = ('x86_64-linux', 'aarch64-linux')
TEST_FILES = (
    'scripts/benchmark_compile.py',
    'docs/internals/core-spec.md',
    'docs/language/dependent-types.md',
    'docs/language/dependent-functions.md',
    'docs/language/dependent-aliases.md',
    'docs/language/dependent-records.md',
    'docs/language/proof-automation.md',
    'docs/language/buffer-ranges.md',
    'docs/language/bounded-collection.md',
    'docs/language/list-buffer-transfer.md',
    'docs/language/vector-extension.md',
)
KEYS = ('compilerSrc', 'compilerDrv', 'testsSrc', 'testsDrv', 'graphDrv', 'toolchainDrv')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def copy_checkout(root, destination):
    def ignored(directory, names):
        relative = Path(directory).relative_to(root)
        skip = {'.git', '__pycache__', 'node_modules', '.lake', '.venv'}
        if relative == Path('.'):
            skip |= {'out', '.toolchain', 'result'}
            skip |= {name for name in names if name.startswith('result-')}
        if relative == Path('site'):
            skip |= {'dist', '.astro'}
        return set(names) & skip
    shutil.copytree(root, destination, symlinks=True, ignore=ignored)


def files_under(root, directory):
    """Match readDir's files and symlinks, without following directory symlinks."""
    found = []
    for path in sorted((root / directory).iterdir()):
        rel = path.relative_to(root).as_posix()
        if path.is_dir() and not path.is_symlink():
            found.extend(files_under(root, rel))
        else:
            found.append(rel)
    return found


def evaluate(nix, root, offline, selected):
    # path: deliberately includes untracked additions in each mutation. A git
    # flake would silently drop them and make the add-file checks meaningless.
    uri = json.dumps('path:' + str(root))
    systems = ' '.join(json.dumps(system) for system in selected)
    expression = '''let
      flake = builtins.getFlake URI;
      files = path: prefix:
        let entries = builtins.readDir path;
        in builtins.concatLists (map (name:
          let rel = prefix + name;
          in if entries.${name} == "directory"
             then files (path + "/${name}") (rel + "/") else [ rel ])
          (builtins.attrNames entries));
      snapshot = system:
        let compiler = flake.packages.${system}.jihoo;
            tests = flake.checks.${system}.tests;
        in { name = system; value = {
          compilerDrv = compiler.drvPath; compilerSrc = toString compiler.src;
          compilerFiles = files compiler.src "";
          testsDrv = tests.drvPath; testsSrc = toString tests.src;
          testsFiles = files tests.src "";
          graphDrv = flake.checks.${system}.graph-certificates.drvPath;
          toolchainDrv = flake.checks.${system}.toolchain.drvPath;
        }; };
    in builtins.listToAttrs (map snapshot [ SYSTEMS ])
    '''.replace('URI', uri).replace('SYSTEMS', systems)
    argv = [nix, 'eval', '--json', '--impure', '--no-write-lock-file']
    if offline:
        argv.append('--offline')
    result = subprocess.run(argv + ['--expr', expression], text=True,
                            capture_output=True, timeout=300)
    require(result.returncode == 0, f'Nix evaluation failed:\n{result.stderr}')
    data = json.loads(result.stdout)
    compiler_files = sorted(files_under(root, 'compiler') + files_under(root, 'lib'))
    test_files = sorted(compiler_files + files_under(root, 'tests') +
                        files_under(root, 'examples') + list(TEST_FILES))
    for system in selected:
        for key, expected in (('compilerFiles', compiler_files), ('testsFiles', test_files)):
            actual = sorted(data[system].pop(key))
            missing, extra = sorted(set(expected)-set(actual)), sorted(set(actual)-set(expected))
            require(actual == expected,
                    f'{system} {key}: missing={missing}, extra={extra}')
    require(len({data[system]['compilerSrc'] for system in selected}) == 1,
            'compiler sources differ between systems')
    require(len({data[system]['testsSrc'] for system in selected}) == 1,
            'test sources differ between systems')
    return data


@contextmanager
def mutation(root, relative, operation):
    path = root / relative
    original = path.read_bytes() if path.exists() else None
    if operation == 'add':
        require(original is None, f'mutation addition already exists: {relative}')
        path.write_text('// Nix source isolation probe\n')
    elif operation == 'edit':
        require(original is not None, f'mutation input missing: {relative}')
        path.write_bytes(original + b'\n// Nix source isolation probe\n')
    elif operation == 'remove':
        require(original is not None, f'mutation input missing: {relative}')
        path.unlink()
    else:
        raise ValueError(operation)
    try:
        yield
    finally:
        if original is None:
            path.unlink()
        else:
            path.write_bytes(original)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--nix', default='nix', help='Nix executable or wrapper (one executable, not shell text)')
    parser.add_argument('--offline', action='store_true')
    parser.add_argument('--system', choices=SYSTEMS, action='append',
                        help='system to evaluate; repeatable, default: both supported systems')
    parser.add_argument('--report', type=Path, help='optional JSON evidence with evaluated paths')
    args = parser.parse_args()
    selected = tuple(dict.fromkeys(args.system or SYSTEMS))
    root = args.repo.resolve()
    require((root / 'flake.lock').is_file(), 'expected checkout with flake.nix and flake.lock')
    changes = []
    tests_only = {'testsSrc', 'testsDrv', 'graphDrv'}
    examples = tests_only | {'toolchainDrv'}
    everything = set(KEYS)
    for directory, existing, expected in (
        ('tests', 'tests/run/basics.jh', tests_only),
        ('examples', 'examples/hello.jh', examples),
    ):
        changes += [(existing, 'edit', expected),
                    (directory + '/nix-source-isolation-probe.jh', 'add', expected),
                    (existing, 'remove', expected)]
    changes += [
        ('compiler/main.jh', 'edit', everything),
        ('lib/std/io.jh', 'edit', everything),
        ('docs/internals/core-spec.md', 'edit', {'testsSrc', 'testsDrv'}),
        ('docs/README.md', 'edit', set()),
        ('scripts/benchmark_compile.py', 'edit', {'testsSrc', 'testsDrv'}),
        ('proofs/Jihoo.lean', 'edit', {'graphDrv'}),
    ]
    evidence = {'systems': list(selected), 'mutations': []}
    with tempfile.TemporaryDirectory(prefix='jihoo-nix-sources-') as temporary:
        copied = Path(temporary) / 'checkout'
        copy_checkout(root, copied)
        baseline = evaluate(args.nix, copied, args.offline, selected)
        evidence['baseline'] = baseline
        print(f'PASS exact compiler/test source membership for {len(selected)} systems', flush=True)
        for relative, operation, expected in changes:
            with mutation(copied, relative, operation):
                current = evaluate(args.nix, copied, args.offline, selected)
                for system in selected:
                    actual = {key for key in KEYS if current[system][key] != baseline[system][key]}
                    require(actual == expected,
                            f'{operation} {relative}, {system}: changed={sorted(actual)}, expected={sorted(expected)}')
                evidence['mutations'].append({'path': relative, 'operation': operation,
                                              'changed': sorted(expected), 'evaluated': current})
            print(f'PASS {operation} {relative}: {", ".join(sorted(expected)) or "no rebuild"}', flush=True)
        require(evaluate(args.nix, copied, args.offline, selected) == baseline,
                'restored snapshot differs from baseline')
    if args.report:
        args.report.write_text(json.dumps(evidence, indent=2) + '\n')
    print(f'nix-source-isolation: {len(changes)} mutations, {len(selected)} systems; no builds requested')


if __name__ == '__main__':
    main()
