#!/usr/bin/env python3
"""Offline regression tests for the seed updater; requires Python, Bash and Git."""
import base64
import hashlib
import io
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
ARCHES = {'x86_64': 62, 'aarch64': 183}


def sri(data):
    return 'sha256-' + base64.b64encode(hashlib.sha256(data).digest()).decode()


def archive(version, arch, machine=None):
    """Small, non-executable ELF-header fixture with the required release layout."""
    header = bytearray(20)
    header[:6] = b'\x7fELF\x02\x01'
    header[18:20] = (ARCHES[arch] if machine is None else machine).to_bytes(2, 'little')
    result = io.BytesIO()
    with tarfile.open(fileobj=result, mode='w:gz') as tar:
        for name, data in {'LICENSE': b'test license\n',
                           'share/jihoo/lib/std/prelude.jh': b'// fixture\n',
                           'bin/jihoo': bytes(header)}.items():
            member = tarfile.TarInfo(f'jihoo-v{version}-{arch}-linux/{name}')
            member.size = len(data)
            member.mode = 0o755 if name == 'bin/jihoo' else 0o644
            tar.addfile(member, io.BytesIO(data))
    return result.getvalue()


class SeedUpdate(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='jihoo-seed-test-')
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.repo = self.base / 'repo'
        self.assets = self.base / 'assets'
        self.bin = self.base / 'bin'
        for path in [self.repo / 'scripts', self.repo / 'tests',
                     self.repo / 'bootstrap', self.assets, self.bin]:
            path.mkdir(parents=True)
        for name in ['scripts/bump-version.sh', 'tests/bootstrap_seed.py']:
            shutil.copyfile(ROOT / name, self.repo / name)
        self.old = {arch: archive('0.1.0', arch) for arch in ARCHES}
        self.new = {arch: archive('0.2.0', arch) for arch in ARCHES}
        self.flake = ('{\n      version = "9.9.9";\n      seed = {\n'
                      '        version = "0.1.0";\n        hash = {\n' +
                      ''.join(f'          {arch}-linux = "{sri(data)}";\n'
                              for arch, data in self.old.items()) +
                      '        };\n      };\n}\n')
        (self.repo / 'flake.nix').write_text(self.flake)
        for arch, data in self.old.items():
            (self.repo / 'bootstrap' / f'jihoo-{arch}-linux.tar.gz').write_bytes(data)
        for arch, data in self.new.items():
            name = f'jihoo-v0.2.0-{arch}-linux.tar.gz'
            (self.assets / name).write_bytes(data)
            (self.assets / (name + '.sha256')).write_text(
                f'{hashlib.sha256(data).hexdigest()}  {name}\n')
        self.stub('gh', '''import os, pathlib, shutil, sys
args = sys.argv[1:]
assert args[:2] in (['release', 'view'], ['release', 'download']), args
assert args[2:5] == ['-R', 'jihoolang/jihoo', 'v0.2.0'], args
if args[1] == 'download':
    target = pathlib.Path(args[args.index('--dir') + 1])
    for i, arg in enumerate(args):
        if arg == '--pattern':
            source = pathlib.Path(os.environ['SEED_TEST_ASSETS']) / args[i + 1]
            if not source.is_file():
                sys.exit('missing release asset: ' + source.name)
            shutil.copyfile(source, target / source.name)
''')
        self.stub('nix', '''import base64, hashlib, pathlib, sys
assert sys.argv[1:6] == ['hash', 'file', '--type', 'sha256', '--sri'], sys.argv
print('sha256-' + base64.b64encode(hashlib.sha256(pathlib.Path(sys.argv[6]).read_bytes()).digest()).decode())
''')
        self.env = {key: value for key, value in os.environ.items()
                    if not key.startswith('GIT_')}
        self.env.update(PATH=str(self.bin) + os.pathsep + os.environ['PATH'],
                        SEED_TEST_ASSETS=str(self.assets),
                        GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull,
                        GIT_AUTHOR_NAME='Seed Test', GIT_AUTHOR_EMAIL='seed@example.invalid',
                        GIT_COMMITTER_NAME='Seed Test', GIT_COMMITTER_EMAIL='seed@example.invalid')
        self.git('init', '-q')
        self.git('add', '.')
        self.git('commit', '-qm', 'Fixture')
        self.head = self.git('rev-parse', 'HEAD').stdout
        self.before = self.snapshot()

    def stub(self, name, source):
        path = self.bin / name
        path.write_text(f'#!{sys.executable}\n' + source)
        path.chmod(0o755)

    def run_command(self, *args):
        return subprocess.run(args, cwd=self.repo, env=self.env,
                              text=True, capture_output=True, timeout=30)

    def git(self, *args):
        result = self.run_command('git', *args)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def snapshot(self):
        return {str(path.relative_to(self.repo)): path.read_bytes()
                for path in self.repo.rglob('*')
                if path.is_file() and '.git' not in path.relative_to(self.repo).parts}

    def update(self):
        return self.run_command('bash', 'scripts/bump-version.sh', 'seed', 'v0.2.0')

    def assert_unchanged_failure(self, expected):
        result = self.update()
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(expected, result.stdout + result.stderr)
        self.assertEqual(self.snapshot(), self.before)
        self.assertEqual(self.git('rev-parse', 'HEAD').stdout, self.head)
        self.assertEqual(self.git('status', '--porcelain').stdout, '')

    def test_success_updates_both_archives_pins_and_commits(self):
        result = self.update()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        flake = (self.repo / 'flake.nix').read_text()
        self.assertIn('      version = "9.9.9";', flake)
        self.assertIn('        version = "0.2.0";', flake)
        for arch, data in self.new.items():
            self.assertIn(f'{arch}-linux = "{sri(data)}";', flake)
            self.assertEqual((self.repo / 'bootstrap' / f'jihoo-{arch}-linux.tar.gz').read_bytes(), data)
        self.assertEqual(self.git('log', '-1', '--format=%s').stdout.strip(), 'Bootstrap from 0.2.0')
        self.assertEqual(self.git('rev-list', '--count', 'HEAD').stdout.strip(), '2')
        self.assertEqual(set(self.git('diff-tree', '--no-commit-id', '--name-only', '-r', 'HEAD').stdout.splitlines()),
                         {'flake.nix', *(f'bootstrap/jihoo-{arch}-linux.tar.gz' for arch in ARCHES)})
        self.assertEqual(self.git('status', '--porcelain').stdout, '')

    def test_second_arch_checksum_mismatch_does_not_modify_checkout(self):
        path = self.assets / 'jihoo-v0.2.0-aarch64-linux.tar.gz'
        path.write_bytes(path.read_bytes() + b'tampered')
        self.assert_unchanged_failure('FAILED')

    def test_missing_second_archive_does_not_modify_checkout(self):
        (self.assets / 'jihoo-v0.2.0-aarch64-linux.tar.gz').unlink()
        self.assert_unchanged_failure('missing release asset')

    def test_malformed_checksum_records_do_not_modify_checkout(self):
        name = 'jihoo-v0.2.0-aarch64-linux.tar.gz'
        digest = hashlib.sha256(self.new['aarch64']).hexdigest()
        for record in [f'{digest}  wrong.tar.gz\n', f'not-a-hash  {name}\n',
                       f'{digest}  {name} extra\n', f'{digest}  {name}\n{digest}  {name}\n', '']:
            with self.subTest(record=record):
                (self.assets / (name + '.sha256')).write_text(record)
                self.assert_unchanged_failure('invalid checksum')

    def test_validator_rejects_archive_tampering(self):
        path = self.repo / 'bootstrap/jihoo-x86_64-linux.tar.gz'
        path.write_bytes(path.read_bytes() + b'tampered')
        result = self.run_command(sys.executable, 'tests/bootstrap_seed.py')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('SHA-256 differs', result.stderr)

    def test_validator_rejects_wrong_elf_architecture_even_with_matching_hash(self):
        data = archive('0.1.0', 'aarch64', machine=62)
        (self.repo / 'bootstrap/jihoo-aarch64-linux.tar.gz').write_bytes(data)
        (self.repo / 'flake.nix').write_text(self.flake.replace(sri(self.old['aarch64']), sri(data)))
        result = self.run_command(sys.executable, 'tests/bootstrap_seed.py')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('compiler architecture differs from aarch64-linux', result.stderr)


if __name__ == '__main__':
    unittest.main()
