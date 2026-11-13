#!/usr/bin/env python3
"""Offline release-version regressions; no release, tag, push or network access."""
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
PAGE = 'site/src/content/docs/start/getting-started.md'
FILES = ['flake.nix', 'compiler/main.jh', PAGE]
REAL_GIT = shutil.which('git')


class ReleaseVersion(unittest.TestCase):
    fixture_version = None

    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='jihoo-release-test-')
        self.addCleanup(temp.cleanup)
        self.base = Path(temp.name)
        self.repo = self.base / 'repo'
        self.bin = self.base / 'bin'
        self.bin.mkdir()
        for name in ['scripts/bump-version.sh', *FILES]:
            target = self.repo / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, target)
        if self.fixture_version is not None:
            # Simulate an already-bumped checkout without running a release or
            # changing the repository's actual version or bootstrap seed.
            substitutions = {
                'flake.nix': (r'^      version = "[0-9.]+";$',
                              f'      version = "{self.fixture_version}";'),
                'compiler/main.jh': (r'^const VERSION = "[0-9.]+"$',
                                     f'const VERSION = "{self.fixture_version}"'),
                PAGE: (r'v[0-9]+\.[0-9]+\.[0-9]+', f'v{self.fixture_version}'),
            }
            for name, (pattern, replacement) in substitutions.items():
                path = self.repo / name
                content, count = re.subn(pattern, replacement, path.read_text(), flags=re.M)
                self.assertGreater(count, 0, name)
                path.write_text(content)
        self.current_version = next(
            line.split('"')[1] for line in (self.repo / 'compiler/main.jh').read_text().splitlines()
            if line.startswith('const VERSION = '))
        major, minor, patch = map(int, self.current_version.split('.'))
        self.next_version = f'{major}.{minor}.{patch + 1}'
        self.later_version = f'{major}.{minor}.{patch + 2}'
        self.env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
        self.env.update(PATH=str(self.bin) + os.pathsep + os.environ['PATH'],
                        GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull,
                        GIT_AUTHOR_NAME='Test', GIT_AUTHOR_EMAIL='test@example.invalid',
                        GIT_COMMITTER_NAME='Test', GIT_COMMITTER_EMAIL='test@example.invalid',
                        RELEASE_TEST_LOG=str(self.base / 'calls'))
        self.git('init', '-q', '-b', 'main')
        self.git('add', '.')
        self.git('commit', '-qm', 'Fixture')
        self.stub('git', f'''import os, subprocess, sys
args = sys.argv[1:]
with open(os.environ['RELEASE_TEST_LOG'], 'a') as log:
    log.write('git ' + ' '.join(args) + '\\n')
if args[0] in ('fetch', 'push') or args[:2] == ['tag', '-a']:
    sys.exit(1 if os.environ.get('FAIL_FETCH') and args[0] == 'fetch' else 0)
if args == ['rev-parse', 'origin/main']:
    if os.environ.get('STALE_MAIN'):
        print('0' * 40)
        sys.exit(0)
    args = ['rev-parse', 'HEAD']
if args[:3] == ['rev-parse', '-q', '--verify'] and os.environ.get('EXISTING_TAG'):
    sys.exit(0)
sys.exit(subprocess.call([{REAL_GIT!r}, *args]))
''')
        self.stub('gh', '''import sys
if sys.argv[1:3] == ['run', 'list']:
    print('123')
''')
        self.stub('sleep', '')

    def stub(self, name, source):
        path = self.bin / name
        path.write_text(f'#!{sys.executable}\n' + source)
        path.chmod(0o755)

    def run_command(self, *args):
        return subprocess.run(args, cwd=self.repo, env=self.env, text=True,
                              capture_output=True, timeout=30)

    def git(self, *args):
        result = self.run_command(REAL_GIT, *args)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout.strip()

    def update(self, version=None):
        version = self.next_version if version is None else version
        return self.run_command('bash', 'scripts/bump-version.sh', 'release', version)

    def assert_failure_unchanged(self, expected, version=None):
        before = {name: (self.repo / name).read_bytes() if (self.repo / name).exists()
                  else None for name in FILES}
        head = self.git('rev-parse', 'HEAD')
        status = self.git('status', '--porcelain')
        result = self.update(version)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(expected, result.stdout + result.stderr)
        for name, data in before.items():
            self.assertEqual((self.repo / name).read_bytes() if (self.repo / name).exists()
                             else None, data)
        self.assertEqual(self.git('rev-parse', 'HEAD'), head)
        self.assertEqual(self.git('status', '--porcelain'), status)
        calls = (self.base / 'calls').read_text()
        for action in ['git add ', 'git commit ', 'git tag -a ', 'git push ']:
            self.assertNotIn(action, calls)

    def test_versions_and_release_commit(self):
        for version in [self.next_version, 'v' + self.later_version]:
            with self.subTest(version=version):
                before = {name: (self.repo / name).read_text() for name in FILES}
                old = next(line.split('"')[1] for line in before['compiler/main.jh'].splitlines()
                           if line.startswith('const VERSION = '))
                new = version.removeprefix('v')
                result = self.update(version)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                expected = {
                    'flake.nix': before['flake.nix'].replace(f'\n      version = "{old}";', f'\n      version = "{new}";'),
                    'compiler/main.jh': before['compiler/main.jh'].replace(f'const VERSION = "{old}"', f'const VERSION = "{new}"'),
                    # Published downloads can lag the compiler during release preparation.
                    PAGE: re.sub(r'v[0-9]+\.[0-9]+\.[0-9]+', f'v{new}', before[PAGE]),
                }
                for name in FILES:
                    self.assertEqual((self.repo / name).read_text(), expected[name])
                self.assertEqual(set(self.git('diff-tree', '--no-commit-id', '--name-only', '-r', 'HEAD').splitlines()), set(FILES))
                self.assertEqual(self.git('log', '-1', '--format=%s'), f'Release {new}')
                self.assertEqual(self.git('status', '--porcelain'), '')
                self.assertEqual(self.git('tag'), '')  # annotated tag command is stubbed

    def test_invalid_or_unchanged_version(self):
        for version, error in [('bad', 'bad version'), (self.current_version, 'already')]:
            with self.subTest(version=version):
                self.assert_failure_unchanged(error, version)

    def test_malformed_inputs(self):
        cases = [
            ('flake.nix', '', 'package version'),
            ('flake.nix', f'      version = "{self.current_version}";\n' * 2, 'package version'),
            ('compiler/main.jh', '', 'compiler VERSION'),
            ('compiler/main.jh', f'const VERSION = "{self.current_version}"\n' * 2, 'compiler VERSION'),
            ('compiler/main.jh', f'const VERSION = "{self.next_version}"\n', 'compiler VERSION'),
            (PAGE, '', 'missing release references'),
            (PAGE, f'releases/download/v{self.current_version}/jihoo-v{self.current_version}-', 'missing release references'),
        ]
        for name, content, error in cases:
            with self.subTest(name=name, content=content):
                self.git('reset', '--hard', '-q', 'HEAD')
                (self.repo / name).write_text(content)
                self.git('add', name)
                self.git('commit', '-qm', 'Malformed fixture')
                self.assert_failure_unchanged(error)
                self.git('reset', '--hard', '-q', 'HEAD~')

    def test_missing_compiler_or_page(self):
        for name in ['compiler/main.jh', PAGE]:
            with self.subTest(name=name):
                self.git('rm', name)
                self.git('commit', '-qm', 'Missing fixture')
                self.assert_failure_unchanged('No such file')
                self.git('reset', '--hard', '-q', 'HEAD~')

    def test_release_guards(self):
        for key, error in [('FAIL_FETCH', ''), ('STALE_MAIN', 'main is not origin/main'), ('EXISTING_TAG', 'already exists')]:
            with self.subTest(key=key):
                self.env[key] = '1'
                self.assert_failure_unchanged(error)
                del self.env[key]
        self.git('checkout', '-qb', 'feature')
        self.assert_failure_unchanged('release from main')

    def test_dirty_worktree_and_index(self):
        with (self.repo / 'compiler/main.jh').open('a') as out:
            out.write('// dirty\n')
        self.assert_failure_unchanged('working tree has changes')
        self.git('add', 'compiler/main.jh')
        self.assert_failure_unchanged('working tree has changes')


class ReleaseVersionAfterBump(ReleaseVersion):
    """Run the entire suite against a simulated 0.6.0 checkout as well."""
    fixture_version = '0.6.0'


if __name__ == '__main__':
    unittest.main()
