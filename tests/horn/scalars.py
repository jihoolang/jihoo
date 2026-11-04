"""Read emitted boundary numerals with the independent Horn reader.

Run as python3 -I tests/horn/scalars.py COMPILER, from the checkout root.
Both targets are exercised without executing cross-compiled programs.
"""

import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "differential"))
from check import Rules, build, parse, value


def main():
    expected = {
        "minimum": -(1 << 127),
        "maximum": (1 << 127) - 1,
        "minimum_next": -(1 << 127) + 1,
        "negative_one": -1,
        "unsigned_upper": 1 << 127,
        "unsigned_maximum": (1 << 128) - 1,
    }
    for target in ("x86_64", "aarch64"):
        for name, want in expected.items():
            result = subprocess.run(
                [sys.argv[1], "emit-horn", "--target", target, "--lib",
                 "tests/horn/scalar_bounds.jh", "--fn", name],
                capture_output=True, text=True,
            )
            assert result.returncode == 0, f"{target} {name}: {result.stderr}"
            rules = [f for f in parse(result.stdout) if f[0] == "rule" and f[-1][0] == "fn." + name]
            assert len(rules) == 1 and rules[0][2] == [], f"{target} {name}: expected one closed rule"
            got = value(build(rules[0][-1][1], {}))
            assert got == want, f"{target} {name}: {got} != {want}"
        result = subprocess.run(
            [sys.argv[1], "emit-horn", "--target", target, "--lib",
             "tests/horn/scalar_bounds.jh", "--fn", "unsigned_case"],
            capture_output=True, text=True,
        )
        assert result.returncode == 0, f"{target} unsigned_case: {result.stderr}"
        rules = Rules(result.stdout)
        for x in (0, (1 << 64) - 1, 1 << 127, (1 << 128) - 1):
            want = int(x == (1 << 64) - 1)
            got = rules.results("fn.unsigned_case", [x])
            assert got == {want}, f"{target} unsigned_case({x}): {got} != {{{want}}}"
    print("Horn scalar boundaries: 12 exact constants and 8 switch results across both targets")


if __name__ == "__main__":
    main()
