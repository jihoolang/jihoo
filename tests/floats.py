#!/usr/bin/env python3
"""Compare std.float's digits with Python's correctly rounded repr, %f and %e."""

import argparse
import math
from pathlib import Path
import random
import struct
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]

PROGRAM = """import std.float

fn main() {
    var out = String.new()
    let b64: [u64; N64] = [BITS64]
    let p: [i64; N64] = [PRECISIONS]
    let b32: [u32; N32] = [BITS32]
    for i in 0..N64 {
        var b = b64[i]
        let x = unsafe { *(&b as *f64) }
        x.show(&out)
        out.push(' ')
        float.write_fixed(&out, float.parts_f64(x), p[i])
        out.push(' ')
        float.write_exponent(&out, float.parts_f64(x), p[i])
        out.push('\\n')
    }
    for b in b32 {
        var c = b
        let x = unsafe { *(&c as *f32) }
        x.show(&out)
        out.push('\\n')
    }
    print(out)
}
"""


def shortest(x, digits_text):
    """Python's shortest digits laid out as jihoo's Show does."""
    if math.isnan(x):
        return "NaN"
    if math.isinf(x):
        return "inf" if x > 0 else "-inf"
    sign = "-" if digits_text.startswith("-") else ""
    mantissa, _, exponent = digits_text.lstrip("-").partition("e")
    whole, _, fraction = mantissa.partition(".")
    digits = (whole + fraction).lstrip("0")
    k = len(whole) - (len(whole + fraction) - len(digits)) + int(exponent or 0)
    digits = digits.rstrip("0")
    if not digits:
        return sign + "0.0"
    if -4 < k <= 16:
        if k <= 0:
            body = "0." + "0" * -k + digits
        elif len(digits) > k:
            body = digits[:k] + "." + digits[k:]
        else:
            body = digits + "0" * (k - len(digits)) + ".0"
    else:
        body = digits[0] + ("." + digits[1:] if len(digits) > 1 else "") + "e" + str(k - 1)
    return sign + body


def f32_digits(x):
    """The fewest correctly rounded digits that read back as the f32."""
    for p in range(1, 12):
        text = "%.*e" % (p - 1, x)
        if struct.unpack("<f", struct.pack("<f", float(text)))[0] == x:
            return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "out/jihoo")
    compiler = parser.parse_args().compiler.resolve()

    rng = random.Random(7)
    bits = [rng.getrandbits(64) for _ in range(3000)]
    for _ in range(500):
        nice = rng.choice([rng.uniform(-1e6, 1e6), round(rng.uniform(0, 1000), rng.randint(0, 6)),
                           rng.randint(-10**9, 10**9) * 1.0])
        bits.append(struct.unpack("<Q", struct.pack("<d", nice))[0])
    # Each exponent's smallest, next and largest significand, subnormals included.
    for e in range(0, 2047, 7):
        bits += [e << 52, (e << 52) | 1, (e << 52) | ((1 << 52) - 1)]
    precisions = [rng.randint(0, 20) for _ in bits]
    bits32 = [rng.getrandbits(32) for _ in range(3000)]

    program = (PROGRAM.replace("N64", str(len(bits))).replace("N32", str(len(bits32)))
               .replace("BITS64", ", ".join(map(str, bits)))
               .replace("PRECISIONS", ", ".join(map(str, precisions)))
               .replace("BITS32", ", ".join(map(str, bits32))))
    with tempfile.TemporaryDirectory(prefix="jihoo-floats-") as directory:
        source = Path(directory) / "floats.jh"
        source.write_text(program)
        result = subprocess.run([str(compiler), "run", "-O0", source], capture_output=True,
                                text=True, timeout=300)
    assert result.returncode == 0, result.stderr
    lines = result.stdout.splitlines()

    wrong = []
    for line, b, precision in zip(lines, bits, precisions):
        x = struct.unpack("<d", struct.pack("<Q", b))[0]
        short, fixed, exponent = line.split(" ")
        expected = [shortest(x, repr(x))]
        found = [short]
        if math.isfinite(x):
            mantissa, _, power = ("%.*e" % (precision, x)).partition("e")
            expected += ["%.*f" % (precision, x), mantissa + "e" + str(int(power))]
            found += [fixed, exponent]
        if found != expected:
            wrong.append((b, found, expected))
    for line, b in zip(lines[len(bits):], bits32):
        x = struct.unpack("<f", struct.pack("<I", b))[0]
        expected = shortest(x, f32_digits(x)) if math.isfinite(x) else shortest(x, "")
        if line != expected:
            wrong.append((b, line, expected))
    assert not wrong, wrong[:10]
    print(f"Floats: {len(bits) * 3 + len(bits32)} shortest, fixed and exponent texts match Python")


if __name__ == "__main__":
    main()
