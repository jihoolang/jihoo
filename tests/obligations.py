#!/usr/bin/env python3
"""Check `emit-obligations` with an independent reader: its structure, the
model of known functions, and what it must not follow."""
import argparse
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]

PROGRAM = """
fn clamp(x: i64, lo: i64, hi: i64) -> i64 {
    if x < lo { return lo }
    if x > hi { return hi }
    x
}

fn sum(xs: [i64]) -> i64 {
    var s = 0
    var i = 0
    while i < xs.len {
        s += xs[i]
        i += 1
    }
    s
}

fn bump(inout x: i64) {
    x += 1
}

fn escapes(n: i64) -> i64 {
    var x = n
    bump(&x)
    x
}

fn widths(a: u8, b: i32) -> u64 {
    let big: u64 = 18446744073709551615
    big - a as u64 + b as u64
}

fn wide(x: i128, y: u128) -> i128 {
    x + y as i128
}

fn main() {
    println(clamp(5, 0, 3) + sum([1, 2]) + escapes(1))
    println(wide(1, 2))
    println(widths(1, 2))
}
"""


def parse(text):
    tokens = text.replace("(", " ( ").replace(")", " ) ").split()
    stack = [[]]
    for t in tokens:
        if t == "(":
            stack.append([])
        elif t == ")":
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(t)
    assert len(stack) == 1, "unbalanced parentheses"
    return stack[0]


def functions(text):
    out = {}
    for f in parse(text):
        assert f[0] == "function" and len(f) >= 7, f[:3]
        name, symbol, args, locals_, lengths = f[1], f[2], f[3], f[4], f[5]
        assert isinstance(name, str) and isinstance(symbol, str)
        assert args[0] == "args" and locals_[0] == "locals" and lengths[0] == "lengths"
        blocks = f[6:]
        for i, b in enumerate(blocks):
            assert b[0] == "block" and b[1] == str(i), (name, b[:2])
            for s in b[2:-1]:
                assert s[0] == "set" and int(s[1]) < len(locals_) - 1, (name, s)
                assert len(s) == 3 or (len(s) == 4 and s[3][0] == "at"), (name, s)
            term = b[-1]
            targets = {"goto": term[1:], "switch": term[2:], "any": term[1:],
                       "assert": term[3:4], "call": term[2:]}.get(term[0], [])
            if term[0] == "assert":
                assert len(term) == 5 and term[4][0] == "at", (name, term)
            assert term[0] in ["goto", "switch", "any", "assert", "call", "trap", "return",
                               "unreachable"], (name, term)
            for t in targets:
                assert int(t) < len(blocks), (name, term)
        for pair in lengths[1:]:
            assert locals_[1 + int(pair[1])] == ["int", "0", "9223372036854775807"]
        out[name] = {"locals": locals_[1:], "lengths": lengths[1:], "blocks": blocks}
    return out


def forms(tree, head):
    if isinstance(tree, list):
        if tree and tree[0] == head:
            yield tree
        for t in tree:
            yield from forms(t, head)


def main():
    ap = argparse.ArgumentParser(__doc__)
    ap.add_argument("--compiler", type=Path, required=True)
    args = ap.parse_args()
    with tempfile.TemporaryDirectory() as d:
        src = Path(d) / "obligations.jh"
        src.write_text(PROGRAM)

        def emit(*options):
            r = subprocess.run([str(args.compiler), "emit-obligations", *options, str(src)],
                               cwd=ROOT, capture_output=True, text=True, timeout=90)
            assert r.returncode == 0, r.stderr
            return functions(r.stdout)

        debug = emit()
        i64 = ["int", "-9223372036854775808", "9223372036854775807"]

        clamp = debug["clamp"]
        assert clamp["locals"][:4] == [i64] * 4 and clamp["locals"][4] == "bool"
        assert clamp["blocks"][0] == ["block", "0", ["set", "4", ["cmp", "lt", ["local", "1"], ["local", "2"]]],
                                      ["switch", "4", "2", "1"]], clamp["blocks"][0]
        assert clamp["blocks"][1] == ["block", "1", ["set", "0", ["use", ["local", "2"]]], ["return"]]

        # The slice's length is a variable of its own, and the bounds check
        # compares the casts of the index and the length.
        s = debug["sum"]
        assert s["lengths"] == [["1", "14"]], s["lengths"]
        assert s["locals"][1] == "other"
        checks = list(forms(s["blocks"], "assert"))
        assert len(checks) == 1 and checks[0][:4] == ["assert", ["local", "6"], "index-out-of-bounds", "6"], checks
        assert ["set", "7", ["cast", ["local", "5"]]] in s["blocks"][4]
        assert ["set", "8", ["cast", ["local", "14"]]] in s["blocks"][4]

        # A check's span is where the interpreter reports it failing: the
        # bytes of the index, and of the statement whose `+` overflows.
        def text(at):
            return PROGRAM.encode()[int(at[1]):int(at[2])].decode()
        assert text(checks[0][4]) == "xs[i]", text(checks[0][4])
        steps = [x for x in s["blocks"][6] if x[0] == "set" and x[2][0] == "add"]
        assert [x[2] for x in steps] == [["add", ["local", "2"], ["local", "10"]],
                                         ["add", ["local", "3"], ["const", "1"]]], steps
        assert [text(x[3]) for x in steps] == ["s += xs[i]", "i += 1"], [text(x[3]) for x in steps]

        # A local lent to `inout` is not followed: its reads are opaque.
        e = debug["escapes"]
        assert e["locals"][2] == "other", e["locals"]
        assert ["set", "0", ["use", ["local", "5"]]] in e["blocks"][1]
        assert ["set", "5", ["use", "opaque"]] in e["blocks"][1], e["blocks"][1]

        # Ranges and constants are values, not bits.
        w = debug["widths"]
        assert w["locals"][1] == ["int", "0", "255"] and w["locals"][2] == ["int", "-2147483648", "2147483647"]
        assert ["const", "18446744073709551615"] in list(forms(w["blocks"], "const")), w["blocks"]

        # 128-bit ranges: 2^127 does not fit an i128, so they are not computed.
        assert debug["wide"]["locals"][1] == ["int", str(-(1 << 127)), str((1 << 127) - 1)], debug["wide"]["locals"]
        assert debug["wide"]["locals"][2] == ["int", "0", str((1 << 128) - 1)]

        # Without overflow checks `+` and `-` wrap, which is opaque, and only
        # the bounds check has a span.
        release = emit("--release")
        for name in ["sum", "widths"]:
            for head in ["add", "sub", "mul"]:
                assert not list(forms(release[name]["blocks"], head)), (name, head)
        assert len(list(forms(release["sum"]["blocks"], "at"))) == 1
    print("emit-obligations: structure, models and opaque values")


if __name__ == "__main__":
    main()
