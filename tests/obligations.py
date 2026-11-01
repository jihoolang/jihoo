#!/usr/bin/env python3
"""Check `emit-obligations` with an independent reader: its structure, the
model of known functions, and what it must not follow."""
import argparse
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]

PROGRAM = """
fn clamp(x: i64, lo: i64, hi: i64) -> i64
    requires lo <= hi
    ensures lo <= result && result <= hi
{
    if x < lo { return lo }
    if x > hi { return hi }
    x
}

fn sum(xs: [i64]) -> i64 {
    var s = 0
    var i = 0
    while i < xs.len
        invariant 0 <= i && i <= xs.len
    {
        s += xs[i]
        i += 1
    }
    s
}

fn bump(inout x: i64)
    requires x < 100
    ensures x == old(x) + 1
{
    x += 1
}

fn lends(n: i64) -> i64 {
    var x = n
    bump(&x)
    x
}

// `x` is lent on to `bump`; the pointer itself goes nowhere else.
fn passes(inout x: i64) {
    bump(&x)
}

fn escapes(inout x: i64) -> *i64 {
    &x
}

fn apart(x: i64) -> i64
    requires x < 0 || !(x <= 10)
{
    x
}

struct Span2
    invariant 0 <= self.lo && self.lo <= self.hi
{
    lo: i64
    hi: i64
}

fn width(s: Span2) -> i64 { s.hi - s.lo }

fn widen(inout s: Span2) {
    if s.hi < 1000 { s.hi += 1 }
    width(s)
}

fn widths(a: u8, b: i32) -> u64 {
    let big: u64 = 18446744073709551615
    big - a as u64 + b as u64
}

fn wide(x: i128, y: u128) -> i128 {
    x + y as i128
}

fn main() {
    var y = 1
    passes(&y)
    println(clamp(5, 0, 3) + sum([1, 2]) + lends(1) + y)
    println(wide(1, 2))
    println(widths(1, 2))
}
"""


REASONS = {"load", "field", "variant", "element", "escaped", "aggregate", "constant", "wrap",
           "bits", "bool", "div", "rem", "shift", "neg", "pointer", "tag", "length"}


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


CLAUSES = {"requires", "ensures", "invariant"}
HOLDS = {"holds-in", "holds-out"}


def check_compare(x, variables, where):
    assert x[0] in ["lt", "le", "gt", "ge", "eq", "ne"], where
    for side in x[1:]:
        assert side[0] in ["lin", "opaque"], where
        if side[0] == "lin":
            int(side[1])
            for v, k in side[2:]:
                assert 0 <= int(v) < variables, where
                int(k)


def check_fact(x, variables, where):
    """(op A B), or (or (and (op A B)...)... [(opaque escaped)])."""
    if x[0] != "or":
        check_compare(x, variables, where)
        return
    assert len(x) >= 2, where
    for alt in x[1:]:
        if alt[0] == "opaque":
            continue
        assert alt[0] == "and" and len(alt) >= 2, where
        for c in alt[1:]:
            check_compare(c, variables, where)


def check_holds(h, variables, where):
    """(TYPE FACT): a type's invariant at a place."""
    assert len(h) == 2, where
    int(h[0])
    check_fact(h[1], variables, where)


def functions(text):
    out = {}
    for f in parse(text):
        assert f[0] == "function" and len(f) >= 10, f[:3]
        name, symbol, args, locals_, lengths, derefs, fields, entries = f[1:9]
        assert isinstance(name, str) and isinstance(symbol, str)
        assert args[0] == "args" and locals_[0] == "locals" and lengths[0] == "lengths"
        assert derefs[0] == "derefs" and fields[0] == "fields" and entries[0] == "entries"
        variables = len(locals_) - 1
        # (VAR LOCAL [*] FIELD...): an integer field, through the local's borrow with `*`.
        for x in fields[1:]:
            assert int(x[1]) < variables and len(x) >= 3, (name, x)
            assert locals_[1 + int(x[0])][0] == "int", (name, x)
            [int(k) for k in x[2 + (x[2] == "*"):]]
        clauses = [x for x in f[9:] if x[0] in CLAUSES]
        holds = [x for x in f[9 + len(clauses):] if x[0] in HOLDS]
        blocks = f[9 + len(clauses) + len(holds):]
        # (holds-in (TYPE FACT)...), (holds-out ...): types' invariants.
        for h in holds:
            assert len(h) >= 2, (name, h)
            for x in h[1:]:
                check_holds(x, variables, (name, h))
        for c in clauses:
            # (requires (op A B) (at lo hi)); (invariant BLOCK (op A B) (at lo hi));
            # with `||`, (or (and (op A B)...)...) in place of (op A B).
            body = c[2:] if c[0] == "invariant" else c[1:]
            assert len(body) == 2 and body[1][0] == "at", (name, c)
            if body[0][0] == "or":
                assert len(body[0]) >= 3, (name, c)
            check_fact(body[0], variables, (name, c))
        for i, b in enumerate(blocks):
            assert b[0] == "block" and b[1] == str(i), (name, b[:2])
            for s in b[2:-1]:
                # (check (TYPE FACT) (at lo hi)): a destructor's invariant, in a writer.
                if s[0] == "check":
                    assert len(s) == 3 and s[2][0] == "at", (name, s)
                    check_holds(s[1], variables, (name, s))
                    continue
                assert s[0] == "set" and int(s[1]) < variables, (name, s)
                assert len(s) == 3 or (len(s) == 4 and s[3][0] == "at"), (name, s)
            term = b[-1]
            targets = {"goto": term[1:], "switch": term[2:], "any": term[1:],
                       "assert": term[3:4], "call": term[2:3]}.get(term[0], [])
            if term[0] == "assert":
                assert len(term) == 5 and term[4][0] == "at", (name, term)
            if term[0] == "call":
                optional = ("changes", "never", "fields", "before", "after")
                parts = [p[0] for p in term[3:] if p[0] not in optional]
                assert parts in [["fn", "args", "at"], ["args", "at"]], (name, term)
                for p in term[3:]:
                    if p[0] == "changes":
                        assert all(int(v) < variables for v in p[1:]), (name, term)
                    if p[0] in ("before", "after"):
                        for x in p[1:]:
                            check_holds(x, variables, (name, term))
            assert term[0] in ["goto", "switch", "any", "assert", "call", "trap", "return",
                               "unreachable"], (name, term)
            for t in targets:
                assert int(t) < len(blocks), (name, term)
        for pair in lengths[1:]:
            assert locals_[1 + int(pair[1])] == ["int", "0", "9223372036854775807"]
        for v, e in entries[1:]:
            assert locals_[1 + int(v)] == locals_[1 + int(e)], (name, v, e)
        out[name] = {"locals": locals_[1:], "lengths": lengths[1:], "derefs": derefs[1:],
                     "fields": fields[1:], "entries": entries[1:], "clauses": clauses, "holds": holds,
                     "blocks": blocks}
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

        # A local lent to one call stays a variable, which the call changes.
        e = debug["lends"]
        assert e["locals"][2] == i64, e["locals"]
        calls = list(forms(e["blocks"], "call"))
        assert calls[0][3:5] == [["fn", "main.bump.3"], ["args", ["lent", "2"]]], calls
        assert ["set", "5", ["use", ["local", "2"]]] in e["blocks"][1], e["blocks"][1]

        # An `inout` integer is a variable when the pointer only reaches it,
        # even lent on to another call; an address taken is not followed.
        b = debug["bump"]
        assert b["derefs"] == [["1", "3"]] and b["entries"] == [["3", "4"]], (b["derefs"], b["entries"])
        assert ["set", "3", ["use", ["local", "2"]]] in b["blocks"][0], b["blocks"][0]
        p = debug["passes"]
        assert p["derefs"] == [["1", "4"]], p["derefs"]
        assert list(forms(p["blocks"], "call"))[0][4] == ["args", ["lent", "4"]]
        assert debug["escapes"]["derefs"] == [], debug["escapes"]["derefs"]

        # Contracts: `ensures` reads the parameters on entry and `result` as
        # local 0; `old(x)` is the entry value of `*x`; an invariant names
        # its loop head.
        c = clamp["clauses"]
        assert clamp["entries"] == [["1", "7"], ["2", "8"], ["3", "9"]], clamp["entries"]
        assert c[0][:2] == ["requires", ["le", ["lin", "0", ["2", "1"]], ["lin", "0", ["3", "1"]]]], c[0]
        assert c[1][:2] == ["ensures", ["le", ["lin", "0", ["8", "1"]], ["lin", "0", ["0", "1"]]]], c[1]
        assert text(c[1][2]) == "lo <= result", text(c[1][2])
        assert b["clauses"][1][1] == ["eq", ["lin", "0", ["3", "1"]], ["lin", "1", ["4", "1"]]], b["clauses"]
        assert [x[:2] for x in s["clauses"]] == [["invariant", "1"], ["invariant", "1"]], s["clauses"]
        assert s["clauses"][1][2] == ["le", ["lin", "0", ["3", "1"]], ["lin", "0", ["14", "1"]]]
        # `||` gives a conjunction per case; `!` negates the comparison.
        x, zero, ten = ["lin", "0", ["1", "1"]], ["lin", "0"], ["lin", "10"]
        a = debug["apart"]["clauses"][0][:2]
        assert a == ["requires", ["or", ["and", ["lt", x, zero]], ["and", ["gt", x, ten]]]], a

        # A type's invariant: assumed of a parameter's fields on entry, and
        # in a writer, proved on return and of what a call is given.
        w = debug["width"]
        assert [h[0] for h in w["holds"]] == ["holds-in"] and len(w["holds"][0]) == 3, w["holds"]
        widen = debug["widen"]
        assert [h[0] for h in widen["holds"]] == ["holds-in", "holds-out"], widen["holds"]
        calls = list(forms(widen["blocks"], "call"))
        assert any(p[0] == "before" for c in calls for p in c[3:]), calls

        # Every opaque value says why: a load through the slice's pointer.
        assert ["set", "10", ["use", ["opaque", "load"]]] in s["blocks"][6], s["blocks"][6]
        for name, f in debug.items():
            for o in forms(f["blocks"], "opaque"):
                assert len(o) == 2 and o[1] in REASONS, (name, o)

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
