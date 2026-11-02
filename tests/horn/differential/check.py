"""Differential test of `jihoo emit-horn` against the code it translates.

check.py RULES CASES

RULES is what `jihoo emit-horn --lib compiler/linear.jh --fn check` writes;
CASES is what cases.jh prints: inputs to compiler/linear.jh's functions with
what the compiled code returned. For each case this file asks the rules, read
as a logic program (independently of lib/proof and of the compiler), which
results they derive for those inputs, and fails unless:

* the code's result is among them: when `check` returns `Ok`, the rules derive
  it, which is what lib/proof/refine.jh's theorem needs of the translation
  (and of std's `Vec` being the rules' lists);
* when the code returns a value, it is the only one the rules derive besides
  the overflow results (`None`, an error), which an exact model in Python
  checks too;
* a result the rules derive and the code does not is one exact arithmetic
  allows: the rules' `add` and `mul` are exact and may also say `None`, so
  they derive `Ok` where an i128 overflowed, and only there.

The rules are solved top-down, premises in order, with integers as Python's
and every solution enumerated.
"""

import sys
import threading
import time

ARITH = {"z0", "z1", "add", "mul", "neg"}
LO, HI = -(1 << 127), (1 << 127) - 1


def parse(text):
    out, stack, tok = [], [[]], ""
    i = 0
    while i < len(text):
        ch = text[i]
        if ch == ";":
            while i < len(text) and text[i] != "\n":
                i += 1
            continue
        if ch in "() \t\r\n":
            if tok:
                stack[-1].append(tok)
                tok = ""
            if ch == "(":
                stack.append([])
            elif ch == ")":
                done = stack.pop()
                stack[-1].append(done)
        else:
            tok += ch
        i += 1
    if tok:
        stack[-1].append(tok)
    out = stack[0]
    return out


class Var:
    __slots__ = ("ref",)

    def __init__(self):
        self.ref = None


class NonGround(Exception):
    pass


def deref(t):
    while isinstance(t, Var) and t.ref is not None:
        t = t.ref
    return t


def is_arith(t):
    return isinstance(t, int) or t in ("z0", "z1") or (isinstance(t, tuple) and t[0] in ARITH)


def value(t):
    """The integer an arithmetic term denotes, or None if a variable is unbound."""
    t = deref(t)
    if isinstance(t, int):
        return t
    if t == "z0":
        return 0
    if t == "z1":
        return 1
    if isinstance(t, Var):
        return None
    if isinstance(t, tuple) and t[0] in ARITH:
        vs = [value(a) for a in t[1]]
        if any(v is None for v in vs):
            return None
        if t[0] == "add":
            return vs[0] + vs[1]
        if t[0] == "mul":
            return vs[0] * vs[1]
        return -vs[0]
    raise ValueError("not an integer: %r" % (t,))


def build(p, m):
    if isinstance(p, str):
        if p.startswith("?"):
            if p not in m:
                m[p] = Var()
            return m[p]
        if p.lstrip("-").isdigit():
            return int(p)
        return p
    return (p[0], tuple(build(a, m) for a in p[1:]))


def ground(t):
    t = deref(t)
    if is_arith(t):
        v = value(t)
        if v is None:
            raise NonGround(repr(t))
        return v
    if isinstance(t, Var):
        raise NonGround("unbound result")
    if isinstance(t, str):
        return t
    return (t[0], tuple(ground(a) for a in t[1]))


def occurs(v, t):
    t = deref(t)
    if t is v:
        return True
    return isinstance(t, tuple) and any(occurs(v, a) for a in t[1])


def bind(v, t, trail):
    t = deref(t)
    if is_arith(t):
        n = value(t)
        if n is not None:
            t = n
    # No cyclic terms: a list that is its own tail would make the search
    # endless.
    if occurs(v, t):
        return False
    v.ref = t
    trail.append(v)
    return True


def solve_linear(e, n, trail):
    """Bind the one unbound variable of e so that e = n, for e of the shapes the
    rules use (sums and differences with constants)."""
    e = deref(e)
    if isinstance(e, Var):
        return bind(e, n, trail)
    if isinstance(e, tuple) and e[0] == "add":
        a, b = e[1]
        va, vb = value(a), value(b)
        if va is None and vb is not None:
            return solve_linear(a, n - vb, trail)
        if vb is None and va is not None:
            return solve_linear(b, n - va, trail)
    if isinstance(e, tuple) and e[0] == "neg":
        return solve_linear(e[1][0], -n, trail)
    raise NonGround("cannot solve %r = %d" % (e, n))


def unify(a, b, trail):
    a, b = deref(a), deref(b)
    if a is b:
        return True
    if isinstance(a, Var):
        return bind(a, b, trail)
    if isinstance(b, Var):
        return bind(b, a, trail)
    if is_arith(a) or is_arith(b):
        if not (is_arith(a) and is_arith(b)):
            return False
        va, vb = value(a), value(b)
        if va is not None and vb is not None:
            return va == vb
        if va is not None:
            return solve_linear(b, va, trail)
        if vb is not None:
            return solve_linear(a, vb, trail)
        raise NonGround("%r = %r" % (a, b))
    if isinstance(a, str) or isinstance(b, str):
        return a == b
    if a[0] != b[0] or len(a[1]) != len(b[1]):
        return False
    return all(unify(x, y, trail) for x, y in zip(a[1], b[1]))


def undo(trail, mark):
    while len(trail) > mark:
        trail.pop().ref = None


class Budget(Exception):
    pass


# Resolution steps and seconds per query: a translation that leaves a result
# unbound can make the search endless (and each step slower, as unbound
# lists grow), which is a failure too.
STEPS = 200_000
SECONDS = 10


class Rules:
    def __init__(self, text):
        self.steps = 0
        self.deadline = 0.0
        self.by_pred = {}
        for form in parse(text):
            if form and form[0] == "rule":
                self.by_pred.setdefault(form[3][0], []).append((form[1], form[2], form[3]))

    def solve(self, goals, trail):
        if not goals:
            yield
            return
        self.steps += 1
        if self.steps > STEPS or (self.steps % 1000 == 0 and time.monotonic() > self.deadline):
            raise Budget()
        g, rest = deref(goals[0]), goals[1:]
        head, args = g[0], g[1]
        if head in ("eq", "le"):
            a, b = args
            va, vb = value(a), value(b)
            mark = len(trail)
            if head == "eq" and (va is None or vb is None):
                if unify(a, b, trail):
                    yield from self.solve(rest, trail)
                undo(trail, mark)
                return
            if va is None or vb is None:
                raise NonGround("le %r %r" % (a, b))
            if (va == vb) if head == "eq" else (va <= vb):
                yield from self.solve(rest, trail)
            return
        for name, prems, concl in self.by_pred.get(head, []):
            m = {}
            c = build(concl, m)
            mark = len(trail)
            if unify(g, c, trail):
                yield from self.solve([build(p, m) for p in prems] + rest, trail)
            undo(trail, mark)

    def results(self, pred, inputs):
        """Every result the rules derive for pred(inputs..., result)."""
        self.steps = 0
        self.deadline = time.monotonic() + SECONDS
        r = Var()
        trail = []
        out = set()
        for _ in self.solve([(pred, tuple(inputs) + (r,))], trail):
            out.add(ground(r))
        return out


# Values as the rules' terms.

def lst(sort, elems):
    t = sort + ".nil"
    for e in reversed(elems):
        t = (sort + ".cons", (e, t))
    return t


def lin(f):
    terms, c = f
    return ("Lin.mk", (lst("Vec<<i64,i128>>", [("Tup<Z,Z>.mk", (int(v), int(k))) for v, k in terms]), int(c)))


SOME_LIN, NONE_LIN = "Option<Lin>.Some", "Option<Lin>.None"
SOME_INT, NONE_INT = "Option<i128>.Some", "Option<i128>.None"
OK, ERR = "Result<i64,str>.Ok", ("Result<i64,str>.Err", ("Str.s",))


# An exact model of add_scaled: the result, and whether a number left i128.

def exact_scaled(a, b, w):
    over = False

    def fit(n):
        nonlocal over
        if not LO <= n <= HI:
            over = True
        return n

    ta, tb = [(int(v), int(k)) for v, k in a[0]], [(int(v), int(k)) for v, k in b[0]]
    out, i, j = [], 0, 0
    while i < len(ta) or j < len(tb):
        if j == len(tb) or (i < len(ta) and ta[i][0] < tb[j][0]):
            v, k = ta[i]
            i += 1
        else:
            p = fit(tb[j][1] * w)
            if i == len(ta) or tb[j][0] < ta[i][0]:
                v, k = tb[j][0], p
            else:
                v, k = ta[i][0], fit(ta[i][1] + p)
                i += 1
            j += 1
        if k != 0:
            out.append((v, k))
    c = fit(int(a[1]) + fit(int(b[1]) * w))
    return (out, c), over


def check_cases(rules, cases):
    counts = {"check": 0, "ok": 0, "add_scaled": 0, "add": 0, "mul": 0, "exact-only": 0}
    failures = []
    for case in cases:
        kind = case[0]
        counts[kind] += 1
        try:
            if kind == "check":
                facts, claim, ws, res = case[1], case[2], case[3], case[4]
                goal = ("Goal.mk", (lst("Vec<Lin>", [lin(f) for f in facts]), lin(claim)))
                cert = ("Certificate.mk", (lst("Vec<i128>", [int(w) for w in ws]),))
                got = rules.results("fn.check", [goal, cert])
                oks = {g for g in got if g != ERR}
                big = any(abs(int(x)) >= 1 << 60 for x in flatten(case[1:4]))
                if res[0] == "ok":
                    counts["ok"] += 1
                    want = (OK, (int(res[1]),))
                    if oks != {want}:
                        failures.append(("check returned Ok %s; the rules derive %s" % (res[1], sorted(map(str, oks))), case))
                else:
                    if ERR not in got:
                        failures.append(("check returned Err; the rules do not derive it", case))
                    if oks:
                        if big:
                            counts["exact-only"] += 1
                        else:
                            failures.append(("check returned Err; the rules also derive %s" % oks, case))
            elif kind == "add_scaled":
                a, b, w, res = case[1], case[2], int(case[3]), case[4]
                got = rules.results("fn.Lin.add_scaled", [lin(a), lin(b), w])
                somes = {g for g in got if g[0] == SOME_LIN}
                model, over = exact_scaled(a, b, w)
                if res[0] == "some":
                    want = (SOME_LIN, (lin(res[1]),))
                    if over or lin(model) != lin(res[1]):
                        failures.append(("add_scaled disagrees with the exact model", case))
                    if somes != {want}:
                        failures.append(("add_scaled returned Some; the rules derive %s" % somes, case))
                else:
                    if NONE_LIN not in got:
                        failures.append(("add_scaled returned None; the rules do not derive it", case))
                    if not over:
                        failures.append(("add_scaled returned None without an overflow", case))
                    if somes - {(SOME_LIN, (lin(model),))}:
                        failures.append(("the rules derive a sum the exact model does not", case))
                    if somes:
                        counts["exact-only"] += 1
            else:
                a, b, res = int(case[1]), int(case[2]), case[3]
                got = rules.results("fn." + kind, [a, b])
                exact = a + b if kind == "add" else a * b
                if res[0] == "some":
                    if int(res[1]) != exact or (SOME_INT, (exact,)) not in got:
                        failures.append(("%s returned Some %s" % (kind, res[1]), case))
                else:
                    if NONE_INT not in got or LO <= exact <= HI:
                        failures.append(("%s returned None" % kind, case))
                if {g for g in got if g[0] == SOME_INT} != {(SOME_INT, (exact,))}:
                    failures.append(("%s: the rules derive %s" % (kind, got), case))
        except NonGround as e:
            failures.append(("the rules could not be solved: %s" % e, case))
        except RecursionError:
            failures.append(("the search went too deep", case))
        except Budget:
            failures.append(("the search took more than %d steps or %d s" % (STEPS, SECONDS), case))
            break  # the rest would take as long
    return counts, failures


def flatten(x):
    if isinstance(x, list):
        for y in x:
            yield from flatten(y)
    else:
        yield x


def main():
    if len(sys.argv) != 3:
        print(__doc__.splitlines()[2])
        return 2
    with open(sys.argv[1]) as f:
        rules = Rules(f.read())
    with open(sys.argv[2]) as f:
        cases = parse(f.read())
    counts, failures = check_cases(rules, cases)
    for msg, case in failures[:10]:
        print("FAIL:", msg)
        print("   ", show(case)[:2000])
    print(
        "differential: %d check cases (%d accepted), %d add_scaled, %d add, %d mul; "
        "%d where only exact arithmetic gives a result; %d failures"
        % (counts["check"], counts["ok"], counts["add_scaled"], counts["add"], counts["mul"],
           counts["exact-only"], len(failures))
    )
    return 1 if failures or counts["ok"] == 0 else 0


def show(x):
    return "(" + " ".join(show(y) for y in x) + ")" if isinstance(x, list) else x


if __name__ == "__main__":
    sys.setrecursionlimit(1_000_000)
    threading.stack_size(1 << 29)
    status = []
    t = threading.Thread(target=lambda: status.append(main()))
    t.start()
    t.join()
    sys.exit(status[0] if status else 1)
