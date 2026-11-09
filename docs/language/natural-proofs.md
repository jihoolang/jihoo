# Natural-index proof library

Marked modules can `import dependent.nat`. Its functions construct proof terms
from the existing dependent core's equality, order, subtraction, induction and
loop rules. The library adds no intrinsics, axioms or checker bypasses. Optional
[bounded proof automation](proof-automation.md) can compose explicitly supplied
lemma results; it does not search or instantiate the library automatically.
The source is [lib/dependent/nat.jh](../../lib/dependent/nat.jh).

## Equality and bounds

Indices denote natural numbers. `Lt(a, b + 1)` expresses `a <= b`.
Arguments named as evidence below are explicitly erased in the API.

| Function | Evidence supplied | Result |
| --- | --- | --- |
| `eq_sym(a, b, p)` | `Eq(a, b)` | `Eq(b, a)` |
| `eq_trans(a, b, c, p, q)` | `Eq(a, b)`, `Eq(b, c)` | `Eq(a, c)` |
| `eq_congr(f, a, b, p)` | `f: fn(u64) -> u64`, `Eq(a, b)` | `Eq(f(a), f(b))` |
| `eq_add(a, b, k, p)` | `Eq(a, b)` | `Eq(a + k, b + k)` |
| `rewrite_upper(i, n, m, e, p)` | `Eq(n, m)`, `Lt(i, n)` | `Lt(i, m)` |
| `rewrite_lower(i, j, n, e, p)` | `Eq(i, j)`, `Lt(i, n)` | `Lt(j, n)` |
| `le_refl(a)` | none | `Lt(a, a + 1)` |
| `weaken(a, b, p)` | `Lt(a, b)` | `Lt(a, b + 1)` |
| `lt_trans(a, b, c, p, q)` | `Lt(a, b)`, `Lt(b, c)` | `Lt(a, c)` |
| `le_trans(a, b, c, p, q)` | `Lt(a, b + 1)`, `Lt(b, c + 1)` | `Lt(a, c + 1)` |
| `le_lt(a, b, c, p, q)` | `Lt(a, b + 1)`, `Lt(b, c)` | `Lt(a, c)` |
| `lt_irrefl(a, p)` | contradictory `Lt(a, a)` | `Lt(0, 0)`, usable with `absurd` |
| `add_le(a, k)` | none | `Lt(a, a + k + 1)` |
| `sub_cancel(n, k, p)` | `Lt(k, n + 1)` | `Eq(sub(n, k, p) + k, n)` |
| `sub_le(n, k, p)` | `Lt(k, n + 1)` | `Lt(sub(n, k, p), n + 1)` |
| `mirror_lt(i, n, p)` | `Lt(i, n)` | `Lt(sub(n, i + 1, lt_add(i, n, 1, p)), n)` |

`dependent.vec` uses the common symmetry and weakening lemmas. Its existing
`vec.eq_sym` interface remains available.

## Finite nondecreasing traces

`Steps(a, b)` is an inductive proposition that records a finite succession of
increments from `a` to `b`, allowing concatenation. It has three constructors:

- `stationary(a)` proves `Steps(a, a)`.
- `successor(a, b, p)` takes `p: Steps(a, b)` and proves `Steps(a, b + 1)`.
- `concatenate(a, b, c, p, q)` joins `Steps(a, b)` and `Steps(b, c)`.

`steps_bound(a, b, p)` proves `Lt(a, b + 1)` by structural induction. Its
concatenation case uses both induction hypotheses. `steps_add(a, b, k, p)`
translates a trace to `Steps(a + k, b + k)`, also by structural induction.
`advance(a, n)` constructs `Steps(a, a + n)` using a proof-producing loop with
invariant `Steps(a, a + iteration)`. `steps_lt(a, b, n, p, q)` combines a trace
with `q: Lt(b, n)` to prove `Lt(a, n)`.

[The complete example](../../examples/core_nat.jh) maintains
`refine(fn(c) { Steps(c, iteration) })` as the accumulator of a runtime counting
loop. An increment uses `steps_add`; a skipped increment uses `successor`.
After the loop, imported `steps_bound` supplies the evidence for a table access.
The example returns `30`. Its trace constructors and induction proofs are erased;
the runtime code is identical to an independently written loop whose invariant
uses primitive order evidence directly.

## Boundaries

Arithmetic inside evidence has the core's ghost natural-number meaning. A proof
of `Lt(a, a + k + 1)` does not authorize wrapping runtime addition: evaluating
`a + k` as a `u64` still traps on overflow. The tests pass maximal u64 values to
an erased symbolic trace without introducing runtime proof loops, and separately
check that actual overflowing additions trap at O0 and O2.

Every function and every induction case is checked, including unused imported
lemmas. Invalid evidence is not accepted by release, no-verify or no-elab flags.
Ordinary checking and normalization resource limits still apply; this library
does not establish universal normalization or completeness of proof checking.

These are proofs accepted by the current native core, whose full soundness and
source/lowering correspondence are not mechanically proved. The independent
Lean model does not automatically certify this library. Runtime/MIR comparisons
and rejection tests are regression evidence, not a general erasure theorem.
Specifications here are dependent types and loop invariants; marked modules still
do not support the ordinary frontend's `requires`/`ensures` syntax.
