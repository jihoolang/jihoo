# Bounded proof automation

In a `#![dependent_core]` module, `auto()` constructs an ordinary proof of an
expected natural-index `Eq(a, b)` or `Lt(a, b)` proposition. The elaborator
checks the generated term against the original goal with the existing kernel.
There is no new axiom, inference rule, trusted solver result or runtime check.

```jihoo
#![dependent_core]

fn read(n: u64, i: u64, data: ref buffer(n + 1), p: erased(Lt(i, n))) -> i64 {
    index(data, i, auto())
}

fn same(a: u64, b: u64, c: u64, p: erased(Eq(a, b)), q: erased(Eq(b, c))) -> Eq(a, c) {
    auto()
}
```

The expected goal can come from a proof result, an annotated binding, an erased
function argument or a dependent field. The evidence positions of `index`,
`sub`, `pack`, `store` and `load` also supply their expected goals. Evidence
arguments remain explicit: write `auto()` where the proof belongs. An untyped
`let p = auto()` has no goal and is rejected.

## Facts and supported reasoning

Search uses visible local equality/order evidence and up to eight explicit
hints, such as `auto(p, nat.steps_bound(a, b, trace))`. Hint expressions are
checked even when the goal is otherwise trivial. Hints must prove `Eq` or `Lt`;
a user-defined inductive proposition must first be eliminated by an explicit
lemma. Discarded or shadowed bindings are not implicitly recovered.

The bounded strategy tries definitional equality and direct facts, true closed
inequalities, positivity/successor bounds, matching additive offsets and their
cancellation, equality rewrites of complete endpoints, and short order chains.
`Lt(a, b + 1)` is the existing encoding of `a <= b`. Additive matching uses a
finite multiset of terms and natural constants; equality is still decided by
the existing conversion checker. Equality rewrites can compose and reverse
facts, but do not search arbitrary subexpressions or instantiate global lemmas.

The [acceptance example](../../examples/core_auto.jh) obtains a trace from the
imported proof-producing loop `nat.advance`, applies the imported inductive
lemma `nat.steps_bound`, and supplies that evidence to a checked buffer read.
Both the library evidence and generated proof are erased. This is a native-core
postcondition/precondition workflow, not ordinary `ensures` syntax or automatic
induction.

## Limits and compatibility

Search is deterministic and incomplete. It accepts at most 32 facts in total,
uses at most 256 goal visits and six recursive search levels, and stops when
its generated node growth exceeds 4096. Individual bounded sum operations may
construct intermediate nodes before that growth check. Sum matching expands at
most 32 atoms, with its own depth bound and explicit occurrence fuel (including
interior and zero nodes): 128 visits for predecessor discovery and 256 for an
offset difference. Existing kernel nesting, work and term
limits still apply and are never reset or increased by search.

An unsupported goal or an unsuccessful search is a source error. Search-depth,
work or node-growth exhaustion reports a search-limit error. Supply a more
specific checked lemma/hint or write the proof explicitly. This is not a
complete arithmetic solver, an induction tactic, proof search over owned data,
or a new mechanized soundness result.

Arithmetic in proofs is ghost arithmetic over naturals. An erased overflowing
index can be valid; using the same addition at runtime still traps on overflow.
Automation does not justify skipping runtime effects or ownership checks.

`auto` is not a newly reserved identifier. Existing module declarations,
including forward or recursive references, and local bindings named `auto`
retain their previous name-resolution behavior. In such a scope, `auto(...)`
is the ordinary call, not automation. Qualified function calls are unchanged.
