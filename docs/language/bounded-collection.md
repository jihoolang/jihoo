# Runtime-selected collections

`import dependent.collect` constructs an owned i64 sequence whose length is
decided at runtime but proved not to exceed the number of candidates. This is
useful when some candidates are skipped, so a fixed `Sized(n)` result would be
incorrect.

`build(n, f)` invokes a callback of type
`fn(i: u64, erased(Lt(i, n))) -> collect.Entry`. Each callback returns either
`Entry.Keep(value)` or `Entry.Skip`. The result is `Bounded(n)`, a private record
containing a runtime count, a `Sized(count)` payload and erased evidence of
`count <= n`. The stored count is the exact payload length, not merely a bound.

## Using the proved output bound

The [complete example](../../examples/core_collect.jh) selects among four
candidates using a runtime cutoff. The resulting count can index a five-element
array without another bound check:

```jihoo
#![dependent_core]
import dependent.collect

fn main() -> i64 {
    let xs = collect.build(4, fn(i, p) {
        if_lt(i, 3, fn(q) { collect.Entry.Keep(7) }, collect.Entry.Skip)
    })
    index([10, 20, 30, 40, 50], collect.len(4, xs), collect.bound(4, xs))
}
```

This returns `40`. The proof is about the computed count, not a guessed number
of accepted elements. `bound(n, xs)` supplies `Lt(len(n, xs), n + 1)` from the
private invariant. It is erased and does not traverse the list.

## The construction invariant

After processing `k` candidates, the loop owns `Bounded(k)`. The empty value
contains `Sized(0)` and evidence that `0 <= 0`. A kept element increments the
stored count, uses `sized_list.cons` to preserve the exact payload length, and
adds one to both sides of the upper bound. A skipped element transfers the
unchanged payload and weakens the bound with the imported natural-number lemma.
The loop therefore returns `Bounded(n)` even though the number kept is dynamic.

The imported `nat.mirror_lt` theorem gives the callback its index evidence.
Callbacks run from index `n - 1` down to `0`, and kept values appear in
ascending-index order. Every candidate is visited exactly once on a successful
run, including skipped candidates. With zero candidates no callback runs.
Effects and traps in a callback are not erased when it returns `Skip` or when
only the final count is used. This API does not promise callback totality.

## API and ownership

- `empty() -> Bounded(0)` creates an empty collection.
- `build(n, f) -> Bounded(n)` constructs a runtime-selected collection.
- `len(n, xs) -> u64` borrows the result and reads its stored count in constant
  time; it does not traverse the payload.
- `bound(n, xs) -> Lt(len(n, xs), n + 1)` exposes the erased upper-bound proof.
- `nth(n, xs, i, p)` requires `p: erased(Lt(i, len(n, xs)))` and reads the
  selected element. The input bound `i < n` alone is insufficient, since some
  candidates may have been skipped. Reading still traverses the selected prefix.
- `to_vec(n, xs)` borrows the collection and copies kept values to an independent
  vector with length and capacity equal to the stored count.
- `to_vec_length(n, xs)` supplies an erased equality for that conversion. See
  [buffer materialization](list-buffer-transfer.md).
- `into_list(n, xs)` consumes the wrapper and returns the owned list, losing the
  public length/bound interface.

All `n` arguments except `build`'s iteration count are erased. The record fields
are private, so callers cannot forge either the stored count or its evidence.
Callbacks can borrow a source buffer; kept scalar values are copied into
independent list nodes. The source may be modified or freed after construction
without changing the result. An owned capture that would be repeatedly consumed
is rejected.

When checking a dynamic `nth` index, a helper taking `xs: ref Bounded(n)` keeps
the count observation and evidence in the same borrowing scope. The regression
suite includes this pattern. Ordinary owner and borrow restrictions still apply.

## Costs, validation and limits

The stored count is a runtime field. Indices and evidence are erased, but the
collection and exact-length wrappers are real allocations. The current O0 model
allocates three initial nodes and three more per kept element: a list node, a
`Sized` wrapper and a `Bounded` wrapper. Replaced wrappers are freed. A skip
transfers the unchanged runtime representation and adds no allocation; ghost
weakening does not force a replacement wrapper. Callback allocations are extra.
Optimizations may remove allocations, so these counts describe the tested
implementation rather than an ABI guarantee.

[The tests](../../tests/core_collect.py) compare exact MIR to an independently
written unindexed representation. Both object targets and native O0/O2 models
cover none/some/all selection, order, count-bounded reads, signed extremes,
callback traces and traps, independent storage, released sources and balanced
allocations/frees. Wrong callback bounds, forged access bounds, private-field
access and repeated owners are rejected. Mutated unused imported definitions
are checked with exact diagnostics, positive object controls and no invalid
output artifacts even under release/no-verify/no-elab flags.

This proves cardinality and access bounds, not a pointwise membership theorem,
callback termination, arbitrary element types or compiler soundness. Runtime
arithmetic and allocation retain their normal traps. The feature is a typed
loop invariant using imported library proofs, not ordinary `ensures` syntax.
