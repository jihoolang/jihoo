# Proof-bounded buffer ranges

`import dependent.range` provides an owned snapshot of a contiguous range of
an i64 buffer. It borrows the source and allocates a separate result with exactly
the requested number of elements. This is an explicit copy, not a zero-copy
slice or a stored borrowing view.

```jihoo
#![dependent_core]
import dependent.range

fn main() -> i64 {
    let source = alloc(4, 17)
    let copied: buffer(2) = range.copy(4, source, 1, 2, decide_lt(3, 5))
    index(copied, 1, decide_lt(1, 2))
}
```

The program returns `17`. The source remains usable; modifying or freeing it
after the copy does not change the snapshot. Both buffers are automatically
freed when their owners leave scope.

## Range bounds

`range.copy(n, source, offset, count, fits)` requires:

- `source: ref buffer(n)`.
- `fits: erased(Lt(offset + count, n + 1))`, expressing `offset + count <= n`.

It returns `buffer(count)`, so subsequent reads need only `i < count`.
The endpoint may equal `n`, and an empty range at `offset == n` is valid.
Empty ranges still produce an owned empty buffer; the implementation currently
allocates its buffer header. The source's length `n` and `fits` are erased.
`offset` and `count` are runtime values.

The reusable theorem `range.offset_lt(n, offset, count, i, fits, inside)`
translates `inside: erased(Lt(i, count))` into `Lt(offset + i, n)`. Its proof
uses existing addition and transitivity rules. The copying loop applies this
imported library evidence to every read and carries the result buffer as its
owned accumulator. Source reads and destination writes need no additional
runtime bounds checks.

## Runtime-selected ranges

The [complete example](../../examples/core_range.jh) checks `offset <= n`,
then `count <= n - offset`, before copying. The second check avoids computing
`offset + count` as a runtime endpoint. Its bound is still stated using that
sum in erased evidence. The example sums the resulting snapshot through a
borrowing helper and returns `-1` for an invalid range.

The example's checks use `n + 1` and `n - offset + 1`; these runtime additions
can trap at maximal u64. Erased evidence does not change runtime overflow rules.
Likewise, buffer allocation checks the byte size and allocation result, and the
example's signed sum can overflow. The API proves index bounds, not successful
allocation, trap-freedom or a general totality theorem.

For an already proved range, `copy` allocates once and copies `count` elements
in increasing index order. It does not traverse elements outside the selected
range. The current primitive allocation initializes the destination before the
copy overwrites it, so this is not a promise of a single memory-write pass.
`offset + i` retains normal checked runtime arithmetic. The range proof implies
that each selected index fits the source length; it does not disable those
arithmetic checks in the generated code.

## Validation and limits

[The regression suite](../../tests/core_range.py) compares exact MIR with a
separate implementation using primitive proofs and checks that an imported ghost
endpoint theorem erases even when its runtime input is maximal u64. Both object
targets and native O0/O2 tests cover empty, full, endpoint and invalid ranges,
element order, signed extremes, source retention, independent mutation, source
release, allocation cleanup, and runtime traps. Invalid ownership, bounds and
result lengths are rejected, including malformed unused imported library code
with verification and elaboration bypass flags enabled.

These are checked native-core library proofs and finite regression tests, not
Lean certification or a mechanized compiler-soundness theorem. The element type
is i64. There is no borrowed slice record, mutable subrange view, generic element
type or formal theorem equating every copied element to its source value.

## Reusing storage and moving overlapping ranges

`copy_into(n, source, m, destination, from, to, count, source_fits, destination_fits)`
borrows `source: ref buffer(n)` and consumes `destination: buffer(m)`, returning
that destination owner with the same length. Evidence states
`from + count <= n` and `to + count <= m` using `Lt(endpoint, length + 1)`.
The loop copies exactly the selected elements in increasing order, without
allocating a snapshot or replacing the destination buffer. The source stays
available; cells outside the destination range are unchanged. Source and
destination must be distinct owners. Passing the same owner twice is rejected.

`move_within(n, target, from, to, count, source_fits, destination_fits)` handles
overlap within one buffer. It consumes and returns `buffer(n)`. When `from < to`,
it reads and writes from the last selected element backwards; otherwise it walks
forwards. Each step threads the single owner through `load` then `store`. This
has memmove-style snapshot semantics without allocating a snapshot. Equal
ranges and empty ranges are permitted, including empty ranges at the endpoint.
There are no per-element bounds tests; the runtime direction comparison remains.

`subrange_fits(n, offset, count, start, length, outer, inner)` composes evidence
for a range within a range. Its conclusion is
`Lt(offset + start + length, n + 1)`. All endpoint arithmetic in this theorem is
erased mathematical arithmetic, so even an overflowing runtime equivalent does
not execute. The transfer loops still retain checked runtime offset arithmetic.

The [transfer example](../../examples/core_range_transfer.jh) uses this imported
lemma to copy into existing storage, then moves an overlapping range. Its result
is 28. The [transfer tests](../../tests/core_range_transfer.py) compare both
operations with an independent snapshot model for every offset/count combination
around six-element buffers, at O0/O2. They cover both object targets, empty
buffers, signed extremes, source retention, exact O0 allocation counts and
balanced frees, erased endpoint evidence, invalid ownership and malformed unused
imported bounds. Counts are not a substitute for a memory-sanitizer proof.

These APIs prove bounds and preserve the buffer's indexed length. Their
pointwise content behavior and overlap order are regression-tested, not an
additional formal content theorem. They do not add a borrowed slice type,
mutable subrange view, generic elements, allocation guarantees or Lean proofs.
