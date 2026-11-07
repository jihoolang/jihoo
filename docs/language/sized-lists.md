# Lists with exact lengths

`import dependent.sized_list` provides `Sized(n)`: an owned i64 list whose
exact length is an erased `u64` index. The record privately owns a
`dependent.list.List` and erased evidence equating its borrowed length to `n`.
The implementation is [lib/dependent/sized_list.jh](../../lib/dependent/sized_list.jh).
Callers cannot construct the record or extract its private fields directly.

## Building a checked loop result

`repeat(n, value)` returns `Sized(n)`. Its runtime loop has accumulator type
`Sized(k)` after `k` iterations. `empty()` supplies `Sized(0)`, and
`cons(k, value, acc)` consumes `Sized(k)` and returns `Sized(k + 1)`:

```jihoo
fold(n, fn(k) { Sized(k) }, empty(), fn(i, p, acc) { cons(i, x, acc) })
```

The core checks the initial value and the step at their indexed types. A wrong
initial index, an unchanged step accumulator or incorrect length evidence is
rejected even when the function is unused. The returned type carries the loop's
exact-length postcondition. This uses dependent types, not the ordinary
frontend's `ensures` syntax.

## Reading and mapping

```jihoo
#![dependent_core]
import dependent.sized_list

fn increment(x: i64) -> i64 { x + 1 }

fn main() -> i64 {
    let xs = sized_list.repeat(3, 17)
    let ys = sized_list.map(3, xs, increment)
    sized_list.nth(3, ys, 2, decide_lt(2, 3))
}
```

This returns `18`. The caller's bound is about `3`, the index in `Sized(3)`;
it does not need to traverse the list to discover its length. `map` borrows the
input, produces an independently owned result at the same index, and checks its
evidence using imported structural `list.map_borrowed_length`. As with
[list.map](list-proofs.md#map-evaluation-order), callbacks run tail-to-head,
element order is preserved, and runtime overflow or allocation failure can trap.
The length theorem does not promise callback termination or trap-freedom.

The [complete example](../../examples/core_sized_list.jh) takes a runtime `n`,
builds and maps `Sized(n)`, and checks `i < n` once before calling `nth`.
No runtime length traversal or additional bounds check is needed for that read.
`nth` still traverses the selected prefix to find the element.

## API and ownership

- `empty() -> Sized(0)` creates an empty list.
- `cons(n, x, xs) -> Sized(n + 1)` consumes `xs: Sized(n)`.
- `repeat(n, x) -> Sized(n)` builds the indexed list with a runtime loop.
- `map(n, xs, f) -> Sized(n)` borrows `xs` and copies its transformed elements.
- `nth(n, xs, i, p)` borrows `xs` and requires `p: erased(Lt(i, n))`.
- `head(n, xs, p)` borrows `xs` and requires `p: erased(Lt(0, n))`.
- `size(n, xs)` borrows `xs` and returns `refine(fn(k) { Eq(k, n) })`.
  Unlike the index, this operation computes a runtime length by traversal.
- `into_list(n, xs)` consumes the wrapper and returns its ordinary owned list.
  The result no longer carries `n` in its type.

The `n` arguments above are erased except in `repeat`, which needs its runtime
iteration count. Indices and equality proofs add no record fields, proof
traversals or runtime checks. The wrapper itself is a runtime heap node and is
not free: the current repeat implementation allocates `n + 1` wrappers and
`n + 1` list nodes, freeing replaced wrappers during the loop. Mapping copies
the list and constructs another wrapper; optimization may eliminate that wrapper
when it is immediately consumed. Scope cleanup frees every remaining owner.

## Validation and limits

`tests/core_sized_list.py` compares the exact MIR of the indexed loop and mapped
result with an independently written unindexed wrapper implementation. It also
checks both object targets, native O0/O2 length and element models, allocation
cleanup, retained input ownership, signed edge values, callback overflow and
intended rejection diagnostics. Malformed base/step/map proofs in unused imported
functions are rejected, including the structural lemma in `dependent.list`.

The index is a natural-number expression in evidence. Runtime arithmetic retains
its overflow rules. These are checked library proofs and finite regression tests,
not a mechanized native-core soundness proof, a general source/erasure theorem or
an unrestricted totality claim. Normal checker resource limits apply. The library
has i64 elements, no type parameters, no index-changing in-place update API and
no zero-cost-wrapper guarantee.
