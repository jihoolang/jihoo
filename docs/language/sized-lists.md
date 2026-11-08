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

## Constructing from bounded indices

`tabulate(n, f)` constructs `Sized(n)` directly from a callback of type
`fn(i: u64, erased(Lt(i, n))) -> i64`. Each callback receives its index and
proof that the index is in range. A callback can therefore read a borrowed
buffer without a separate bounds check or a list-length traversal. This avoids
building a repeated list and then mapping it.

The construction loop carries `Sized(k)` after `k` iterations. It prepends
one value at each step, using the imported `nat.mirror_lt` theorem to visit
indices from `n - 1` down to `0`. The final list contains `f(0), f(1), ...`
in ascending-index order, but callback effects happen in descending-index
order, exactly once per index on a successful run. For `n == 0`, no callback
runs. Callbacks may allocate or trap; this API does not promise purity or
totality. Passing an owned capture that would be consumed repeatedly is rejected.

`from_buffer(n, source)` uses this callback to copy a borrowed `buffer(n)`
directly into an independent `Sized(n)`. `from_range(n, source, offset, count,
fits)` copies only the selected range and returns `Sized(count)`, using
`fits: erased(Lt(offset + count, n + 1))`. Empty ranges and ranges ending
exactly at the source length are valid. Both helpers preserve element order
and leave the source usable. The result can outlive the source or remain
unchanged when the source is later modified.

The [complete conversion example](../../examples/core_tabulate.jh) applies the
imported mirror and [range-offset theorem](buffer-ranges.md#range-bounds) inside
the indexed loop, then reads the exact-length result using the caller's bound.
There is no intermediate buffer or structural traversal to rediscover the
result length. These are owned copies, not borrowing views.

The current construction allocates `n + 1` list nodes and `n + 1` wrapper
nodes, freeing replaced wrappers during the loop. It avoids the second list
allocation/traversal of repeat-then-map, but it is not a zero-allocation API.
The existing checked runtime subtraction/addition and allocation failure rules
remain in force. The library proves length and access bounds, not a formal
pointwise correspondence theorem for callback results.

## Imported induction inside a runtime loop

`append_into(n, m, prefix, suffix)` borrows `prefix: Sized(n)`, consumes
`suffix: Sized(m)`, and returns `Sized(n + m)`. The prefix is copied, while the
suffix's existing list nodes become part of the result. Imported
`list.append_into_length` supplies the structural length proof; the wrapper
transports it through the private input equalities.

The [concatenation example](../../examples/core_sized_concat.jh) repeats a
two-element prefix with this loop:

```jihoo
fold(n, fn(k) { sized_list.Sized(k + k) }, sized_list.empty(),
    fn(i, p, acc) { sized_list.append_into(2, i + i, pair, acc) })
```

Every step uses the imported structural theorem to establish the next
accumulator's exact length. The result has type `Sized(n + n)`, so a caller's
`i < n + n` proof suffices to read it. This is a loop postcondition proved using
an imported inductive lemma, with the program and evidence checked and erased
from the same core. It does not add ordinary `ensures` syntax or establish
mechanized compiler soundness.

Each iteration copies only the two prefix elements and allocates a new wrapper;
it transfers the entire old accumulator tail and frees the old wrapper. This
makes node allocation linear in the number of iterations, rather than repeatedly
copying a growing tail. Runtime computation of `n + n` still checks overflow;
the erased index does not make runtime arithmetic wrapping or trap-free.

## API and ownership

- `empty() -> Sized(0)` creates an empty list.
- `cons(n, x, xs) -> Sized(n + 1)` consumes `xs: Sized(n)`.
- `repeat(n, x) -> Sized(n)` builds the indexed list with a runtime loop.
- `tabulate(n, f) -> Sized(n)` constructs elements from bounded indices,
  invoking callbacks in descending-index order.
- `from_buffer(n, source) -> Sized(n)` copies a borrowed buffer directly.
- `to_buffer(n, xs) -> buffer(n)` copies a borrowed exact-length list in one
  structural pass; `n` is a runtime allocation count. See
  [buffer materialization](list-buffer-transfer.md).
- `from_range(n, source, offset, count, fits) -> Sized(count)` copies a proved
  range directly; `n` and `fits` are erased.
- `append_into(n, m, xs, ys) -> Sized(n + m)` borrows/copies the prefix
  and consumes/transfers the suffix. Both indices are erased.
- `map(n, xs, f) -> Sized(n)` borrows `xs` and copies its transformed elements.
- `nth(n, xs, i, p)` borrows `xs` and requires `p: erased(Lt(i, n))`.
- `head(n, xs, p)` borrows `xs` and requires `p: erased(Lt(0, n))`.
- `size(n, xs)` borrows `xs` and returns `refine(fn(k) { Eq(k, n) })`.
  Unlike the index, this operation computes a runtime length by traversal.
- `into_list(n, xs)` consumes the wrapper and returns its ordinary owned list.
  The result no longer carries `n` in its type.

The `n` arguments above are erased except in `repeat`, `tabulate`,
`from_buffer` and `to_buffer`, which need runtime iteration or allocation counts.
`from_range` uses its runtime `count` instead. Indices and equality proofs add no record fields, proof
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

`tests/core_sized_concat.py` compares indexed concatenation-loop MIR with an
unindexed wrapper reference. It checks order, retained prefix ownership,
linear allocation counts, no suffix copying, and rejection of aliased or reused
owners, wrong indices, broken loop steps and malformed imported equalities.
Both object targets and native O0/O2 executions are covered.

`tests/core_tabulate.py` checks direct buffer/range conversion, callback order
and effects, no callbacks for empty results, retained and released source owners,
independent mutation, exact erasure against an unindexed wrapper, allocation
counts, both object targets and malformed imported callback/loop/range evidence.

The index is a natural-number expression in evidence. Runtime arithmetic retains
its overflow rules. These are checked library proofs and finite regression tests,
not a mechanized native-core soundness proof, a general source/erasure theorem or
an unrestricted totality claim. Normal checker resource limits apply. The library
has i64 elements, no type parameters, no index-changing in-place update API and
no zero-cost-wrapper guarantee.
