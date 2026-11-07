# List proof library

Marked modules can `import dependent.list`. The library supplies an owned list
of `i64`, borrowing observations, copies and structural length proofs. Its source
is [lib/dependent/list.jh](../../lib/dependent/list.jh); there are no new compiler
intrinsics or unchecked axioms.

## Operations and ownership

`list.List.Nil` and `list.List.Cons(value, tail)` build a list. Every node,
including `Nil`, is allocated on the heap. A scope frees an unused owned list.

- `repeat(n, x)` builds `n` copies of `x`.
- `length(xs)`, `sum(xs)` and `head_or(xs, missing)` borrow their list. `sum`
  uses checked i64 addition; an overflow traps.
- `head(xs, p)` needs `p: erased(Lt(0, length(xs)))`;
  `nth(xs, i, p)` needs `p: erased(Lt(i, length(xs)))`. Both borrow their
  list. Evidence rules out empty or out-of-bounds access, rather than a
  fallback value or an additional runtime bounds check. `nth` walks the
  prefix up to the selected element.
- `map(xs, f)` borrows `xs` and takes `f: fn(i64) -> i64`, returning a new
  owned list of the transformed elements. It preserves element order.
- `size(xs)` returns the length as `refine(fn(k) { Eq(k, length(xs)) })`.
- `clone(xs)` borrows its input and returns a new owned copy.
- `append(xs, ys)` borrows **both** inputs and copies both into a new list.
  It does not consume the second list or share its nodes.
- `into_length(xs)` consumes a list while counting, freeing every node. It can
  measure a newly produced list without introducing a temporary borrow.

The current source elaborator lends one owned value per expression. To call
`append` with two locally owned lists, use a helper whose first parameter is
already a borrow, then lend the second local list at the call. The
[executable example](../../examples/core_list_library.jh) shows this pattern.
This module does not extend the borrowing rules or provide generic element types.

## Map evaluation order

Structural recursion computes the tail before the current node, so `map`
invokes `f` from the last element to the first, once per element. This order
matters if the callback allocates or traps. An empty map does not invoke `f`.
Named functions and fully annotated scalar-capturing functions are supported:

```jihoo
let ys = list.map(xs, fn(x: i64) -> i64 { x + offset })
```

A successful result preserves the original element order and leaves the borrowed
input available. Ordinary integer-overflow and allocation-failure behavior still
applies. Computing only the mapped length, or discarding the mapped result, does
not erase a runtime callback's traps. A proof *about* the map is different: its
callback applications are ghost terms and do not execute.

## Structural theorems

`clone_length(xs)` proves:

```jihoo
Eq(into_length(clone(xs)), length(xs))
```

`append_length(xs, ys)` proves:

```jihoo
Eq(into_length(append(xs, ys)), length(xs) + length(ys))
```

`map_length(xs, f)` proves:

```jihoo
Eq(into_length(map(xs, f)), length(xs))
```

When applying `map_length` to a locally owned list, use its evidence inside a
helper taking `ref List`, as the map example does. A proof type that retains a
borrow cannot be returned from the temporary lend into a surrounding `let`.

All three lemmas use structural induction over a borrow. The append proof uses the
clone theorem in its empty-prefix case and transports the induction hypothesis
in its nonempty case. The terms in these propositions are ghost computations:
proving a length does not copy or consume the caller's list at runtime.

The example checks that the sum of the two input lengths is below nine. The
imported append theorem then proves the array bound for a separately computed
length of the appended list. The proof is erased, while the executed append and
consuming length remain. `lookup(2, 3)` returns `60`; an input length sum of nine
or more returns `-1` without allocating an append result.

[The map example](../../examples/core_list_map.jh) uses imported `map_length`
to prove an array bound from the input list's length, and separately uses
proof-bounded `nth` to read a mapped list. `lookup(3, 7)` returns `40` and
`at(3, 1, 7)` returns `8`. The theorem states preservation of length, not that
the callback terminates or cannot trap.

## Validation boundary

`tests/core_list_library.py`, included in the core suite, compares imported and
flattened-module MIR, checks both object targets and compares native O0/O2
results with arithmetic models. Allocation accounting checks all nodes are
freed and that erased theorems introduce no extra copies. Negative tests reject
false theorems and malformed induction cases in unused imported functions, with
positive controls and exact source diagnostics. Runtime sum overflow still traps.

`tests/core_list_map.py` additionally checks named and scalar-capturing maps,
mapped order, tail-to-head callback allocation traces, proof-only callback
suppression, both signed overflow directions, empty and maximal-index access,
and malformed unused imported map/nth proofs. Its allocation callback uses a
runtime size to retain a traceable allocation in the tested O0/O2 builds.

These are native-core library proofs and regression tests, not Lean certificates
for these definitions or a full compiler soundness theorem. The MIR comparison
checks import/erasure consistency, not an independently formalized list model.
Normal resource limits apply, and the ordinary `requires`/`ensures` syntax remains
unsupported in dependent modules.
