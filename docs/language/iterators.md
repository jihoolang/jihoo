# Iterator pipelines

Import `std.iter` to compose iterators without intermediate collections:

```jihoo
import std.iter

fn main() {
    let scale = 3
    let total = iter.range(0, 10)
        .map(fn(x) { x * scale })
        .filter(fn(x) { x > 10 })
        .take(3)
        .fold(0, fn(acc, x) { acc + x })
    println(total)                           // 45
}
```

`IteratorExt` provides these methods for every type implementing
[`Iterator`](generics.md#standard-traits). A `Vec` or slice supplies an
iterator through `.iter()`; `v.into_iter()` gives ownership of the vector's
elements to the iterator. `iter.range(start, end)` yields `i64` values from
`start` up to, but excluding, `end`; reversed ranges are empty.

## Adapters and consumers

| Method | Behavior |
| --- | --- |
| `map(f)` | Transform each item; infer the output type from `f` |
| `filter(pred)` | Yield the items for which `pred` returns true |
| `take(n)` | Yield at most `n` items; nonpositive counts are empty |
| `zip(other)` | Yield pairs, stopping when either input ends |
| `fold(initial, combine)` | Accumulate a result in input order |
| `for_each(f)` | Call `f` for each item |
| `count()` | Count the items |
| `any(pred)` | Stop at the first true result; empty input gives false |
| `all(pred)` | Stop at the first false result; empty input gives true |

`map`, `filter`, `take` and `zip` construct adapters. They pull no elements
until `next`, a consumer, or a `for` loop requests them. Each adapter owns
its input iterator. Callbacks borrow their arguments; an owned input item
is dropped after its callback finishes unless the adapter yields that item.
`fold` lends its accumulator and item to `combine`, then replaces the
accumulator with the returned value.

The callback's input types come from the iterator. Its body determines its
result type, so `map` may change the item type:

```jihoo
let count = iter.range(0, 6)
    .map(fn(x) { x % 2 == 0 })                // i64 -> bool
    .filter(fn(x) { x })
    .count()                                 // 3
```

An explicit output type works too: `.map(u8, fn(x) { x as u8 })`.

## Execution order and ownership

For a `map`/`filter` chain, one element is mapped and tested before the
next is requested. This order also applies to callback side effects and
traps; it differs from constructing a complete mapped collection first.
`take`, `any` and `all` stop requesting elements as soon as they finish.
`zip` requests its left item before its right item. It may consume one
unpaired left item when the right input ends, and stays exhausted after
either input returns `None`.

Callbacks are usually [borrowed closures](closures.md). An adapter keeps
their captures borrowed until its last use, and a borrowed input cannot
change while the adapter still needs it. Adapters may be stored in locals;
they cannot outlive their input or callback environments. An adapter owning
an `into_iter()` drops unconsumed elements when it goes away, including
after an early exit. These rules use the ordinary borrow checker and
destructors.

## Returning a pipeline

`map` and `filter` hold their callback as it is given, so an adapter is a
view when its callback borrows and an ordinary value when it is a
[`move fn`](closures.md#closures-that-own-what-they-capture). A function can
then build a pipeline from its own locals and return it, naming its type
with `impl Iterator`:

```jihoo
import std.iter

fn scaled(n: i64) -> impl Iterator {
    let k = n
    iter.range(0, 5).map(move fn(x) { x * k })
}

fn main() {
    println(scaled(3).fold(0, fn(acc, x) { acc + x }))   // 30
}
```

The pipeline allocates nothing and calls its closures directly; the
[fusion benchmark](../../benchmarks/functional-fusion/README.md) checks
that a returned pipeline becomes one loop. The adapters' types are
`MapIter(I, U, F)` and `FilterIter(I, F)`, with `F` the callback's type;
`impl Iterator` saves writing them.

## Compile time and performance

The same pipeline can run in a `const` initializer or `comptime` expression
when its operations are supported by the [MIR interpreter](comptime.md):

```jihoo
import std.iter

const TOTAL = iter.range(0, 5)
    .map(fn(x) { x * x })
    .fold(0, fn(acc, x) { acc + x })           // 30
```

Ranges and these adapters allocate no heap memory themselves. Their input
iterators and callbacks may allocate; the interpreter's existing allocation
and destructor restrictions still apply.

At runtime, adapters are concrete generic structs. LLVM can inline their
`next` methods and callbacks and remove the adapter state. This permits
simple pipelines to become a single loop without indirect calls or
intermediate collections. Fusion depends on optimization and the particular
pipeline; it is not a language guarantee for every composition.
