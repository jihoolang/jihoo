# Design: closures that own what they capture

Item 1 of the [0.4 roadmap](roadmap.md#5-functional-composition-without-cost-04):
a function could not return a pipeline whose closure captures its own
locals without paying for `dyn fn`. A borrowing `fn` is free but is a view
of the function that made it. A `dyn fn` can leave that function, but it
costs an allocation and an indirect call. This note records what 0.4 adds
between the two, and how the roadmap's open questions were settled.

## The closure

`move fn(x) { ... }` captures by value, as a `dyn fn` does: plain values
are copied, the others move in, and a capture that is a view is an error.
Its value is just the tuple of captures, with no heap and no code pointer.
Its type is `TyKind.Lambda(f, env, sig)` (`types.jh`): `f` is the lifted
function, `env` the tuple it is laid out as, and `sig` its signature for
calls and messages. Layout, drops, fields and views all come from `env`,
so code generation, elaboration, the borrow kernel and the interpreter see
an ordinary aggregate.

A call borrows the value and calls `f` directly, passing the borrow where a
borrowing closure passes its environment pointer. A `move fn` becomes a
borrowing closure (its function, and a borrow of itself) where a
`fn(A) -> R` is expected, and moves to the heap with a vtable where a
`dyn fn(A) -> R` is expected. Its body reads what it captured, as a
`dyn fn` body does: a call borrows the value shared, so it cannot be
`FnMut`.

The type's identity is the lifted function, not the signature, and it is
created before the body is lowered (the body's environment parameter is a
borrow of it). A closure's body is lowered twice when its result type is
inferred, and a function's when its result is `impl`. So `lambda()` keys
each `move fn` by the instance it is written in (`Fb.root`), its position
and the compile-time names in scope (`Sema.lambda_ids`), and reuses the
same function and type when that key comes back. The signature is filled
in once the body is known; it is not part of the type's interning key.

## How a result names the type (open question 1)

The roadmap compared an opaque result type with adapters generic over the
closure type. jihoo has both now, and they do different jobs:

- Adapters are generic over the closure type (below). That makes the
  pipeline's type concrete: `MapIter(Range, i64, move fn(i64) -> i64)`.
- `-> impl Trait` and `-> impl fn(A) -> R` are how a function names that
  type in its result. `instance()` lowers the body once to learn the type
  (`infer_result`, like a closure's inferred result), records the type of
  any `return`, checks the bound, and the body is then lowered for real
  with the type known. A function that uses itself in its own `impl`
  result is an error.

The result is not opaque, unlike Rust's `impl Trait`: the caller sees the
body's type, as a Zig caller sees an inferred type. That is what
per-instance checking already does for generic code. It also lets the
caller use `Item` without `Iterator<Item = ...>` syntax. The cost is that
changing the body can change what callers see, which matters little
inside one program. An opaque wrapper type could be added later without
changing the syntax.

`impl` is not a parameter's type (Rust's argument-position `impl Trait`).
A parameter that takes any closure is written as a type parameter, so the
instance's arguments stay explicit.

## Owned closures, borrowing ones, or both in adapters (question 2)

Both. `MapIter(I, U, F)` and `FilterIter(I, F)` store their callback as
an `F` that `map` and `filter` take with `sink`. The bound is
`comptime F: impl fn(Self.Item) -> U`:

- A borrowing closure is a `Closure(sig)` value, a view. The adapter is
  then a view because one of its type arguments is (`adt_instance`), and it
  is checked exactly as before. Existing pipelines keep their semantics,
  and the fusion benchmark's optimized IR is unchanged.
- A `move fn` is not a view, so the adapter is not one either. It can be
  returned.

A parameter bounded by `impl fn` is never written at a call (`.map(u8, f)`
still writes only `U`). A closure argument for `sink f: F` takes its
parameter types from the bound, and the closure's signature then binds
what the bound names (`U`). Consumers (`fold`, `for_each`, `any`, `all`)
still take a borrowing `fn`: they finish before returning, and a
`move fn` is lent to them.

## Rejecting captured views (question 3)

A `move fn` capture is checked as a `dyn fn` capture is: a capture whose
type `is_view` is an error that names it ("a `move fn` owns what it
captures, so it cannot capture `xs`, which holds a borrow"). Because the
captured value moves in, use after the move and moves on only some paths
are ordinary elaboration errors. A borrowing closure returned through
`-> impl fn` is an ordinary escaping view that the borrow kernel rejects.

## Not done

- `move fn` cannot change its captures. A `var` closure called through
  `inout` could allow it later.
- An `impl` result's type is the body's last expression or the value of a
  `return`; a closure that ends the body takes its parameter types from
  `impl fn` only when it is the body's last expression (not inside an
  `if`).
- `move fn` is not a `comptime` closure argument; those already inline.
- `compiler/` does not use these features until the seed knows them
  ([self-hosting](self-hosting.md)).
