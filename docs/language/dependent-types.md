# Dependent types

A module marked `#![dependent_core]` is checked by a small dependent type theory:
a function can state what it needs and what it promises in its types, the compiler
checks the proofs, and the proofs are erased before code generation. An index with
evidence needs no bounds check, because the check has already been done.

```jihoo
#![dependent_core]

fn at(xs: [i64; 3], i: u64, p: erased(Lt(i, 3))) -> i64 { index(xs, i, p) }

fn read(i: u64) -> i64 {
    let xs = [10, 20, 30]
    if_lt(i, 3, fn(q) { at(xs, i, q) }, -1)
}

fn main() -> i64 { read(1) + read(7) }
```

`erased(Lt(i, 3))` is a parameter of evidence that `i < 3`, which callers must supply
and which does not exist at run time. `if_lt(a, b, fn(q) { yes }, no)` compares at run
time, and `yes` receives the evidence. The compiled `at` is a load with no comparison.
`main` returns 19.

This is a separate, smaller language inside jihoo. It is new in 0.5 and its limits
are [listed below](#what-it-does-not-do). For the rules, see
[the specification](../internals/core-spec.md); for why they are what they are, see
[the design](../internals/dependent-core.md).

## Requires and ensures

A precondition is a parameter of erased evidence, and a postcondition is the result
type. A function's result can be evidence itself, as a lemma is:

```jihoo
#![dependent_core]

// x < y gives x < y + 1. The rules of the order are lt_add, lt_cancel, lt_le,
// zero_le and decide_lt.
fn weaken(x: u64, y: u64, p: erased(Lt(x, y))) -> Lt(x, y + 1) {
    lt_le(x, y, y + 1, p, lt_add(0, 2, y, decide_lt(0, 2)))
}

// A value with evidence about it: at run time, only the u64.
fn clamp(i: u64, n: u64, p: erased(Lt(0, n))) -> refine(fn(j) { Lt(j, n) }) {
    if_lt(i, n, fn(q) { pack(i, q) }, pack(0, p))
}

fn main() -> i64 { 0 }
```

Evidence is built from these rules, from `refl` and `transport` for equality on u64,
from what `if_lt` and `if_eq` give, and from inductive propositions the program
declares. Nothing is searched for: a proof is written out, and is an ordinary term.

## Contextual types

Integer literals use the expected scalar type. Without one, arithmetic takes its
signedness from the first nonliteral operand, looking through nested arithmetic:
`let next = 1 + n` and `let next = n + 1` both infer u64 when `n` is u64.
Literal-only arithmetic still defaults to i64. This is inference, not a conversion:
mixing an i64 value with a u64 value is an error, and overflow still traps.

Contextual lambdas may spell out their parameter types. For example, a loop body
can be `fn(i: u64, p: Lt(i, n), acc: i64) -> i64 { acc + 1 }`. Its types are checked
against the loop's signature; `p` remains erased even though its annotation does
not say `erased`. Writing `p: erased(Lt(i, n))` asserts that it is erased, while
writing `i: erased(u64)` is an error because the loop index is a runtime parameter.
Annotations may refer to earlier parameters, and parameters in one lambda must
have distinct names. Inner lambdas may still shadow outer names.

The same optional parameter annotations work in `if_lt`/`if_eq` branches, proof
families such as `fn(k: u64) { Eq(k, k) }`, and data motives such as
`fn(t: List) { i64 }`. Loop, induction and conditional cases also allow result annotations.
Families and motives still omit result annotations. No
proof search is implied, and all annotations are checked, including evidence
inside an annotation that computation would otherwise discard.

Without an expected type, `if_lt` and `if_eq` infer their result from the
proof-bearing branch (or its result annotation), then check the other branch
against it. A `match` infers its result from the first variant in the type's
**declaration order**, regardless of arm order, and checks the remaining arms.
Literal-only branches default to `i64`; use a local or branch annotation when
another numeric type is intended. No signed/unsigned coercion is inserted.
An inferred match type cannot mention the first arm's local fields. Dependent
motives, proofs by borrowed cases, and empty matches still need an expected
type, usually a `let` or function result annotation. Inference does not search
other arms or speculate by elaborating an expression twice.


## Owned memory

`buffer(n)` is `n` i64 values on the heap, and data declared with `enum` or `struct` that
holds one, or is recursive, lives on the heap too. Each owned value is used exactly once,
which the kernel checks. A value that a scope does not use is freed there, so `free` need
not be written, and a wrong free is a compile error rather than a leak or a double free.

A `ref T` parameter reads without consuming, and an `inout` parameter changes a value its
caller keeps. `old(x)`, in types and evidence, is the value it started with:

```jihoo
#![dependent_core]

enum List {
    Nil
    Cons(i64, List)
}

fn length(xs: ref List) -> u64 { induct(fn(t) { u64 }, 0, fn(x, rest, ih) { ih + 1 }, xs) }

fn push(inout xs: List, x: i64) -> Eq(length(xs), length(old(xs)) + 1) {
    xs = List.Cons(x, xs)
    refl(length(old(xs)) + 1)
}

fn main() -> i64 {
    var xs = List.Nil
    let a = push(&xs, 1)
    let b = push(&xs, 2)
    0
}
```

A call with `&x` is a `let`'s value, a statement or a block's value, and x is then the new
value: a fact about the old one stays about the old one. A change inside a `let`'s value or a
loop body is an error: call a function that takes `&x`, or pass the value as the accumulator.
Nothing is allocated to return a value with its container, and rebuilding a node at its own
size reuses it.

## Vectors

[`dependent.vec`](../../lib/dependent/vec.jh) is a growable vector of i64 whose contracts are
types, so evidence follows it as it changes:

```jihoo
#![dependent_core]

import dependent.vec

fn sum(v: ref vec.Vec) -> i64 {
    let n = vec.size(v)
    fold(witness(n), 0, fn(i, p, acc) {
        acc + vec.get(v, i, transport(fn(m) { Lt(i, m) }, proof(n), p))
    })
}

fn main() -> i64 {
    var v = vec.new()
    let a = vec.push(&v, 20)
    let b = vec.push(&v, 22)
    sum(v)
}
```

`vec.size` gives the length with evidence that it is the length. `fold(n, init, fn(i, p,
acc) { ... })` is a loop whose body has evidence of `Lt(i, n)`, so each read needs no check.
`main` returns 42. A loop's accumulator can also have a type that changes with the index, which
is how a loop's invariant is stated, and into a proposition the same form is a proof by
induction: see [the invariant example](../../examples/core_invariant.jh).

## Module boundaries

A marked module imports other marked modules with `import a.b` or `import a.b as c`.
Use the direct import's alias to name its public declarations: `c.helper(...)`,
`c.Proposition(n)`, `c.constructor(...)`, `c.Record { ... }` or `c.Enum.Variant(...)`.
Qualified patterns resolve the same way. Imports do not put another module's
names into the local namespace, and one alias cannot reach another module's items.
Different modules may reuse helper, type and constructor names.

Items and struct fields are private unless marked `pub`. A public proposition's
constructors and a public enum's variants are public members of that type.
A public factory can return a private type that callers pass back to its public
API, but callers cannot inspect it with `match` or `induct`. Constructing a struct
or inducting over it exposes all its fields, so those operations require access
to every field. A named `match` may select public fields and leave private ones
with `..`; discarded fields still get the usual ownership cleanup. `_` is a
discarded binding, not a name that can recover one of those fields.

`dependent.vec.Vec` keeps its checked representation public: all four fields are
explicitly `pub`, so existing proof-oriented construction and destructuring work.
Visibility does not replace type or ownership checking.

Only direct imports are visible. Even `pub import` does not re-export a module
alias, matching ordinary module lookup; marked modules have no prelude or wildcard
imports. Definitions are still checked in declaration order, and only the root
module supplies the executable entry point. An `export fn` chooses a foreign
symbol independently of `pub`; two exported symbols cannot have the same name.

## What it does not do

- **It is not verified.** The kernel's soundness is not mechanically proved. It rests on
  rejection suites, an independent evaluator and reviews. A proof is planned after 0.5.
- **It is a subset.** A marked module has no `if`, `while`, division, comparison operators, strings,
  closures at run time, threads, generics or `comptime`, and `trait` there declares a proposition.
  An export's arguments are u64 or i64. It imports only marked modules, and ordinary modules cannot
  import it.
- **Elements are i64.** There are no type parameters, so a vector of another type is written again.
- **A `let` or `var` of an owned value keeps only its type**, so `var v = vec.new()` knows nothing
  about its length until `vec.clear(&v)` says it is 0.
- **Changing the i-th element of a list walks all of it.** A buffer changes any element directly.
- **Recursion is structural**, over declared data, and a program that checks may still be rejected
  while compiling in [a few listed cases](../internals/core-spec.md#lowering).

The examples named `core_*`, such as [the vector](../../examples/core_vec.jh), show each part in a
complete program, and the ordinary [contracts](contracts.md) remain the way to state and prove properties of unmarked code.
