# Functions in dependent code

In a `#![dependent_core]` module, `fn(A, B) -> R` describes a curried core
function. It can annotate a local value, a parameter or a result. This makes
higher-order helpers reusable without a new runtime closure representation:

```jihoo
#![dependent_core]

fn twice(f: fn(u64) -> u64, x: u64) -> u64 { f(f(x)) }
fn shifted(n: u64) -> fn(u64) -> u64 { fn(x) { x + n } }
export fn incremented(n: u64) -> u64 { twice(shifted(1), n) }
fn main() -> i64 {
    let f: fn(i64) -> i64 = fn(x) { x + 10 }
    f(7)
}
```

`main` returns `17`, and `incremented(n)` returns `n + 2`, trapping on overflow.
The lambda receives its parameter and result types from context. Helpers can
also be public and imported from another marked module. Multi-argument function
types support the existing partial application behavior.

## Outer indices and evidence

The type syntax lists types, not parameter names. Every listed domain and the
result may refer to names in the surrounding scope. For example, inside a
function with `n: u64` and `i: u64`, a callback type can be
`fn([i64; n], erased(Lt(i, n))) -> i64`. Here `n` and `i` refer to the outer
parameters; the callback's unnamed arguments do not introduce source names.
Dependent results referring to a callback's own named parameters still require
the existing named-function or annotated-lambda form.

Proof arguments inside a function type must explicitly use `erased(P)`. A
proof-producing function can itself be erased, as in
`erased(fn(u64) -> Eq(n, n))`. A function producing ordinary runtime data cannot
be made erased merely by wrapping its type in `erased(...)`.

The [natural proof library](natural-proofs.md) provides
`nat.eq_congr(f, a, b, p)`: given `f: fn(u64) -> u64` and `p: Eq(a, b)`, it
constructs `Eq(f(a), f(b))` using transport. Applications of `f` inside this
proof are ghost computations. They do not execute runtime arithmetic or make
an overflowing runtime application safe. The complete
[example](../../examples/core_functions.jh) demonstrates both modes.

## Ownership and runtime boundaries

Callbacks can take owned buffers and must obey the existing ownership rules.
Capturing an owned value remains rejected. Calling a callback twice evaluates
its body twice; passing or discarding the function value does not execute its
body. Effects performed while constructing a partially applied function remain
ordered and evaluated by the existing runtime normalization rules.

A function type needs at least one parameter and an explicit result. The core
form accepts plain domains and `erased(T)`; it does not add `sink`, `inout`,
zero-argument thunks, `fnptr`, `dyn fn`, heap closures or a function-pointer ABI.
An exported function cannot receive a function-valued argument from foreign
callers. Supported calls specialize through the core's existing normalization
and lowering; not every higher-order graph has a runtime representation.

The elaborator checks each annotation before conversion and shifts outer
references beneath the generated Pi binders. Existing nesting and graph limits
still apply. No kernel typing or normalization rule changes here. The tests
cover source elaboration and runtime erasure; this is not a general proof of
elaborator correspondence or compiler soundness.
