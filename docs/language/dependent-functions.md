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
    let f: fn(n: u64, i64) -> buffer(n) = fn(k, x) { alloc(k, x) }
    free(f(3, 17), 17)
}
```

`main` returns `17`, and `incremented(n)` returns `n + 2`, trapping on overflow.
The lambda receives its parameter and result types from context. Helpers can
also be public and imported from another marked module. Multi-argument function
types support the existing partial application behavior.

## Outer indices and evidence

Domains can be unnamed types or named binders such as `n: u64`. A binder is
in scope in later domains and the result, so `fn(n: u64, buffer(n)) -> i64`
accepts a buffer at the length passed to that callback. A binder is not in
scope in its own domain, and does not escape the function type. Every domain
and the result may also refer to names in the surrounding scope. For example, inside a
function with `n: u64` and `i: u64`, a callback type can be
`fn([i64; n], erased(Lt(i, n))) -> i64`. Here `n` and `i` refer to the outer
parameters; the callback's unnamed arguments do not introduce source names.
Named results such as `fn(n: u64) -> buffer(n)` and nested types such as
`fn(n: u64) -> fn(erased(Eq(n, n))) -> u64` are supported. Parameter names
do not affect type equality: a lambda can call the same argument `k`. A named
binder may shadow an outer name; duplicate names within one function type and
reserved built-in names are rejected. `_` introduces an inaccessible binder.
Unnamed domains keep their previous outer-scope meaning, even when mixed with
named domains.

These binders are supported only in marked dependent modules. Ordinary code
rejects named function type parameters; the existing unnamed function syntax
remains available there.

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

## Pure natural local definitions

An immutable local may retain a pure natural function definition for later calls
and dependent conversion. For example, given `fn next(n: u64) -> u64 { n + 1 }`,
`let y = next(n)` lets a subsequent `Eq(y, n + 1)` annotation check using
`refl(n + 1)`. The same applies to imported helpers, local typed lambdas, curried
natural functions and aliases of those functions. An imported public function
can be referenced as a value, such as `let f = module.next`; private declarations
and shadowed module names are not exposed by this syntax. Captured scalar values retain
their lexical binding when another name shadows them.

The compiler inspects original checked syntax, including global bodies and actual
arguments, before ghost normalization. Supported terms are U64 literals and
variables, addition, checked subtraction, application and lambdas with non-erased
U64 parameters. A variable of function type is an unknown callback, so neither
calling nor returning one establishes purity. Explicit proof parameters, general
higher-order combinators, memory access and effectful function bodies remain
outside this conservative fragment. Existing code can still call these functions;
their local results do not gain this transparency.

The original initializer remains evaluated at its binding point. Unused or
proof-only overflowing calls still trap, while discarding a lambda does not run
its body. A prior effectful scalar result can be captured without replaying its
effects. A function alias must also normalize in runtime mode to a lambda with
no preceding capture-time computation. A partial application that evaluates
trapping arithmetic while capturing an argument retains its original opaque
binding, so subsequent calls do not replay that prefix. Pure arithmetic in
scalar definitions may be recomputed under existing beta normalization;
this is not an exactly-once arithmetic guarantee. The shared 4096-occurrence
inspection budget counts repeated graph and global references and falls back to
an opaque binding on exhaustion. No kernel equality rule is added, and this is
not a theorem of general purity inference or elaborator soundness.

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

The elaborator checks each annotation before conversion and introduces
sequential Pi binders, preserving outer references and restoring source scope
after each function type. Existing nesting and graph limits
still apply. No kernel typing or normalization rule changes here. The tests
cover source elaboration and runtime erasure; this is not a general proof of
elaborator correspondence or compiler soundness.
