# Type aliases in dependent code

In a `#![dependent_core]` module, `type` gives a checked type or proposition a
transparent name. Optional parameters are erased `u64` indices:

```jihoo
#![dependent_core]

type Mem(n: u64) = buffer(n)
type Positive(n: u64) = Lt(0, n)
type Reader = fn(n: erased(u64), ref Mem(n), erased(Positive(n))) -> i64

fn read(n: erased(u64), b: ref Mem(n), p: erased(Positive(n))) -> i64 {
    index(b, 0, p)
}

fn main() -> i64 {
    let b: Mem(3) = alloc(3, 17)
    let f: Reader = read
    let value = f(3, b, decide_lt(0, 3))
    free(b, value)
}
```

This returns 17. `Mem(3)` is the same type as `buffer(3)`; it does not wrap the
buffer or allocate another object. `Positive(n)` names a proposition, so a
parameter of that type still needs `erased(...)`. `Reader` names a dependent
function type, preserving the callback's binder scope and ownership rules.
Aliases can also name scalar, array, refinement, borrowed and declared data
types. Named types keep the underlying type's identity and equality rules.

Each declaration is checked when encountered, including an unused alias.
An alias may refer to earlier declarations and its own parameters, but cannot
refer forward or recursively to itself. Every use supplies all indices in
order. Every index must typecheck as `u64` even when the alias body ignores
it; reduction cannot hide an invalid proof inside an unused argument. Type
computations remain erased and do not introduce runtime overflow checks.
This does not erase arithmetic needed to produce a runtime value.

Aliases are private unless declared `pub`. An imported public alias is written
`module.Name` or `module.Name(n)`. Expansion uses the checked meaning from its
defining module, so a caller's local names cannot capture it. A public alias
can describe a private representation exposed through public functions, but
does not grant access to private constructors or fields. Construct and match
data using the original accessible declaration's names, not alias names.

The subset accepts only `u64` parameters, not type parameters. It requires
`= type`, does not support associated types or declaration attributes, and
shares the existing core graph and normalization limits. Parameterized aliases
are rejected in ordinary modules; their existing unparameterized alias syntax
is unchanged. No kernel rule or formal soundness theorem is added by aliases.
