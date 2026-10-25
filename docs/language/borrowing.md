# Borrowing

References in jihoo are *second class*: they are made for a call or a block
and end there. They cannot be stored in ordinary structs, returned (except
as described below) or outlive what they point to, so there are no lifetime
annotations, and the compiler checks every use locally.

## Parameters

| parameter | the function may | at the call |
|-----------|------------------|-------------|
| `x: T` | read `x` during the call | `f(x)` |
| `inout x: T` | read and change `x`; no one else sees it meanwhile | `f(&x)` |
| `sink x: T` | own `x`: keep it, change it, destroy it | `f(x)`, which moves `x` |

A method's `self` takes the same forms, and `obj.method()` passes `&obj`
by itself when `self` is `inout`.

```jihoo
fn total(xs: Vec(i64)) -> i64 { ... }        // borrows: no copy
fn add_one(inout xs: Vec(i64)) { ... }       // changes in place
fn into_text(sink xs: Vec(i64)) -> String { ... }
```

Borrowed parameters are passed as pointers (or as values, for small plain
types), so passing a large value costs nothing.

## Exclusivity

One rule keeps borrows safe: **while something is borrowed mutably, nothing
else may use it; while something is borrowed, nothing may change it.**

```jihoo
swap(&a, &a)              // error: `a` is borrowed mutably twice
for x in v {
    v.push(x)             // error: `v` changes while the loop borrows it
}
```

A borrow lasts until its last use, not to the end of the block:

```jihoo
let first = v.as_slice()
println(first.len)        // last use of `first`
v.push(4)                 // fine
```

Assignments compute the value before borrowing the place, so
`c[i] = c[i] + 1` and `v.push(v.len())` work.

Because an `inout` parameter cannot alias anything, the compiler marks it
`noalias` for LLVM, which C compilers can only do where `restrict` is
written by hand.

## Local borrows

`let x = place` borrows a place that is not plain (see
[Values and ownership](ownership.md#let-and-var)). `inout x = &place`
borrows it to change it:

```jihoo
inout last = &v[v.len() - 1]
last += 1
```

`match &x` borrows `x` for the arms, mutably if `x` can change, so the arms
can change what they bind:

```jihoo
match &state {
    Running(count) => count += 1
    Stopped => {}
}
```

## Projections

A function may return a borrow of what its first parameter points to, with
`-> ref T` or `-> inout T`. Indexing and dereferencing are such functions,
which is how `Vec`, `Map` and `Box` are library types and still read like
built-ins:

```jihoo
impl(T: type) Vec(T) {
    pub fn index(self, i: i64) -> ref T { ... }
    pub fn index_mut(inout self, i: i64) -> inout T { ... }
}

v[2] += 1          // index_mut
let x = v[0]       // index
```

`x.f` and patterns see through `deref` (`Box`), and `index_mut` and
`deref_mut` are used where the place is changed.

## Views

`str`, slices `[T]`, closures and borrows are *views*: values that point
into something owned elsewhere. A struct or enum that contains a view is a
view, and so is a generic type given one (`Vec(str)`, `Option(ref T)`); a
library type that holds borrows through raw pointers says so with
`#[view]` (the `Vec` iterator does).

Views can be passed, returned, stored in other views and kept in local
variables. The compiler follows what each one borrows:

- A function returning a view returns something its arguments point to,
  and the caller counts the result as borrowing those arguments.
- A value cannot go away while a view of it is still used, and a function
  cannot return a view of its own locals.

```jihoo
fn first_word(s: str) -> str {
    ...
    s[0..i]                            // part of `s`: fine
}

fn broken() -> str {
    let s = String.from("temp")
    s.as_str()                         // error: the result borrows `s`,
}                                      // which goes away
```

## How it is checked

The checks run on the compiler's intermediate representation, in a pass
that does not trust the rest of the compiler: if the type checker let
something through by mistake, this pass still rejects it
([Architecture](../internals/architecture.md#the-borrow-kernel)).
