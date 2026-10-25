# Closures

`fn(x) { ... }` makes a closure. It borrows the variables it uses, mutably
if they can change, so making one allocates nothing.

```jihoo
fn each(xs: [i64], f: fn(i64)) {
    for x in xs {
        f(x)
    }
}

var total = 0
each(numbers, fn(x) { total += x })
```

## Closure parameters

A parameter of type `fn(A, B) -> R` takes a closure. Because a closure
borrows its surroundings, it is a [view](borrowing.md#views): it can be
called, passed on and kept in local variables, but not stored in an
ordinary struct or outlive what it uses. The borrow rules apply to what it
captures: while a closure that changes `n` is alive, nothing else may use
`n`.

Parameter types follow parameter conventions: `fn(T)` lends its argument
(by value if plain), `fn(inout T)` lends it mutably, `fn(sink T)` gives it.

```jihoo
fn count_if(xs: [i64], pred: fn(i64) -> bool) -> i64 { ... }

count_if(v.as_slice(), fn(x) { x > limit })
```

A closure's parameter types come from the parameter it is passed to;
otherwise they are written: `fn(x: i64) -> bool { ... }`. The result type
is inferred from the body.

## Compile-time closures

`comptime f: fn(A) -> R` makes one instance of the function per closure
passed, with the closure called directly, so LLVM inlines it. This is how
`sort_by` costs what a hand-written sort costs:

```jihoo
pub fn sort_by(comptime T: type, inout xs: Vec(T), comptime less: fn(T, T) -> bool)

sort_by(&people, fn(a, b) { a.age < b.age })
```

## Function pointers

`fnptr(A) -> R` is a plain function pointer: a named function, or a closure
that captures nothing. It can be stored anywhere and passed to C. A named
function also converts to a closure where one is expected.

```jihoo
let f: fnptr(i64) -> i64 = double
```
