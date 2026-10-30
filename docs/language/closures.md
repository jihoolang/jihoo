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
called, passed on, kept in local variables, or stored in a struct that is
itself a view. It cannot outlive what it uses. The borrow rules apply to what it
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

A generic callback may have known input types and an inferred result type.
The compiler uses those inputs to check the closure, then infers generic
arguments from its result. For example,
[iterator](iterators.md) `.map(fn(x) { x * 2 })` needs no written type
argument or closure parameter type.

## Compile-time closures

`comptime f: fn(A) -> R` makes one instance of the function per closure
passed, with the closure called directly, so LLVM inlines it. This is how
`sort_by` costs what a hand-written sort costs:

```jihoo
pub fn sort_by(comptime T: type, inout xs: Vec(T), comptime less: fn(T, T) -> bool)

sort_by(&people, fn(a, b) { a.age < b.age })
```

An immutable local initialized with a closure, or an immutable alias of it,
can also be passed. Compile-time closure parameters may be captured by an
inner closure, called there, and forwarded to another compile-time closure
parameter:

```jihoo
fn apply(comptime f: fn(i64) -> i64, x: i64) -> i64 { f(x) }

fn twice(comptime f: fn(i64) -> i64, x: i64) -> i64 {
    let inner = fn(y: i64) { apply(f, y) }
    apply(inner, inner(x))
}

fn main() {
    let scale = 3
    let multiply = fn(x: i64) { x * scale }
    println(twice(multiply, 2))               // 18
}
```

The function identity is known at compile time; its captured values may be
runtime values. Captures retain the same borrow and lifetime checks. A
mutable closure variable or an ordinary closure parameter has no statically
known function identity for specialization; use an ordinary closure parameter
for those values.

## Closures that own what they capture

A closure borrows, so it cannot outlive the block that made it. `move fn`
makes one that owns what it captures instead: the captured values move
into it (or are copied, if they are plain), and it can leave the function
that made it. It allocates nothing, and calling it calls its function
directly, so LLVM inlines it as it does a borrowing closure.

```jihoo
fn adder(n: i64) -> impl fn(i64) -> i64 {
    move fn(x) { x + n }
}

fn main() {
    let add = adder(10)
    println(add(5))                           // 15
}
```

Each `move fn` expression has a type of its own, known while compiling
and written in messages as `move fn(i64) -> i64`. Two closures are two
types even when their signatures are the same. The type has no name to
write; `impl` stands for it:

- `-> impl fn(A) -> R` or `-> impl Trait` as a result: the type of the
  function's body, which must be such a closure, or implement the trait.
  The body decides the type, so every `return` must give that same type,
  and the function cannot call itself.
- `comptime F: impl fn(A) -> R` as a type parameter: the function has one
  instance per closure type. A closure argument for `sink f: F` takes its
  parameter types from the bound, and `F` is never written at the call.
  A borrowing closure fits the bound too.

```jihoo
fn twice(comptime F: impl fn(i64) -> i64, sink f: F, x: i64) -> i64 {
    f(f(x))
}

twice(move fn(x) { x * 3 }, 1)                // 9
```

A `move fn` is a value like any other: it moves, and a value it captured
is dropped when it is. It reads what it captured but cannot change it,
since a call borrows it shared. It cannot capture a view (a `str`, a slice,
a borrowing closure, a struct holding one): what it holds must not borrow.
It is lent where a `fn(A) -> R` is expected, and moves to the heap where a
`dyn fn(A) -> R` is. [Iterator adapters](iterators.md#returning-a-pipeline)
hold either kind of closure, so a function can return a pipeline.

To return or store closures of different types in one place, write the
closure where a `dyn fn(A) -> R` is expected: it then owns what it
captures, on the heap ([dynamic dispatch](dyn.md#dyn-fn)):

```jihoo
fn pick(add: bool, n: i64) -> dyn fn(i64) -> i64 {
    if add { fn(x) { x + n } } else { fn(x) { x * n } }
}
```

## Function pointers

`fnptr(A) -> R` is a plain function pointer: a named function, or a closure
that captures nothing. It can be stored anywhere and passed to C. A named
function also converts to a closure where one is expected.

```jihoo
let f: fnptr(i64) -> i64 = double
```
