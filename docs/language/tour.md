# A tour

jihoo is a systems language: programs compile through LLVM to machine code
that runs as fast as C, with no garbage collector and no runtime. Memory is
safe without lifetime annotations: every value has one owner, functions
borrow their arguments, and the compiler checks that nothing changes what
is borrowed.

```jihoo
struct Point {
    x: i64
    y: i64
}

impl Point {
    fn norm2(self) -> i64 {
        self.x * self.x + self.y * self.y
    }
    fn shift(inout self, d: i64) {
        self.x += d
    }
}

fn main() {
    var p = Point { x: 3, y: 4 }
    p.shift(1)
    println(p.norm2())          // 32
}
```

## Variables

`let` names a value that does not change, `var` one that does. Types of
locals are inferred; signatures are written out.

```jihoo
let n = 10          // i64
var total = 0
for i in 0..n {
    total += i
}
```

## Functions borrow

A parameter `x: T` is lent to the function for the call: it can read it,
not change or keep it. `inout x: T` lends it to be changed, and the caller
writes `&` to show that. `sink x: T` gives the value away.

```jihoo
fn sum(xs: [i64]) -> i64 { ... }            // reads
fn reset(inout v: Vec(i64)) { v.clear() }   // changes
fn consume(sink s: String) { ... }          // takes

reset(&numbers)
```

Nothing is copied unless the program says so: values that own memory
(`String`, `Vec`, `Box`, anything holding one) move, and `.clone()` copies
them. Numbers and structs made of numbers copy freely. See
[Values and ownership](ownership.md) and [Borrowing](borrowing.md).

## Data

Structs, tuples, arrays, and enums with payloads; `match` takes them apart
and must cover every case.

```jihoo
enum Expr {
    Num(i64)
    Add(Box(Expr), Box(Expr))
}

fn eval(e: Expr) -> i64 {
    match e {
        Num(n) => n
        Add(a, b) => eval(a) + eval(b)
    }
}
```

## Generics

A generic parameter is a compile-time parameter, and each set of arguments
compiles to its own code. Bounds are traits.

```jihoo
fn largest(comptime T: Ord, xs: [T]) -> T { ... }

let words = Map(String, i64).new()
```

## Errors

`Option` and `Result` are ordinary enums, and `?` returns early with the
failure. Bugs stop the program with a message: an index out of bounds, an
integer overflow (in debug builds), `panic(...)`.

```jihoo
fn parse_pair(a: str, b: str) -> Option(i64) {
    Some(a.parse_int()? + b.parse_int()?)
}
```

## The standard library

`Vec`, `String`, `Map`, `Box`, sorting, files and printing are written in
jihoo, on top of [unsafe code](unsafe.md), and the same library works without
libc ([Profiles](profiles.md)). See the [Standard library](../reference/standard-library.md).
