# Dynamic dispatch

A [generic](generics.md) function is compiled once per type, so every call
is known while compiling. When the type is known only while the program
runs, as in a list of shapes of several kinds or a callback kept for later,
a value of a `dyn` type holds it:

- `dyn Trait`: a value of some type with the trait.
- `dyn fn(A) -> R`: a closure that owns what it captures.

Both own their value, on the heap, like a `Box` that has forgotten its
type. They move, are dropped, can be stored in structs and collections,
returned, and sent to other threads. They are never views: nothing they
hold borrows.

## `dyn Trait`

A value whose type implements the trait becomes a `dyn Trait` where one is
expected: it moves to the heap, next to a table of its type's functions.
Calling a method looks the function up in that table:

```jihoo
trait Shape {
    fn area(self) -> i64
    fn grow(inout self, k: i64)
}

impl Shape for Square { ... }
impl Shape for Rect { ... }

fn total(shapes: [dyn Shape]) -> i64 {
    var t = 0
    for s in shapes {
        t += s.area()
    }
    t
}

fn main() {
    var shapes = Vec(dyn Shape).new()
    shapes.push(Square { side: 2 })          // moved into a `dyn Shape`
    shapes.push(Rect { w: 2, h: 3 })
    shapes[0].grow(3)                         // `inout self`: `shapes` is a `var`
    println(total(shapes.as_slice()))
    var one: dyn Shape = Square { side: 5 }
    one = Rect { w: 1, h: 1 }                 // the square is dropped
}
```

A call borrows the `dyn` value for its duration, shared for `self` and
mutably for `inout self`, as a method call on the value itself would; the
[borrow rules](borrowing.md) apply to it and to the arguments. Default
methods of the trait work. Generic code can make one from a type parameter:

```jihoo
fn erase(comptime T: Shape, sink x: T) -> dyn Shape { x }
```

A trait's methods can be called through `dyn` when:

- they take `self` or `inout self` (a method that takes `sink self`, or no
  `self`, is left out of the table);
- their parameters and result do not name `Self` or the trait's associated
  types, which differ between the types behind the `dyn`;
- they have no compile-time parameters, and return a value, not a borrow.

A trait with parameters cannot be `dyn` yet. A type that holds borrows (a
view) cannot become a `dyn` value, since the value would outlive what it
borrows.

## `dyn fn`

A closure written where a `dyn fn` is expected owns what it uses: each
captured variable moves into it (or is copied, if it is plain). It can be
returned, stored and called later:

```jihoo
fn adder(n: i64) -> dyn fn(i64) -> i64 {
    fn(x) { x + n }
}

struct Button {
    label: String
    on_click: dyn fn(i64) -> String
}

fn main() {
    let add5 = adder(5)
    println(add5(10))                         // 15
    let suffix = String.from("!")
    let b = Button { label: String.from("ok"), on_click: fn(n) { n.to_string() + suffix.as_str() } }
    // `suffix` moved into the closure
    var fs = Vec(dyn fn(i64) -> i64).new()
    fs.push(adder(1))
    fs.push(double)                           // a named function
}
```

Parameter types follow parameter conventions, as for `fn` types
([closures](closures.md)): `dyn fn(inout Vec(i64))` lends its argument
mutably. A `dyn fn` reads what it captured but cannot change it, so calling
it needs only a shared borrow, from any number of places or threads at
once; share changes through [`std.sync`](threads.md#sharing-changes-atomic-and-mutex)
types. It cannot capture a view (a `str`, a slice, a borrowing closure), and
a closure that already borrows cannot become one: write the closure where
the `dyn fn` is expected.

## Cost

Making a `dyn` value allocates once (nothing for a named function), and
dropping it frees that allocation. A call loads a function from the table
and calls it indirectly, which the optimizer usually cannot inline. Use
generics where the types are known while compiling.

`dyn` values also work during [compile-time evaluation](comptime.md), but
cannot be its result.

## How it works

A `dyn` value is two pointers: to its value on the heap, and to a static
table of functions. The first function drops the value and frees it (it
is `std.mem.dyn_drop` of the value's type); the others are the trait's
methods, in the order the trait declares them, or the closure's body. Each
takes the address of the `dyn` value first, as a closure takes its
environment, so a call is an ordinary closure call.
