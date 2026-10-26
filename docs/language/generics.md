# Generics and traits

## Compile-time parameters

A generic parameter is a parameter given at compile time:
`comptime T: type` for a type, `comptime N: i64` for a number. Every set of
compile-time arguments compiles to its own copy of the function, so generic
code costs what hand-written code costs.

```jihoo
fn fill(comptime T: Plain, comptime N: i64, x: T) -> [T; N] {
    [x; N]
}

fn largest(comptime T: Ord, xs: [T]) -> T { ... }

largest([3, 1, 2])            // T = i64, inferred
fill(u8, 4, 0)                // given explicitly
```

Type arguments are inferred from the other arguments, and from the expected
result. They are written explicitly by passing them first, in order.

Structs and enums take parameters the same way, and their instances are
written like calls:

```jihoo
struct Pair(T: type) {
    a: T
    b: T
}

impl(T: Ord) Pair(T) {
    fn larger(self) -> T { if self.a > self.b { self.a.clone() } else { self.b.clone() } }
}

let p = Pair(i64) { a: 1, b: 2 }
var w = Vec(String).new()
let b = Box.new(3)            // Box(i64), from the argument
let v: Vec(u8) = Vec.new()    // from the expected type
```

A generic function's body is checked for each instance, as in Zig: errors
name the instance. Bounds are checked when the instance is made.

Compile-time arguments can call ordinary functions: `fill(u8, factorial(3),
0)`. The compiler interprets the calculation before creating the instance;
see [Compile-time evaluation](comptime.md).

For a callback such as `f: fn(T) -> U`, if `T` is already known, a closure's
input type can be inferred even while `U` is unknown. The compiler checks
the body and uses its result to infer `U`. This allows
[iterator pipelines](iterators.md) such as `.map(fn(x) { x.to_string() })`.

## Traits

A trait is a set of functions a type can provide, with optional default
bodies; `impl Trait for Type` provides them. Calls are resolved at compile
time: there is no dynamic dispatch.

```jihoo
trait Shape {
    fn area(self) -> f64
    fn describe(self) -> String {
        "area " + (self.area() as i64).to_string()
    }
}

impl Shape for Square {
    fn area(self) -> f64 { self.side * self.side }
}
```

Impls can be generic and have bounds: `impl(T: Eq) Eq for Vec(T)`. A
method is looked for first in the type's own impls, then in the traits it
implements. Traits may have associated types (`type Item`, written
`Self.Item`).

### Standard traits

| trait | what it gives |
|-------|---------------|
| `Clone` | `x.clone()` |
| `Eq` | `eq`; `==` and `!=` call it |
| `Ord` | `compare` returning an `Ordering`; `< <= > >=` call it |
| `Hash` | `hash`, for `Map` keys |
| `Show` | `show(inout out: String)`, and `to_string`; `print` uses it |
| `Default` | `T.default()` |
| `Drop` | a destructor |
| `Iterator` | `next`, which `for` uses |

The compiler itself implements the marker traits `Plain` (values that copy),
`Int`, `Signed`, `Unsigned`, `Float` and `Number`, so the standard library can
give all integers `Ord`, `Hash` and `Show` with one impl each:

```jihoo
impl(T: Number) Ord for T { ... }
```

`#[derive(Clone, Eq, Ord, Hash, Show)]` before a struct or enum gives it
those impls, written in the standard library with
[reflection](reflection.md#derive).
