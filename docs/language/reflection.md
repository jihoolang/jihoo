# Reflection and derive

A generic function is checked once for each set of compile-time arguments
(see [Generics](generics.md)). Because of that, code can look at what a
type is made of, its fields or its variants, and the instance for each type
is ordinary code. The compiler checks it like any other code, so moves,
borrows and privacy apply to it. Rust uses macros for this, and Zig uses
`comptime` without memory safety. `#[derive(...)]` is written this way, in
the standard library.

```jihoo
fn sum_fields(comptime T: type, v: T) -> i64 {
    var total = 0
    inline for i in 0..field_count(T) {
        total += field(v, i)
    }
    total
}

struct Point {
    x: i64
    y: i64
}

sum_fields(Point, Point { x: 3, y: 4 })     // 7
sum_fields((i64, i64), (1, 2))              // 3
```

## `inline for` and `inline if`

`inline for i in a..b { ... }` repeats its body once for each `i` from `a`
up to `b`. Both bounds are compile-time integers. In each copy, `i` is a
compile-time constant, as a `comptime` parameter is. It can be a field index,
an array length or a compile-time argument, and its type comes from where
it is used. The body may use `return`; `break` and `continue` belong to an
enclosing runtime loop. The body is repeated at most 65536 times.

`inline if c { ... } else { ... }` takes a compile-time `bool` and compiles
only the branch it selects. The other branch is not checked, so it may
use fields or methods that the type of this instance does not have. An
`else if` after an `inline if` is also `inline`.

```jihoo
inline if is_enum(T) {
    // only for enums
} else if is_struct(T) {
    // only for structs
} else {
    // anything else
}
```

## Describing a type

These builtins take a type and give compile-time constants, so they work in
`inline` bounds and conditions, `const` items and array lengths:

| builtin | |
|---------|---|
| `is_struct(T)`, `is_enum(T)`, `is_tuple(T)` | what kind of type `T` is |
| `field_count(T)` | the fields of a struct or tuple |
| `field_name(T, i)` | field `i`'s name, as a `str` (a tuple's are `"0"`, `"1"`, ...) |
| `variant_count(T)` | an enum's variants |
| `variant_name(T, v)` | variant `v`'s name |
| `variant_field_count(T, v)` | the values variant `v` holds |
| `field_index(T, "name")` | the index of the field with that name |
| `type_name(T)`, `size_of(T)`, `needs_drop(T)` | as before ([builtins](../reference/builtins.md)) |

A function that builds a `String` or `Vec` from them can run while
compiling, and its result is a static `str` or slice
([the compile-time heap](comptime.md#the-heap)):

```jihoo
fn header(comptime T: type) -> String {
    var s = String.new()
    inline for i in 0..field_count(T) {
        if i > 0 { s.push(',') }
        s.push_str(field_name(T, i))
    }
    s
}

const POINT_HEADER: str = header(Point)   // "x,y"
```

Two builtins name a type, so they go where a type is written:

| builtin | |
|---------|---|
| `field_type(T, i)` | the type of field `i` of a struct or tuple |
| `variant_field_type(T, v, j)` | the type of value `j` of variant `v` |

```jihoo
fn first_field(comptime T: type, v: T) -> field_type(T, 0) {
    field(v, 0)
}

make(T, fn(i) { field_type(T, i).default() })     // how `Default` is derived
```

Indices count from 0 in declaration order. An index out of range is a
compile error.

## Naming and building parts

| builtin | |
|---------|---|
| `field(x, i)` | field `i` of the struct or tuple `x`: a place, as `x.name` is |
| `variant_of(x)` | the index of the enum value's variant, an `i64` (at run time) |
| `variant_field(x, v, j)` | value `j` of variant `v` of `x`: a place. If `x` holds another variant, the program stops |
| `make(T, fn(i) { ... })` | a struct or tuple from its fields |
| `make_variant(T, v, fn(j) { ... })` | variant `v` of the enum `T` from its values |

`field(x, i)` is a place: it can be read, borrowed, assigned and changed
(`field(p, 0) += 1`) under the same rules as `p.x`. A `let` binding cannot
be changed through it, and a field cannot be moved out of a value that
stays whole.

The last argument of `make` and `make_variant` is written as a closure with
one untyped parameter. It is not a closure value. Its body is inlined once
for each part, with the parameter a compile-time index, and its value is
that part. The parts may have different types:

```jihoo
let t = make((i64, bool, String), fn(i) {
    inline if i == 0 {
        7
    } else if i == 1 {
        true
    } else {
        "text".to_string()
    }
})
```

Inside an enum's variant, `variant_of` and `inline for` give the shape of a
`match` over every variant:

```jihoo
let v = variant_of(s)
inline for k in 0..variant_count(Shape) {
    if v == k {
        // here `s` holds variant `k`: variant_field(s, k, j) for each j
    }
}
```

## Privacy

Reflection reaches only what the code could name by hand. Another module's
private field cannot be read with `field`, and `make` cannot build a value
whose fields are private there. The one exception is derived code, below:
a type that says `#[derive(Clone)]` allows the derived `clone` to read and
build its private fields, and nothing else.

## `#[derive(...)]`

```jihoo
#[derive(Clone, Eq, Ord, Hash, Show)]
enum Shape {
    Dot(Point)
    Line(Point, Point)
    Empty
}
```

| trait | derived method |
|-------|----------------|
| `Clone` | every field cloned |
| `Eq` | the same variant and equal fields |
| `Ord` | variants in declaration order, then fields in order |
| `Hash` | the variant and the fields' hashes, mixed in order |
| `Show` | `Point { x: 1, y: 2 }`, `Line(Point { ... }, Point { ... })`, `Empty` |
| `Default` | every field's `default()` (structs only) |

The derived methods are written in jihoo, in `std/derive.jh`, with the
builtins above. The compiler only makes `#[derive(Show)]` mean that
`Shape` implements `Show` with that module's `show`. It loads `std.derive`
only when an item derives something.

Each field must implement the trait. If one does not, the error points into
`std/derive.jh` and names the field's type. A generic type derives for every
instance (`Pair(T)` is `Clone` for any `T`). An instance whose field type
lacks the trait fails when the method is used.

`Default` is derived for structs: every field's `default()`.
