# Structs, enums and patterns

## Structs and tuples

```jihoo
struct Point {
    x: f64
    y: f64
}

let p = Point { x: 1.0, y: 2.0 }

let t = (1, "two")
println(t.1)
```

Fields are given by name; `Point { x, y }` takes them from variables of the
same names. Fields are private to the module unless marked `pub`. Methods
go in `impl` blocks:

```jihoo
impl Point {
    pub fn origin() -> Point { Point { x: 0.0, y: 0.0 } }   // Point.origin()
    pub fn len(self) -> f64 { sqrt(self.x * self.x + self.y * self.y) }
    pub fn scale(inout self, k: f64) { self.x *= k; self.y *= k }
}
```

Structs are laid out like C structs: fields in order, each at its natural
alignment.

## Enums

Variants may carry values. A variant is written `Type.Variant`, or alone
where the type is known; `Some`, `None`, `Ok` and `Err` always work alone.

```jihoo
enum Shape {
    Circle(f64)
    Rect(f64, f64)
    Empty
}

let s = Shape.Circle(2.0)
let n: Option(i64) = None
```

A recursive enum puts the inner value in a `Box`:
`Add(Box(Expr), Box(Expr))`. A type that contains itself directly is an
error.

## `match`

`match` tries the arms in order, and must cover every value; an arm that
can never be reached is an error too.

```jihoo
match shape {
    Circle(r) => 3.14 * r * r
    Rect(w, h) if w == h => w * w
    Rect(w, h) => w * h
    Empty => 0.0
}
```

Patterns are `_`, names, literals (integers, bytes, strings, `true`),
ranges `1..=9`, alternatives `A | B` (each binding the same names), tuples,
variants `Some(x)`, and structs `Point { x, y: 0.0 }` or `Point { x, .. }`.
Patterns see through `Box`: `Add(Num(a), b)`.

A range pattern includes its end however it is written: `1..9` and `1..=9`
both match 9, while the range `0..n` of a `for` loop stops before `n`.

How bindings get their values:

- On a new value (a call's result), bindings take its parts, moving them.
- On a whole owned variable whose parts the arms bind, the same: the
  variable is used up.
- Otherwise bindings borrow (plain values are copied).
- `match &x` borrows `x` mutably when it can change, so arms can change
  what they bind.
- Patterns look through a borrow held as a value: on an `Option(ref T)`
  (from `v.first()`, `map.get(k)`), `Some(Circle(r))` matches inside the
  `T`, and bindings borrow; on an `Option(inout T)` (`map.get_mut(k)`) they
  can change. A plain name binds the borrow itself.

`let` destructures too, with a pattern that must always match:
`let (a, b) = pair`. With `else`, the pattern may fail to match, and the
block after `else` then runs. It must not finish (`return`, `break`,
`continue`, `panic`), and it does not see the pattern's names:

```jihoo
fn radius(s: Shape) -> f64 {
    let Circle(r) = s else { return 0.0 }
    r
}
```

The names bind as they would in a `match` arm: a borrow of a place, or
the parts of a new value (`let Some(line) = lines.next() else { break }`).

## Loops

```jihoo
for i in 0..n { ... }              // 0 up to n - 1
for x in v { ... }                 // a Vec, slice, array or str, by element
for i, x in v { ... }              // with the index
while cond { ... }
loop { ... break }
```

`for` borrows a collection and gives each element (borrowed, or copied if
plain). A type with `next(inout self) -> Option(T)` is an iterator and is
used up by the loop; a type with `iter()` gives one. To own the elements of
a `Vec`, loop over `v.into_iter()`. A borrow held as a value (a field of
type `ref Vec(T)`) is looped over, and indexed, as what it points to.
