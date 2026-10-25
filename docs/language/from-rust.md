# Coming from Rust

jihoo looks like Rust and shares many of its ideas, so the places where it
differs are easy to miss. This page lists them: read it before writing jihoo
if you know Rust, and check here when code that "should work" does not. The
[Grammar](../reference/grammar.md) is the exact syntax.

## Side by side

| Rust | jihoo |
|------|-------|
| `Vec<i64>`, `HashMap<K, V>` | `Vec(i64)`, `Map(K, V)` |
| `fn f<T: Ord>(x: &T)` | `fn f(comptime T: Ord, x: T)` |
| `impl<T: Clone> Clone for Box<T>` | `impl(T: Clone) Clone for Box(T)` |
| `struct Pair<T> { a: T }` | `struct Pair(T: type) { a: T }` |
| `Vec::new()`, `Shape::Circle(r)` | `Vec.new()`, `Shape.Circle(r)` (no `::`) |
| `Vec::<u8>::new()` | `Vec(u8).new()` |
| `let mut x = 0;` | `var x = 0` (no semicolons needed) |
| `x: &T` | `x: T` (borrowing is the default) |
| `x: &mut T`, call `f(&mut x)` | `inout x: T`, call `f(&x)` |
| `x: T` (moves) | `sink x: T` |
| `&mut self`, `self` | `inout self`, `sink self`; plain `self` borrows |
| `-> &T` (a part of the first argument) | `-> ref T`; `-> inout T` for `&mut T` |
| `\|x\| x + 1` | `fn(x) { x + 1 }` |
| `impl Fn(i64) -> bool` | `fn(i64) -> bool` (a borrowed closure) |
| `fn(i64) -> i64` (a pointer) | `fnptr(i64) -> i64` |
| `usize`, `char` | `i64` for lengths and indices; `u8` for bytes (`'a'` is a `u8`) |
| `0..=n` in a `for` | `0..n + 1` (`..=` exists only in patterns) |
| `if let Some(x) = o { ... }` | `match o { Some(x) => ..., None => {} }` |
| `while let Some(x) = it.next()` | `loop { match it.next() { Some(x) => ..., None => break } }` |
| `format!("{} {}", a, b)` | `a.to_string() + " " + b.to_string()`, or `show` into a `String` |
| `println!("{}", x)` | `println(x)` (one argument, with `Show`) |
| `#[derive(Clone, PartialEq)]` | write the `impl` by hand |
| `Self::new()` | `Self.new()` or `Type.new()` |
| `x.len()` on `&str`, `&[T]` | `x.len`: a field on `str` and slices; `v.len()` on `Vec`, `String`, `Map` |
| `unsafe { *p }`, `p.add(n)` | `unsafe { *p }`, `p + n` (in elements) |
| `std::ptr::null()` | `null`, where a pointer type is expected |
| `std::mem::take(&mut x)` | `mem.take(&x)` (after `import std.mem`) |
| `loop { break 5 }` | not possible: `break` takes no value |

## What does not exist

- No `if let`, `while let`, `let else`, labeled loops or `break value`. Use
  `match` and flags.
- No macros. `println`, `print`, `panic` and `assert` are functions.
- No string formatting. Build text with `+` and `to_string()`, or call
  `show(&out)` on each part.
- No items inside function bodies: helper functions go at the top level.
- No `mut` keyword (`var` instead), no `&T`/`&mut T` types, no lifetimes,
  no `dyn`, no trait objects. Traits are resolved at compile time only.
- No `Copy` trait to opt into: a type made only of plain parts copies by
  itself ([Values and ownership](ownership.md)).
- No overloading of `/`, `%` or the bitwise operators. `==`/`!=` call `eq`,
  `<`/`<=`/`>`/`>=` call `compare`, `+ - *` call `add`/`sub`/`mul`, and
  `+=`/`-=` call `add_assign`/`sub_assign`.
- No `char`: text is UTF-8 bytes, and `'가'` is an error because it is more
  than one byte.
- No default or named arguments, no variadic functions except `extern fn`.

## Ownership differences

**`let x = place` borrows.** `let name = person.name` does not move or copy
the field: `name` is a borrow, and `person` cannot change while `name` is
used. `var name = person.name` moves (and fails for a field, see below);
`.clone()` copies. In Rust the same line would move or copy.

```jihoo
var v = Vec(String).new()
v.push("a")
let first = v[0]          // borrows v[0]
v.push("b")               // error: `v` is changed here while it is borrowed
println(first)
```

**`&x` is not a shared borrow.** Shared borrowing happens by itself
(`f(x)` lends `x`). `&x` means two things: an argument for an `inout`
parameter (`f(&x)`), and, outside calls, a raw pointer `*T` to a place.
The `&` is required for `inout` arguments: it shows the reader that `x`
may change. A method call `x.push(1)` passes `self` without it.

**Moving out of a field is an error.** Only a whole variable can be moved.
For a field, an element or anything behind a borrow, use `.clone()`,
`mem.take(&x.f)` or `mem.replace(&x.f, new)`:

```jihoo
var t = a.s                       // error: cannot move a part of `a`
let t = mem.replace(&a.s, String.new())
```

**`+` on a `String` variable moves it** when it can: `let b = a + "y"`
leaves `a` moved away. When `a` is borrowed (a parameter, a field) the
compiler copies its text instead. Write `a.as_str() + "y"` to keep `a`.

**A value with a `Drop` impl cannot be taken apart.** `match f { F { fd }
=> ... }` is an error when `F` has `Drop`; read its fields instead.

**Views are not stored in ordinary data.** `str`, `[T]`, closures, `ref T`
are views. A struct holding one becomes a view itself: it can be a local
and be returned, but the compiler tracks what it borrows, as it would a
Rust struct with a lifetime parameter, without the annotation
([Borrowing](borrowing.md#views)).

## Pattern differences

- **Range patterns include their end**, whichever way they are written:
  `'0'..'9'` and `'0'..='9'` both match `'9'`. A range expression
  (`for i in 0..9`, `s[0..9]`) leaves the end out.
- A bare name is a variant if the matched type has a payload-less variant of
  that name, and a binding otherwise. There is no `Tok::Eq` vs `eq`
  distinction by case: `Eq =>` matches the variant `Eq` if `Tok` has one.
- Variants are written alone when the type is known (`Circle(r)`), or as
  `Shape.Circle(r)`; `Some`, `None`, `Ok` and `Err` always work alone.
- `A(x) | B(x)` is an error: alternatives cannot bind names.
- A `match` arm's body may be a statement: `Run(c) => c += 1`. Arms are
  separated by newlines or commas.
- `match &x` lets the arms change what they bind. A plain `match x` on a
  place borrows the parts it binds; on a new value (a call's result) it
  moves them out.

## Equality and printing

- `==` needs an `Eq` impl, even for an enum without payloads or a tuple.
  Compare such values with `match`, or write `impl Eq for T`.
- `String == str` and `str == String` both work.
- `print`/`println` need `Show`: integers, `bool`, `str` and `String` have
  it. Floats, `Vec`, `Option` and tuples do not; convert first
  (`(x as i64).to_string()`) or write a `Show` impl.

## Line breaks matter

Statements end at a newline. An expression continues onto the next line only
after a binary operator, or before a `.`:

```jihoo
let total = a +           // continues
    b
let s = text
    .trim()               // continues: a line may start with `.`
let bad = a
    + b                   // error: `+ b` is a new statement
```

`(`, `[` and `?` at the start of a line do not apply to the line before, and
`return` followed by a newline returns nothing.

In the head of `if`, `while`, `match` and `for`, `P { x: 1 }` is not a
struct literal; write `(P { x: 1 })`.

## Generics

- Type parameters are ordinary parameters marked `comptime`, listed with the
  others; callers may leave them out when they can be inferred
  (`largest(xs)`) or pass them first (`fill(u8, 4, 0)`). Integer
  parameters work the same way: `comptime N: i64`.
- Several bounds: `comptime T: Ord + Hash`.
- Bodies are checked per instance, like C++ templates and Zig, so an error
  in a generic function names the instance (`note: in the instance ...`).
- `impl(T: Number) Ord for T` gives every number type an impl at once; the
  marker traits are `Plain`, `Int`, `Signed`, `Unsigned`, `Float`, `Number`.
- Inherent impls work on any type, built-in ones too: the standard library
  has `impl str { ... }`.

## Integers

- Integer types never convert by themselves; `as` converts (truncating,
  extending, saturating for floats). `as` binds tighter than every binary
  operator: `c as i64 * 2` is `(c as i64) * 2`.
- Overflow traps in debug builds, wraps with `--release`. `+% -% *%` always
  wrap. Unsigned values cannot be negated: write `0 -% x`.
- Literals take the type the context expects (`let b: u8 = 200`), else
  `i64`. `int` is another name for `i64`.

## A translation

```rust
// Rust
fn count_words(text: &str) -> HashMap<String, usize> {
    let mut counts = HashMap::new();
    for w in text.split(' ') {
        if w.is_empty() { continue; }
        *counts.entry(w.to_string()).or_insert(0) += 1;
    }
    counts
}
```

```jihoo
// jihoo
fn count_words(text: str) -> Map(String, i64) {
    var counts = Map(String, i64).new()
    for w in text.split(" ") {
        if w.len == 0 {
            continue
        }
        match counts.get_mut(w) {
            Some(n) => n += 1
            None => {
                counts.insert(w.to_string(), 1)
            }
        }
    }
    counts
}
```
