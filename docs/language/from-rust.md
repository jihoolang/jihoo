| `for x in &v` | `for x in v` (borrows) |
| `for x in v` (moves `v`) | `for x in v.into_iter()` |
| `let (mut a, b) = t` | `let (var a, b) = t` |
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
| `impl Fn(i64) -> bool` (a parameter) | `fn(i64) -> bool` (a borrowed closure), or `comptime F: impl fn(i64) -> bool, sink f: F` |
| `-> impl Iterator<Item = i64>`, `-> impl Fn(i64) -> i64` | `-> impl Iterator`, `-> impl fn(i64) -> i64`: the body's type, which callers see |
| `fn(i64) -> i64` (a pointer) | `fnptr(i64) -> i64` |
| `Box<dyn Shape>` | `dyn Shape` (owned; the value moves in where one is expected) |
| `move \|x\| x + n` | `move fn(x) { x + n }`: owns its captures, no allocation |
| `Box<dyn Fn(i64) -> i64>` | `dyn fn(i64) -> i64`, `fn(x) { x + n }` where one is expected |
| `usize`, `char` | `i64` for lengths and indices; `u8` for bytes (`'a'` is a `u8`) |
| `0..=n` in a `for` | `0..n + 1` (`..=` exists only in patterns) |
| `if let Some(x) = o { ... }` | `match o { Some(x) => ..., None => {} }` |
| `while let Some(x) = it.next()` | `loop { let Some(x) = it.next() else { break } ... }` |
| `let Some(x) = o else { return }` | the same; `x` borrows when `o` is a place |
| `format!("{} {:>5.2}", a, b)` | `fmt.format("{} {:>5.2}", (a, b))` (`import std.fmt`): the values are a tuple |
| `println!("{}", x)` | `println(x)` (one argument, with `Show`), or `fmt.println("{} {}", (a, b))` |
| `#[derive(Clone, PartialEq, Debug)]` | `#[derive(Clone, Eq, Show)]`; `Show` prints like `{:?}` without quotes around strings |
| `Self::new()` | `Self.new()` or `Type.new()` |
| `x.len()` on `&str`, `&[T]` | `x.len`: a field on `str` and slices; `v.len()` on `Vec`, `String`, `Map` |
| `unsafe { *p }`, `p.add(n)` | `unsafe { *p }`, `p + n` (in elements) |
| `std::ptr::null()` | `null`, where a pointer type is expected |
| `std::mem::take(&mut x)` | `mem.take(&x)` (after `import std.mem`) |
| `AtomicI64`, `Arc<Mutex<T>>` | `sync.Atomic(i64)`, `sync.Mutex(T)`, borrowed by the threads (no `Arc`) |
| `*m.lock().unwrap() += 1` | `m.lock(fn(n) { n += 1 })`: the value is lent to the closure |
| `UnsafeCell<T>` | a `#[interior]` struct |
| `loop { break 5 }` | not possible: `break` takes no value |

## What does not exist

- No `if let`, `while let`, labeled loops or `break value`. Use `match`,
  or `let pattern = value else { ... }`, whose block must not finish
  (`return`, `break`, `continue`, `panic`).
- No macros. `println`, `print`, `panic` and `assert` are functions, and
  [`std.fmt`](../reference/standard-library.md#formatting) formats several
  values from a tuple. A literal pattern is checked while compiling, as
  `format!`'s is (but a value no placeholder uses is not an error); one
  made while the program runs is read then, and a
  malformed one, or a placeholder without a value, panics instead of
  failing to compile.
- No items inside function bodies: helper functions go at the top level.
- No `mut` keyword (`var` instead), no `&T`/`&mut T` types, no lifetimes.
  [`dyn Trait`](dyn.md) is always owned: there is no `&dyn Trait`, and a
  `dyn fn` or `move fn` cannot change what it captured (no `FnMut`).
- `impl` is not a parameter's type (`f: impl Fn(..)`): write a type
  parameter, `comptime F: impl fn(A) -> R`, and `sink f: F`. A result
  `-> impl Trait` is not opaque: the caller sees the body's type, and its
  `Item`. Each `move fn` has its own type, so two `return`s of different
  closures do not fit one `impl` result; use `dyn fn` for those.
- No `Copy` trait to opt into: a type made only of plain parts copies by
  itself ([Values and ownership](ownership.md)).
- No overloading of `/`, `%` or the bitwise operators. `==`/`!=` call `eq`,
  `<`/`<=`/`>`/`>=` call `compare`, `+ - *` call `add`/`sub`/`mul`, and
  `+=`/`-=` call `add_assign`/`sub_assign`.
- No `char`: text is UTF-8 bytes, and `'가'` is an error because it is more
  than one byte.
- No default or named arguments, no variadic functions except `extern fn`.
- No `#[cfg(test)]`, test modules, `assert_eq!` or `#[should_panic]`.
  [`jihoo test f.jh`](../reference/command-line.md#tests) runs the
  `#[test]` functions of `f.jh` and of the modules it imports outside the
  standard library, each in a process of its own, since a panic stops the
  whole process rather than unwinding. Tests sit next to the code they
  test, private functions included.

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

**Moving out of a field is an error.** Only a whole variable can be moved,
or a part of a new value (`pair().1`, whose other parts are dropped there).
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

**A method called on a `ref T` value is that of the `T`.** A call
returning `ref T` (`v.first().unwrap()`, `map.get(k).unwrap()`) gives a
borrow as a value; `.clone()`, `.len()` or `.to_string()` on it call the
`T`'s methods, as Rust's auto-deref does, so `.clone()` gives a `T` that
no longer borrows `v`. Only a method the `T` lacks is looked up on the
borrow itself.

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
- `A(x) | B(x)` binds `x` from whichever alternative matches, as in Rust;
  every alternative binds the same names with the same types, and a name
  is `var` in all of them or in none. With a guard, `A(x) | B(x) if x > 0`
  tries the guard for each alternative that matches.
- A `match` arm's body may be a statement: `Run(c) => c += 1`. Arms are
  separated by newlines or commas.
- `match &x` lets the arms change what they bind. A plain `match x` on a
  part of something (a field, an element) or on a borrow borrows the parts
  it binds. On a new value (a call's result), or on a whole variable that
  owns a value with a destructor, the arms move the parts out: the variable
  is used up by the `match`, on every path, not only in the arms that bind.
  To keep it on the other paths, decide before the `match`:
  `if is_expr(s) { match s { ... } } else { keep(s) }`.
- `let (a, b) = pair` borrows the parts when `pair` is a variable (like
  every `let x = place`); to take a value apart, `match` it.
- A `match` whose first arm gives a borrowed part is a view of it, as
  `let x = place` is: `let t = match o { Some(t) => t, None => return }`
  borrows the payload when `o` is borrowed, and `o` cannot change while
  `t` is used. Every other arm must then give a place too (not a new
  value), and the `match` cannot be moved out of: `.clone()` in the arms
  makes it owned.
- Patterns see through `ref` and `inout` values, as Rust's default binding
  modes do: `Some(Circle(r))` matches an `Option(ref Shape)`.
- `let Some(v) = m.get(k) else { ... }` keeps `v` a `ref V`, which borrows
  what the call borrowed, the map and the key. A `str` key lent where a
  `String` is borrowed becomes a `String` over the same bytes that lives
  to the end of the block, so `v` can be used after the statement.
- `None` (or another variant) alone as one arm of an `if` takes no type
  from the other arm: `let x: Option(u32) = if c { None } else { y }`.

## Equality and printing

- `==` needs an `Eq` impl, even for an enum without payloads or a tuple.
  Compare such values with `match`, or write `impl Eq for T`.
- `String == str` and `str == String` both work.
- `print`/`println` need `Show`: integers, floats, `bool`, `str` and
  `String` have it. `Vec`, `Option` and tuples do not; derive or write a
  `Show` impl. A float prints the shortest text that reads back as it,
  like Rust's `{:?}`: `1.0`, `0.30000000000000004`, `1e21`.

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
- `i128` and `u128` exist, but a literal is at most 64 bits: write
  `u128::MAX` as `0 -% (1 as u128)` and `1 << 100` for large values.

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
