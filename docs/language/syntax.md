# Syntax

This page explains the syntax with examples; [Grammar](../reference/grammar.md)
is the exact version, and [Coming from Rust](from-rust.md) lists where jihoo
differs from what Rust would suggest.

## Files and items

A file is a module: imports, then items in any order. Items are `fn`,
`struct`, `enum`, `impl`, `trait`, `const`, `static` and `type` aliases;
`pub` makes one visible to other modules.

```jihoo
import std.fs

pub const LIMIT: i64 = 100

pub fn main() {
    ...
}
```

## Statements

A statement ends at the end of its line, at `;` or at `}`. An expression
goes on to the next line only after an operator (or before a `.`, for
method chains):

```jihoo
let total = first +
    second
let s = text
    .trim()
```

A block `{ ... }` is an expression: its value is its last expression, if it
ends with one. `if`, `match`, `loop` and blocks can all give values.

```jihoo
let sign = if x < 0 { -1 } else { 1 }
```

The value of a block that is expected to give nothing is thrown away, so a
function returning `()` can end with a call that returns something.

## Comments and literals

`//` comments to the end of the line, `/* */` comments nest.

| literal | type |
|---------|------|
| `42`, `1_000`, `0xff`, `0b1010`, `0o17` | the integer type expected, else `i64` |
| `1.5`, `2e10` | `f64`, or `f32` where one is expected |
| `'a'`, `'\n'` | `u8` (a byte) |
| `"text"` | `str`; a `String` where one is expected, without copying |
| `true`, `false` | `bool` |

Escapes are `\n \t \r \0 \\ \' \" \xNN`.

## Keywords

```text
as break comptime const continue else enum export extern false fn for if
impl import in inout let loop match move pub ref return sink static struct
trait true type unsafe var while
```

## Operators

From loosest to tightest:

| operators | |
|-----------|---|
| `\|\|` | or, short-circuit |
| `&&` | and, short-circuit |
| `== != < <= > >=` | comparisons (they do not chain) |
| `\|` | bitwise or |
| `^` | bitwise xor |
| `&` | bitwise and |
| `<< >>` | shifts |
| `+ - +% -%` | `+%` and `-%` wrap around |
| `* / % *%` | `*%` wraps around |
| `as` | conversion |
| `- ! * &` `move` | prefix: negation, not, dereference, address, move |
| `f(x) a[i] a.b t.0 e?` | postfix |

`a += b` and the other `op=` forms update a place. On library types, `==`
calls `eq`, `<` and friends call `compare`, `+` calls `add`, and `+=` calls
`add_assign` ([Generics and traits](generics.md)).
