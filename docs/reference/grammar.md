# Grammar

The whole syntax of jihoo, as the parser (`crates/jihoo/src/parse.rs`) reads
it. [Syntax](../language/syntax.md) explains it with examples; this page is
the precise version, for checking what parses.

## Notation

```text
x y        x, then y
x | y      x or y
[ x ]      x, or nothing
{ x }      x any number of times, maybe none
"fn"       the token itself
name       an identifier: a letter or `_`, then letters, digits and `_`
sep        a `,`, a `;`, or a newline before the next element
```

## Tokens

- Whitespace is spaces, tabs, `\r` and newlines. The lexer records whether a
  newline came before each token; that is all the parser knows of lines.
- `// ...` to the end of the line; `/* ... */` nests.
- Integers: `123`, `1_000`, `0xff`, `0b1010`, `0o17`. Floats: `1.5`, `2e10`,
  `1.5e-3` (decimal only; `1.` and `.5` are not floats). After a `.`, digits
  are always an integer, so `t.0.1` is two tuple fields.
- `'a'` is one byte (`u8`); `'가'` is an error, since it is more than one byte.
  `"..."` is a string, on one line. Escapes in both: `\n \t \r \0 \\ \' \" \xNN`.
- The keywords:

  ```text
  as break comptime const continue else enum export extern false fn for if
  impl import in inout let loop match move pub ref return sink static struct
  trait true type unsafe var while
  ```

  `self`, `Self`, `null`, `fnptr`, `int`, `never` and the primitive types are
  ordinary names that the compiler gives a meaning to; `_` is a name too,
  except in patterns.
- Some tokens are made of others: `..=` is `..` then `=`, which is how range
  patterns take either spelling.

## Files

```text
module   = { "#![" name "]" } { item | ";" }
item     = { attr } [ "pub" ] ( import | fn | struct | enum | impl | trait
                              | const | static | alias )
attr     = "#[" name [ "(" name { "," name } ")" ] "]"

import   = "import" name { "." name } [ "as" name ]
fn       = [ "unsafe" ] [ "extern" | "export" ] "fn" name params
           [ "->" [ "ref" | "inout" ] type ] [ block ]
params   = "(" [ param { "," param } [ "," ] ] ")"
param    = "..."                                   (last; `extern fn` only)
         | [ "inout" | "sink" | "comptime" ] name [ ":" type { "+" type } ]
struct   = "struct" name [ params ] "{" { [ "pub" ] name ":" type sep } "}"
enum     = "enum" name [ params ] "{" { name [ "(" type { "," type } ")" ] sep } "}"
impl     = "impl" [ params ] type [ "for" type ] "{" { item | ";" } "}"
trait    = "trait" name [ params ] [ ":" type { "+" type } ] "{" { item | ";" } "}"
const    = "const" name [ ":" type ] "=" expr
static   = "static" name [ ":" type ] "=" expr
alias    = "type" name [ "=" type ]
```

- `#![...]` attributes come first in the file; the only one is
  `#![freestanding]`. Item attributes are `#[view]` and `#[derive(...)]`
  (reserved).
- A parameter's type may be left out only for `self`. A function without a
  block is a declaration: an `extern fn`, or a trait function without a
  default body. Items do not nest inside function bodies.
- The parameters of a `struct`, `enum` or `trait` are compile-time ones
  whether or not they say `comptime`: `struct Pair(T: type)`. Those of an
  `impl` are written the same way: `impl(T: Ord) Ord for Vec(T)`.
- `type Item` without `= T` declares an associated type in a trait.

## Types

```text
type     = path [ "(" expr { sep expr } ")" ]      Vec(i64), std.map.Map(K, V)
         | "*" type                                 raw pointer
         | "[" type "]"                             slice
         | "[" type ";" expr "]"                    array
         | "(" ")" | "(" type ")"                   unit; parentheses
         | "(" type "," [ type { "," type } ] ")"   tuple
         | "fn" fn_ty | "fnptr" fn_ty               closure; function pointer
         | ( "ref" | "inout" ) type                 a borrow, as a type argument
         | "type"                                   the type of types
path     = name { "." name }
fn_ty    = "(" [ [ "inout" | "sink" ] type { "," [ "inout" | "sink" ] type } ] ")"
           [ "->" type ]
```

Type arguments are expressions, so a number can be one (`[T; N]`,
`Matrix(f64, 3)`). The `(` of type arguments, and the `->` of a function
type, must be on the same line as what comes before.

## Blocks and statements

```text
block    = "{" { stmt end } [ expr ] "}"
end      = ";" | newline | before "}"
stmt     = ( "let" | "var" | "inout" ) pattern [ ":" type ] "=" expr
         | expr "=" expr
         | expr opassign expr
         | expr
opassign = "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>="
         | "+%=" | "-%=" | "*%="
```

A block whose last statement is an expression with no `;` after it has that
expression's value. The `=` or `op=` of an assignment must be on the same
line as its left side.

## Expressions

```text
expr     = range | binary
range    = [ binary ] ".." [ binary ]               only as a whole expression
binary   = unary { binop unary }                    by precedence, below
         | binary "as" type
unary    = ( "-" | "!" | "*" | "&" | "move" ) unary
         | primary { postfix }
postfix  = "(" [ expr { sep expr } ] ")"            call
         | "[" expr "]"                             index or slice
         | "." name | "." integer                   field, method, tuple field
         | "?"                                      early return on None / Err
         | "{" [ field { sep field } ] "}"          struct literal, after a path
field    = name [ ":" expr ]

primary  = literal | name | "(" ")" | "(" expr ")"
         | "(" expr "," [ expr { "," expr } ] ")"   tuple
         | "[" [ expr { sep expr } ] "]"            array
         | "[" expr ";" expr "]"                    array of copies
         | block | "unsafe" block | "comptime" unary
         | "if" cond block [ "else" ( if | block ) ]
         | "match" cond "{" { pattern [ "if" expr ] "=>" stmt sep } "}"
         | "while" cond block
         | "loop" block
         | "for" [ name "," ] pattern "in" cond block
         | "fn" "(" [ cparam { "," cparam } ] ")" [ "->" type ] block   closure
         | "fn" fn_ty | "fnptr" fn_ty | ( "ref" | "inout" ) type          a type
         | "return" [ expr ] | "break" | "continue"
cparam   = name [ ":" type ]
cond     = expr, where a struct literal cannot start (write `(P { x: 1 })`)
```

### Precedence

From loosest to tightest. Binary operators are left-associative.

| level | operators |
|-------|-----------|
| 0 | `a..b` (a whole expression only) |
| 1 | `\|\|` |
| 2 | `&&` |
| 3 | `== != < <= > >=` (they do not chain: `a < b < c` is an error) |
| 4 | `\|` |
| 5 | `^` |
| 6 | `&` |
| 7 | `<< >>` |
| 8 | `+ - +% -%` |
| 9 | `* / % *%` |
| 10 | `e as T`, which applies to the operand just before it |
| 11 | prefix `- ! * & move` |
| 12 | postfix `f(x) a[i] a.b t.0 e? P { ... }` |

So `c as i64 * 2` is `(c as i64) * 2` and `-x as u64` is `(-x) as u64`.
Unlike C, the bitwise operators are tighter than comparisons, as in Rust:
`a & mask == 0` is `(a & mask) == 0`. Shifts are looser than `+`:
`1 << 2 + 1` is `1 << 3`.

### Lines

A statement ends at a newline, unless the expression cannot end there. The
rules:

- A binary operator continues the expression only at the end of a line,
  not at the start of the next one. `a\n+ b` is `a`, then the statement
  `+ b`, which is an error.
- A `.` continues the expression from either line, so method chains may
  start each line with `.method()`.
- `(`, `[` and `?` at the start of a line do not apply to what came before:
  `f\n(x)` is `f`, then `(x)`.
- `as`, `..`, `=` and `op=` must be on the line of their left side.
- `return` takes a value only on its own line: `return\nx` returns nothing.
- Inside `( )`, `[ ]` and `{ }` lists (arguments, arrays, struct fields,
  enum variants, `match` arms), a newline separates elements like a comma.

### Closures and types

`fn(...)` starts a closure when a block follows, and is a type otherwise:
`fn(x, y: i64) { ... }` is a closure (parameter types are optional),
`fn(i64) -> bool` is a type, written where a value is expected only as a
compile-time argument.

### Struct literals

After a path (`P`, `m.P`, `Pair(i64)`), a `{` on the same line starts a
struct literal if it is followed by `}`, by `name:`, by `name,` or by
`name }`. In the head of `if`, `while`, `match` and `for` it never does, so
the `{` there is the body; put a struct literal there in parentheses.

## Patterns

```text
pattern  = single { "|" single }
single   = "_"
         | [ "-" ] integer | char                    a literal
         | lit ".." [ "=" ] lit                      a range, both ends included
         | "true" | "false" | string
         | name                                      binds, or a variant without payload
         | "var" name                                a binding that can change
         | "(" pattern { "," pattern } ")"           tuple
         | path "(" [ pattern { "," pattern } ] ")"  variant with payload
         | path "{" { name [ ":" pattern ] sep } [ ".." ] "}"   struct
lit      = [ "-" ] integer | char
```

- A range pattern includes both ends whichever way it is written: `0..9`
  and `0..=9` both match 9. (A range *expression*, `0..9` in a `for` loop
  or a slice, leaves out its end.)
- A single name is a variant if the matched type has a variant of that name
  without payload (`Stop`, `None`); otherwise it binds.
- `A | B` alternatives cannot bind names.
