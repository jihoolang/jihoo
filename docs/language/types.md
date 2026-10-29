# Types

| type | values |
|------|--------|
| `bool` | `true`, `false` |
| `i8` `i16` `i32` `i64` `i128` | signed integers; `int` is `i64` |
| `u8` `u16` `u32` `u64` `u128` | unsigned integers |
| `f32` `f64` | IEEE 754 floats |
| `()` | the value of a function that returns nothing |
| `(A, B)` | tuples |
| `[T; N]` | arrays of `N` values |
| `[T]` | a slice: a borrowed view of values in a row |
| `str` | a borrowed view of text (UTF-8 bytes) |
| `Name`, `Name(args)` | structs and enums, maybe generic |
| `fn(A) -> R` | a borrowed closure ([Closures](closures.md)) |
| `fnptr(A) -> R` | a function pointer |
| `*T` | a raw pointer ([Unsafe code](unsafe.md)) |
| `ref T`, `inout T` | borrows, as type arguments (`Option(ref T)`) |
| `never` | what `return`, `panic` and endless loops produce: no value |

`Vec(T)`, `String`, `Map(K, V)`, `Box(T)`, `Option(T)` and `Result(T, E)` are
library types ([Standard library](../reference/standard-library.md)).

## Integers

Integer types never mix implicitly: convert with `as`. A literal takes the
type its context expects. A literal is at most 64 bits
(`0xffff_ffff_ffff_ffff`); build wider values with shifts and `|`:
`(hi as u128) << 64 | lo as u128`.

- `+`, `-` and `*` **trap on overflow** in debug builds (the default) and
  wrap in release builds (`--release`). `+%`, `-%` and `*%` always wrap.
- `/` and `%` round towards zero. Dividing by zero stops the program;
  `MIN / -1` wraps to `MIN`.
- Shifts use the shift amount modulo the width.
- Lengths and indices are `i64`.
- `i128` and `u128` are 16 bytes, aligned to 16, as C's `__int128` on
  both targets. LLVM calls helpers for their division and their conversions
  to and from floats: libgcc's in native programs, the standard library's
  (`std/rt.freestanding.jh`) in freestanding ones.

## Floats

`+ - * /` and `%` (C's `fmod`) follow IEEE 754. Converting a float to an
integer with `as` saturates: NaN becomes 0, and values out of range become
the nearest end.

`println(x)` and `to_string()` write a float as the shortest decimal that
reads back as the same value (`0.1`, `1.0`, `-0.0`, `NaN`, `inf`), with an
exponent below 1e-4 and from 1e16 on (`1e-5`, `1e16`). The digits are
computed exactly, without float arithmetic. [`std.fmt`](../reference/standard-library.md#formatting)
gives a fixed number of digits (`{:.2}`) or an exponent (`{:e}`), rounded
half to even.

## Conversions

`as` converts between integers (truncating or extending), integers and
floats, `bool` to integers, enums without payloads to integers, pointers to
pointers, and pointers to and from `i64`/`u64`.

## Views

`str`, slices, closures and borrows are *views*: they point into values
owned elsewhere. A struct or enum that contains a view, or is instantiated
with one (`Vec(str)`, `Option(ref T)`), is a view too. The compiler follows
what each view borrows and makes sure it is not used after that goes away
([Borrowing](borrowing.md#views)).
