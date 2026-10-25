# Standard library

The library lives in `lib/std/` and is written in jihoo. The prelude
(`std.prelude`) and the modules it imports with `pub import` are seen
everywhere; the others are imported (`import std.fs`).

## Prelude

| name | what |
|------|------|
| `Option(T)` | `Some(T)` or `None`: `is_some`, `is_none`, `unwrap`, `expect`, `unwrap_or` |
| `Result(T, E)` | `Ok(T)` or `Err(E)`: `is_ok`, `is_err`, `unwrap`, `expect`, `ok` |
| `Ordering` | `Less`, `Equal`, `Greater` |
| `Clone`, `Eq`, `Ord`, `Hash`, `Show`, `Default`, `Drop`, `Iterator` | the [standard traits](../language/generics.md#standard-traits) |
| `Plain`, `Int`, `Signed`, `Unsigned`, `Float`, `Number` | marker traits the compiler implements |
| `panic(msg)` | stops the program |
| `assert(cond, msg)` | panics when `cond` is false |
| `drop(x)` | destroys `x` now |
| `min(a, b)`, `max(a, b)` | by `Ord` |
| `print(x)`, `println(x)`, `eprintln(x)` | anything with `Show`, to standard output (error) |
| `sort(&v)`, `sort_by(&v, less)` | a stable merge sort of a `Vec` |
| `is_space`, `is_digit`, `is_alpha` | on bytes |

## `Vec(T)`

A growable array. `Vec(T).new()`, `with_capacity(n)`, `Vec.filled(n, x)`;
`len`, `is_empty`, `capacity`, `push`, `pop`, `insert`, `remove`, `swap`,
`truncate`, `clear`, `extend`, `reverse`, `reserve`, `resize`, `first`,
`last`, `as_slice`, `iter`; `v[i]` (bounds-checked). `Clone` and `Eq` when
`T` has them. `for x in v` borrows each element.

## `String` and `str`

`str` is a borrowed view of UTF-8 bytes; `String` owns its bytes. A string
literal is a `str`, or a `String` where one is expected (without copying
until it changes). A `str` passed where a `String` is borrowed is lent
without copying.

`String`: `new`, `with_capacity`, `from(s)`, `len`, `is_empty`, `as_str`,
`push(byte)`, `push_str`, `clear`, `into_bytes`; `+` and `+=` with a `str`;
`==` and `<` with other strings.

`str`: `len`, `ptr`, `s[i]` (a byte), `s[a..b]` (a part), `to_string`,
`starts_with`, `ends_with`, `find`, `contains`, `trim`, `split`, `lines`,
`parse_int`, `+`; `for b in s` gives bytes.

## `Map(K, V)`

A hash map with open addressing, for keys with `Hash` and `Eq`. `new`,
`len`, `is_empty`, `insert(k, v)` (returns the old value), `get(k)` and
`get_mut(k)` (an `Option` of a borrow), `contains`, `remove`, `keys`;
`m[k]` panics if the key is missing.

## `Box(T)`

A value on the heap: `Box.new(x)`, `unbox`. Field access, method calls and
patterns see through it.

## Modules

| module | |
|--------|---|
| `std.mem` | `alloc`, `realloc`, `dealloc` (unsafe); `replace`, `swap`, `take`; `drop_at` |
| `std.fs` | `read_file(path) -> Result(String, String)`, `write_file(path, text)` |
| `std.env` | `args() -> Vec(str)`, `get(name) -> Option(str)`, `environ()` |
| `std.process` | `run(program, args) -> Result(Exit, String)`, which waits; `Exit` is `Code(i32)` or `Signal(i32)`, with `success()`; `find(program)` looks in `PATH` |
| `std.sys` | the operating system: `write_fd`, `read_fd`, `open_read`, `open_write`, `close`, `spawn`, `wait`, `exit`, `abort`, and the allocator under `mem` |
| `std.libc` | C library declarations (native programs) |
| `std.sysno` | Linux system call numbers for the target |
