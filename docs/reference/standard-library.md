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
| `print(x)`, `println(x)`, `eprintln(x)` | anything with `Show` (integers, `bool`, `str`, `String`; not floats or `Vec` yet), to standard output (error) |
| `sort(&v)`, `sort_by(&v, less)` | a stable merge sort of a `Vec` |
| `is_space`, `is_digit`, `is_alpha` | on bytes |

## `Vec(T)`

A growable array. `Vec(T).new()`, `with_capacity(n)`, `Vec.filled(n, x)`;
`len`, `is_empty`, `capacity`, `push`, `pop`, `insert`, `remove`, `swap`,
`truncate`, `clear`, `extend`, `reverse`, `reserve`, `resize`, `first`,
`last`, `as_slice`, `iter`; `v[i]` (bounds-checked). `Clone` and `Eq` when
`T` has them. `for x in v` borrows each element; `for x in v.into_iter()`
owns each one (`into_iter` takes the `Vec`; the values a loop that stops
early does not reach are dropped with it).

## Iterators

`import std.iter` enables `IteratorExt` for every `Iterator`: `map`,
`filter`, `take`, `zip`, `fold`, `for_each`, `count`, `any` and `all`.
Slices gain `.iter()`, and `iter.range(start, end)` supplies a half-open
`i64` range. Adapters are lazy and own their input iterator; callbacks
borrow their captures. See [Iterator pipelines](../language/iterators.md)
for execution order, ownership and compile-time use.

## `String` and `str`

`str` is a borrowed view of UTF-8 bytes; `String` owns its bytes. A string
literal is a `str`, or a `String` where one is expected (without copying
until it changes). A `str` passed where a `String` is borrowed is lent
without copying.

`String`: `new`, `with_capacity`, `from(s)`, `len`, `is_empty`, `as_str`,
`push(byte)`, `push_str`, `clear`, `into_bytes`; `+` and `+=` with a `str`;
`==` and `<` with other strings.

`str` (and slices) have the fields `len` and `ptr`, not methods: `s.len`.
`str`: `s[i]` (a byte), `s[a..b]` (a part), `to_string`,
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
| `std.iter` | lazy iterator adapters, consumers, slice iteration and `range` |
| `std.thread` | `join(a, b)`, `each(lo, hi, f)`, `map(xs, f)`, `each_mut(&v, f)`, `cpu_count()`: work on several threads that borrows from the caller ([threads](../language/threads.md)) |
| `std.sync` | `Atomic(T)` (`new`, `load`, `store`, `add`, `sub`, `swap`, `compare_swap`, `into_inner`) and `Mutex(T)` (`new`, `lock(f)`, `into_inner`), shared by threads ([threads](../language/threads.md#sharing-changes-atomic-and-mutex)) |
| `std.derive` | the bodies of `#[derive(...)]`d methods, loaded by the compiler when an item derives a trait ([derive](../language/reflection.md#derive)) |
| `std.mem` | `alloc`, `realloc`, `dealloc` (unsafe); `replace`, `swap`, `take`; `drop_at` |
| `std.fs` | `read_file(path) -> Result(String, String)`, `write_file(path, text)`, `remove_file(path)`, `read_dir(path) -> Result(Vec(String), String)` (sorted names) |
| `std.env` | `args() -> Vec(str)`, `get(name) -> Option(str)`, `environ()` |
| `std.process` | `run(program, args) -> Result(Exit, String)`, which waits; `Exit` is `Code(i32)` or `Signal(i32)`, with `success()`; `output(program, args) -> Result(Output, String)` also keeps what the program writes (`Output { status, stdout, stderr }`, its standard input empty); `find(program)` looks in `PATH` |
| `std.sys` | the operating system: `write_fd`, `read_fd`, `open_read`, `open_write`, `close`, `spawn`, `spawn_io` (with the child's standard streams), `pipe`, `poll`, `wait`, `exit`, `abort`, and the allocator under `mem` |
| `std.libc` | C library declarations (native programs) |
| `std.ffi` | native Linux `Library.open`/`symbol` (unsafe), `c_string`, `copy_c_string` (unsafe), and C integer aliases; see [C interoperation](../language/unsafe.md#shared-libraries-and-c-strings) |
| `std.sysno` | Linux system call numbers for the target |
