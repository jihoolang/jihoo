# Standard library

The library lives in `lib/std/` and is written in jihoo. The prelude
(`std.prelude`) and the modules it imports with `pub import` are seen
everywhere; the others are imported (`import std.fs`).

## Prelude

| name | what |
|------|------|
| `Option(T)` | `Some(T)` or `None`: `is_some`, `is_none`, `unwrap`, `expect`, `unwrap_or` |
| `Result(T, E)` | `Ok(T)` or `Err(E)`: `is_ok`, `is_err`, `unwrap`, `expect`, `ok`, `err` |
| `Ordering` | `Less`, `Equal`, `Greater` |
| `Clone`, `Eq`, `Ord`, `Hash`, `Show`, `Default`, `Drop`, `Iterator` | the [standard traits](../language/generics.md#standard-traits) |
| `Plain`, `Int`, `Signed`, `Unsigned`, `Float`, `Number` | marker traits the compiler implements |
| `panic(msg)` | stops the program |
| `assert(cond, msg)` | panics when `cond` is false |
| `drop(x)` | destroys `x` now |
| `min(a, b)`, `max(a, b)` | by `Ord` |
| `print(x)`, `println(x)`, `eprintln(x)` | anything with `Show` (integers, floats, `bool`, `str`, `String`; not `Vec` yet), to standard output (error) |
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

`import std.utf8` adds `s.chars()`, an iterator of `Result(u32, String)`
Unicode scalar values. Invalid UTF-8 yields one error, then ends iteration.
`utf8.decode(s, byte_offset)` returns `(scalar, byte_width)` or an error;
`utf8.validate(s)` checks the whole string. `utf8.is_whitespace(scalar)`
recognizes Unicode White_Space; byte-oriented `is_space` keeps its meaning.

## Files and errors

`std.os` reports what the operating system says. `os.Error` has one variant
per error number (errno) that programs commonly handle: `NotPermitted`,
`NotFound`, `Interrupted`, `Io`, `BadDescriptor`, `WouldBlock`,
`OutOfMemory`, `PermissionDenied`, `Busy`, `AlreadyExists`,
`NotADirectory`, `IsADirectory`, `InvalidInput`, `TooManyOpenFiles`,
`NoSpace`, `ReadOnly`, `BrokenPipe`, `NameTooLong` and `NotEmpty`;
`Other(code)` holds any other number. Two variants are not error numbers:
`UnexpectedEof` (the input ended before what was asked for) and
`InvalidData` (such as invalid UTF-8). `Error.from_code(n)` and `code()`
convert (`code()` is 0 for the last two), `message()` is the C library's
wording, and `Show` prints `No such file or directory (os error 2)`. `==`
compares variants and numbers.

`os.File` owns a descriptor and closes it when dropped; `os.stdin()`,
`stdout()` and `stderr()` borrow the standard streams without closing them.
`File.open(path)` reads, `create(path)` writes a new or emptied file,
`append(path)` writes at the end, and `open_with(path, flags, mode)` takes
`os.READ`, `WRITE`, `READ_WRITE`, `CREATE`, `EXCLUSIVE`, `TRUNCATE`,
`APPEND` and `NONBLOCK`. `os.pipe()` returns `(read end, write end)`.
Descriptors are closed in programs `std.process` starts.

Each read and write is one system call, so partial operations, the end of
input, signals and nonblocking descriptors show in the result:

| method | |
|--------|---|
| `read(&buf, max)` | appends at most `max` bytes to a `Vec(u8)`; `Ok(0)` is the end of input |
| `write(data)` | writes some of a `[u8]`; the count may be smaller than `data.len` |
| `read_exact(&buf, n)` | exactly `n` bytes, or `UnexpectedEof` with the bytes read so far left in `buf` |
| `read_to_end(&buf)` | everything up to the end of input |
| `write_all(data)` | every byte, or an error after an unknown amount; use `write` where the amount matters |
| `set_nonblocking(on)` | reads and writes return `WouldBlock` instead of waiting |
| `wait_readable(ms)`, `wait_writable(ms)` | whether the descriptor became ready within `ms` milliseconds (forever if negative) |

`read` and `write` return `Interrupted` when a signal arrives first;
`read_exact`, `read_to_end` and `write_all` retry such calls. `s.as_bytes()`
views a `str` or `String` as `[u8]`. Both profiles behave the same: native
programs go through libc and `errno`, freestanding ones through system calls.

```jihoo
import std.os

fn copy(path: str) -> Result(i64, os.Error) {
    var input = os.File.open(path)?
    var out = os.stdout()
    var buf = Vec(u8).new()
    let n = input.read_to_end(&buf)?
    out.write_all(buf.as_slice())?
    Ok(n)
}
```

`std.fs` reads and writes whole files with the same errors:
`read_file(path) -> Result(String, os.Error)` (bytes not checked to be
UTF-8), `read_bytes`, `write_file(path, text)`, `write_bytes(path, data)`,
`append_bytes`, `remove_file` and `read_dir` (sorted names).

## Buffered input

`std.io.BufRead` supplies `read_line(&out) -> Result(i64, os.Error)`, appending
one UTF-8 line to a `String`, including its newline. The count is in bytes;
zero means end of input. Invalid UTF-8 is `InvalidData`. An error restores
the output's previous length; input already consumed is not restored.

`io.StrReader.new(text)` borrows a string without copying it.
`io.BufReader.open(path)` owns a file and a 64 KiB buffer;
`with_capacity(path, bytes)` chooses a positive buffer size, and
`BufReader.new(file)` reads an open `os.File`, such as `os.stdin()`.
Interrupted reads are retried. Lines may span buffers, and the final line
needs no newline. Both readers work in native and freestanding code. Only
the memory reader can be used during compile-time evaluation.

```jihoo
import std.io
import std.os

fn read() -> Result(i64, os.Error) {
    var input = io.StrReader.new("first\nsecond")
    var line = String.new()
    input.read_line(&line)
}
```

## Formatting

`std.fmt` formats several values with a pattern. The values are a tuple,
or a single value that is not a tuple:

```jihoo
import std.fmt

fn report(name: str, total: f64, change: i64) {
    fmt.println("{:<10} {:>8.2} ({:+})", (name, total, change))
    let line = fmt.format("{1} before {0}", ("b", "a"))   // "a before b"
    fmt.println("{:#010x}", 255)                           // 0x000000ff
}
```

`format(pattern, values) -> String`, `write(&out, pattern, values)`,
`print`, `println` and `eprintln`. `{}` takes the next value and `{N}` the
value at index `N`; `{{` and `}}` are braces. After `:` comes
`[[fill]align][+][#][0][width][.precision][kind]`:

| part | |
|------|---|
| `fill`, `align` | `<` left, `>` right, `^` centered, padded with any one character (a space by default); numbers align right and other values left |
| `+` | a sign on positive numbers too |
| `#` | `0x`, `0o` or `0b` before an integer in that base |
| `0` | pads a number with zeros between its sign or prefix and its digits |
| `width` | the least number of characters (Unicode scalar values) |
| `.precision` | digits after the point of a float, rounded half to even; the most characters of a string |
| `kind` | `x`, `X`, `o`, `b`: an integer in base 16, 8 or 2, negative values as their two's complement bits; `e`: a float with an exponent (`1.2345e3`) |

Values format through the `Format` trait (`fn format(self, inout out:
String, spec: fmt.Spec)`). Integers, floats, `bool`, `str` and `String`
implement it; any other type with `Show` uses its `show` text, padded. A
type can implement `Format` itself, using `fmt.pad` for the width. The
pattern is read when the program runs: a malformed pattern or a placeholder
without a value panics. Formatting works in compile-time code, so
`const S = comptime fmt.format(...)` is a string constant.

`std.float` has the digits beneath: `shortest` (the fewest that read back as
the float), `exact` (a chosen count, rounded half to even), and the text
forms `write_shortest`, `write_fixed` and `write_exponent`, computed with
big integers rather than float arithmetic.

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
| `std.io` | printing and `BufRead`, `StrReader`, `BufReader` for buffered UTF-8 lines |
| `std.fmt` | `format`, `write`, `print`, `println`, `eprintln` with patterns, and the `Format` trait ([formatting](#formatting)) |
| `std.float` | exact decimal digits of floats: shortest, fixed and exponent forms |
| `std.utf8` | strict UTF-8 decoding, validation, scalar iteration and Unicode whitespace |
| `std.thread` | `join(a, b)`, `each(lo, hi, f)`, `map(xs, f)`, `each_mut(&v, f)`, `cpu_count()`: work on several threads that borrows from the caller ([threads](../language/threads.md)) |
| `std.arena` | `Arena(T)` and `Id(T)`, `Pool(T)` and `Handle(T)`, `Soa(T)`: data that refers to data by index ([data by index](../language/data-oriented.md)) |
| `std.sync` | `Atomic(T)` (`new`, `load`, `store`, `add`, `sub`, `swap`, `compare_swap`, `into_inner`), `Mutex(T)` (`new`, `lock(f)`, `into_inner`), `Channel(T)` (`new`, `bounded(n)`, `send`, `recv`, `try_recv`, `close`, `iter`, `len`, `is_closed`) and `Once(T)` (`new`, `get`, `get_or_init(f)`, `into_inner`), shared by threads ([threads](../language/threads.md#sharing-changes-atomic-and-mutex)) |
| `std.os_thread` | `start`, `wait` (unsafe) and `cpu_count`: the threads `std.thread` uses, POSIX threads or `clone` |
| `std.derive` | the bodies of `#[derive(...)]`d methods, loaded by the compiler when an item derives a trait ([derive](../language/reflection.md#derive)) |
| `std.mem` | `alloc`, `realloc`, `dealloc` (unsafe); `replace`, `swap`, `take`; `drop_at`; `dyn_box`, `dyn_drop`, which [`dyn` values](../language/dyn.md) use |
| `std.os` | `Error` (errno-based), `File` with partial and nonblocking reads and writes, `pipe`, the standard streams ([files and errors](#files-and-errors)) |
| `std.fs` | `read_file`, `read_bytes`, `write_file`, `write_bytes`, `append_bytes`, `remove_file`, `read_dir`, failing with `os.Error` |
| `std.env` | `args() -> Vec(str)`, `get(name) -> Option(str)`, `environ()` |
| `std.process` | `run(program, args) -> Result(Exit, String)`, which waits; `Exit` is `Code(i32)` or `Signal(i32)`, with `success()`; `output(program, args) -> Result(Output, String)` also keeps what the program writes (`Output { status, stdout, stderr }`, its standard input empty); `find(program)` looks in `PATH` |
| `std.sys` | the operating system: `write_fd`, `read_fd`, `open_read`, `open_write`, `close`, `spawn`, `spawn_io` (with the child's standard streams), `pipe`, `poll`, `wait`, `exit`, `abort`, the allocator under `mem`, and `*_raw` calls returning `-errno` that `std.os` uses |
| `std.libc` | C library declarations (native programs) |
| `std.ffi` | native Linux `Library.open`/`symbol` (unsafe), `c_string`, `copy_c_string` (unsafe), and C integer aliases; see [C interoperation](../language/unsafe.md#shared-libraries-and-c-strings) |
| `std.sysno` | Linux system call numbers for the target |
