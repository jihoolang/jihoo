# Unsafe code and C

Code inside `unsafe { ... }`, and the body of an `unsafe fn`, may do what
the compiler cannot check. Safe code that only calls safe functions cannot
corrupt memory; unsafe code must make sure of that itself. The standard
library's `Vec`, `String`, `Map` and `Box` are built this way.

## Raw pointers

`*T` is a raw pointer. Making one is safe: `&place` gives the address of a
variable, field or element. Using one is not:

```jihoo
var buf = [0; 4]
let p = &buf[0]          // *i64
unsafe {
    *p = 2               // write through it
    *(p + 3) = 5         // pointer arithmetic, in elements
}
```

In `unsafe` code:

| | |
|---|---|
| `*p`, `p[i]`, `p.field` | the place `p` points to |
| `p + n`, `p - n` | `n` elements on |
| `null` | the null pointer, where a pointer type is expected |
| `read(p)`, `write(p, v)` | move a value out of, or into, memory, without running destructors |
| `mem_copy(dst, src, n)`, `mem_fill(p, byte, n)` | copy `n` elements, fill bytes |
| `make_slice(p, n)`, `make_str(p, n)` | a view of `n` elements at `p` |
| `syscall(n, args...)` | a Linux system call |
| atomics | `atomic_load`, `atomic_store`, `atomic_swap`, `atomic_add`, ..., `atomic_cas`, `fence` |

See [Builtins](../reference/builtins.md) for all of them.

## Globals

`static NAME: T = value` declares a global variable, initialized with a
constant (or `zeroed(T)`). Every use is in `unsafe` code, since any part of
the program may change it.

```jihoo
static COUNTER: i64 = 0

fn next_id() -> i64 {
    unsafe {
        COUNTER += 1
        COUNTER
    }
}
```

## Calling C

`extern fn` declares a C function; calling it is unsafe. Arguments and
results are integers up to 64 bits, floats, `bool`, raw pointers and scalar
`fnptr` types; `...` accepts more arguments with
C's promotions. A string literal passed where `*u8` is expected is a C
string: literals end with a zero byte.

```jihoo
extern fn printf(fmt: *u8, ...) -> i32

fn main() {
    unsafe { printf("%d apples\n", 3) }
}
```

`std.libc` declares the common C functions. Object files, C sources and
`-l` libraries given to `jihoo build` are linked in.

`export fn` makes a function callable from C under its own name.

To build a C-callable object without a jihoo `main`:

```sh
jihoo emit-obj --lib api.jh -o api.o
cc caller.c api.o -lm -ldl -o caller
cc -shared api.o -lm -ldl -o libapi.so
```

The object uses PIC. Link any other libraries required by `api.jh` too.

Parameters use the ordinary `name: T` syntax, without `inout`, `sink` or
`comptime`. Results may also be `()` or `never`. Jihoo views, closures,
borrow types, 128-bit integers and aggregates by value are rejected at the C boundary.
Pass a struct by raw pointer instead; jihoo structs have C field order,
padding and alignment on the supported Linux targets. For callbacks,
use `export fn` with a matching scalar `fnptr` signature. C variadic
arguments promote `bool` and integers smaller than 32 bits to `i32`,
and `f32` to `f64`.

## Shared libraries and C strings

`std.ffi` provides native Linux shared library loading without a C shim:

```jihoo
import std.ffi

fn main() {
    unsafe {
        let lib = ffi.Library.open("libm.so.6").unwrap()
        let cos = lib.symbol("cos").unwrap() as fnptr(f64) -> f64
        println(cos(0.0) as i64)  // 1
    }
}
```

Loading is unsafe because libraries run initializers. `symbol` is unsafe:
the caller must cast the address to the exact C signature and keep the
library alive until every use of that address finishes. Dropping a
`Library` closes its loader handle; copying a raw address does not keep
the library loaded. Libraries must not retain pointers or callbacks
beyond the lifetime of the pointed-to data or code.

`ffi.c_string(text)` returns an owned `String` with a trailing zero and
rejects embedded zero bytes. Keep that string alive while C uses its
`as_str().ptr`. `unsafe { ffi.copy_c_string(p) }` copies a readable,
zero-terminated C string into a jihoo `String`. The module also defines
Linux C aliases `c_schar`, `c_uchar`, `c_int`, `c_uint`, `c_long`, `c_ulong`
and `size_t`.

## Unsafe functions

`unsafe fn f()` may only be called in unsafe code, and its body is unsafe.
Mark a function unsafe when calling it wrong could corrupt memory, such as
`mem.alloc`.
