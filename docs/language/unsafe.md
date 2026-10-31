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
| `read_volatile(p)`, `write_volatile(p, v)` | access a device register ([below](#device-registers)) |

See [Builtins](../reference/builtins.md) for all of them.

## Device registers

`read(p)` and `write(p, v)` are ordinary memory accesses: the optimizer may
read once where the program reads in a loop, drop a store that a later one
overwrites, or access fewer bytes than the type has. That is wrong for a
memory-mapped device register, where every access is an event. In unsafe
code, `read_volatile(p)` and `write_volatile(p, v)` access such memory:

```jihoo
fn wait_ready(status: *u32) {
    unsafe {
        while (read_volatile(status) & 1) == 0 {}
    }
}

fn ring_twice(doorbell: *u32) {
    unsafe {
        write_volatile(doorbell, 1)
        write_volatile(doorbell, 2)
    }
}
```

Each call is one load or store of exactly the pointee's type, which must be
an integer, float, `bool` or pointer (a struct's registers are accessed one
field at a time). The compiler keeps the number, order relative to other
volatile accesses, and width of these accesses; they become LLVM `volatile`
loads and stores. The pointer must be aligned for its type.

Volatile is not atomic and not a fence: it does not synchronize threads
and does not order ordinary memory accesses around it, nor make the CPU do
so. Use [atomics](../reference/builtins.md#in-unsafe-code) between threads,
and `fence()` where a device needs memory ordered, for example before
ringing a doorbell for a buffer just written (a barrier that `fence()` does
not give, such as one for uncached memory on some machines, needs an
assembly helper). Mapping the device's memory with the right
cache attributes is also the caller's (the kernel's) work.

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

## Changing behind a shared borrow

A shared borrow promises that the value does not change while it lasts, and
the compiler tells LLVM so (`readonly`, `noalias`). A type whose unsafe code
changes it anyway, through `&self.field`, says `#[interior]`:

```jihoo
#[interior]
pub struct Atomic(T: Int) {
    value: T
}

impl(T: Int) Atomic(T) {
    pub fn add(self, v: T) -> T {
        unsafe { atomic_add(&self.value, v) }
    }
}
```

Borrows of such a type, or of anything containing one, carry neither
promise. Such a type is never plain, so it moves instead of copying. Safe
code can share it between threads (see [Threads](threads.md)), so its
author must make every change safe when several threads make it at once,
as `std.sync`'s `Atomic`, `Mutex`, `Channel` and `Once` do.

## Calling C

`extern fn` declares a C function; calling it is unsafe. Arguments and
results are integers through 128 bits, floats, `bool`, raw pointers,
C-compatible `fnptr` types and plain structs by value. Structs may contain
nested structs and fixed arrays of these types. `...` accepts more arguments
with C's promotions. A string literal passed where `*u8` is expected is a C
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
A program defines each such name once. Another module of the same program
may declare it with `extern fn` (to call it without importing the
module's names, as C code would); the declaration must have the same
signature, and calls go to the definition.

To build a C-callable object without a jihoo `main`:

```sh
jihoo emit-obj --lib api.jh -o api.o
cc caller.c api.o -lm -ldl -o caller
cc -shared api.o -lm -ldl -o libapi.so
```

The object uses PIC. Link any other libraries required by `api.jh` too.

Parameters use the ordinary `name: T` syntax, without `inout`, `sink` or
`comptime`. Results may also be `()` or `never`. A struct passed by value
is an independent copy; passing its raw pointer instead lets C use its
original storage. Jihoo structs have C field order, padding and alignment
on both supported Linux targets.

```jihoo
struct Point { x: f64, y: f64 }
extern fn translate(p: Point, dx: f64, dy: f64) -> Point

export fn scale(p: Point) -> Point {
    Point { x: p.x * 2.0, y: p.y * 2.0 }
}
```

The compiler uses the System V AMD64 ABI on x86_64 and AAPCS64 on aarch64;
[UEFI programs](profiles.md#uefi) on x86_64 use the Microsoft x64
convention, where aggregates of 1, 2, 4 or 8 bytes go in one register,
others and 128-bit integers by reference.
It handles integer and floating-point register groups, homogeneous
floating-point aggregates, stack arguments and indirect returns, including
when earlier arguments have exhausted the available registers. `i128`
and `u128` match C's `__int128` and `unsigned __int128`.

For callbacks, use `export fn` with a matching `fnptr` signature, such as
`fnptr(Point) -> Point`. An ordinary named function can also be converted
where a C-compatible `fnptr` is expected; a compiler-generated adapter
borrows its C argument copies when the jihoo function expects borrows.
A closure with no captures can be used where that `fnptr` is expected.
Function pointers with C-compatible value signatures use the C ABI;
jihoo closure and borrow signatures keep the internal calling convention.

C variadic arguments may include structs and 128-bit integers. `bool`
and integers smaller than 32 bits promote to `i32`, and `f32` to `f64`;
struct fields are unchanged. A variadic function pointer retains `...`:

```jihoo
extern fn printf(fmt: *u8, ...) -> i32
fn main() {
    let print: fnptr(*u8, ...) -> i32 = printf
    unsafe { print("%d %.1f\n", 7 as u8, 2.5 as f32) }
}
```

Views, borrowed or owning closures, borrow types, tuples and jihoo enums
cannot cross this boundary by value. Neither can structs with `Drop`,
`#[view]`, `#[interior]` or incompatible fields. C array parameters must
be declared as pointers, and C enum values as the corresponding integer
type. C unions, bit-fields, packed structs, vector types and `long double`
have no direct jihoo type; use a C wrapper exposing supported types for
such interfaces.

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
