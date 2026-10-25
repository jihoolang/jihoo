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
results are numbers, `bool` and pointers; `...` accepts more arguments with
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

## Unsafe functions

`unsafe fn f()` may only be called in unsafe code, and its body is unsafe.
Mark a function unsafe when calling it wrong could corrupt memory, such as
`mem.alloc`.
