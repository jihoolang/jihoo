# Builtins

Functions the compiler provides. A module may define a function of the same
name, which then hides the builtin.

## Everywhere

| builtin | |
|---------|---|
| `size_of(T)`, `align_of(T)` | bytes, as `i64` (compile-time constants) |
| `type_name(T)` | the type's name, as a `str` |
| `needs_drop(T)` | whether values of `T` have a destructor |
| `trap()` | stops the program at once |
| `forget(x)` | gives up `x` without running its destructor |
| `sqrt`, `floor`, `ceil`, `trunc`, `round`, `abs`, `copysign` | floats (`abs` also on signed integers) |
| `argc()`, `argv()` | the program's arguments, as C has them (see `std.env`) |

## In `unsafe` code

| builtin | |
|---------|---|
| `read(p)` | the value at `p`, moved out (the memory is left as it is) |
| `write(p, v)` | stores `v` at `p` without dropping what was there |
| `mem_copy(dst, src, n)` | copies `n` elements (the ranges may overlap) |
| `mem_fill(p, byte, n)` | sets `n` bytes |
| `make_slice(p, n)`, `make_str(p, n)` | a view of `n` elements at `p` |
| `zeroed(T)` | a value with all bits zero |
| `syscall(n, a, ...)` | a Linux system call with up to 6 arguments; returns `i64` |
| `atomic_load(p)`, `atomic_store(p, v)` | sequentially consistent |
| `atomic_swap`, `atomic_add`, `atomic_sub`, `atomic_and`, `atomic_or`, `atomic_xor` | `(p, v)`, returning the old value |
| `atomic_cas(p, expected, new)` | returns whether it swapped |
| `fence()` | a full memory fence |
