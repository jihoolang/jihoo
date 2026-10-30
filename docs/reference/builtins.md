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
| `efi_image()`, `efi_system_table()` | in a [UEFI program](../language/profiles.md#uefi), the image handle and system table the firmware gave it, as `*u8` (see `std.uefi`) |

## Reflection

See [Reflection and derive](../language/reflection.md).

| builtin | |
|---------|---|
| `is_struct(T)`, `is_enum(T)`, `is_tuple(T)` | compile-time `bool`s |
| `field_count(T)`, `field_name(T, i)`, `field_index(T, "name")` | a struct's or tuple's fields (compile-time constants) |
| `field_type(T, i)`, `variant_field_type(T, v, j)` | a part's type, written where a type goes |
| `variant_count(T)`, `variant_name(T, v)`, `variant_field_count(T, v)` | an enum's variants (compile-time constants) |
| `field(x, i)` | field `i` of `x`, as a place |
| `variant_of(x)` | the index of `x`'s variant, as `i64` |
| `variant_field(x, v, j)` | value `j` of variant `v` of `x`, as a place; stops the program if `x` holds another variant |
| `make(T, fn(i) { ... })` | a struct or tuple from its fields; the body is inlined for each `i` |
| `make_variant(T, v, fn(j) { ... })` | variant `v` of `T` from its values |
| `captures_mut(f)` | whether the `comptime` closure parameter `f` captures a variable mutably or captures a closure ([threads](../language/threads.md#checks-that-libraries-write)) |
| `compile_error("...")` | a compile error where an instance reaches it |

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
| `read_volatile(p)`, `write_volatile(p, v)` | one access of exactly the pointee's width, for memory-mapped device registers ([unsafe](../language/unsafe.md#device-registers)) |
