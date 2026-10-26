# Roadmap

## Direction

jihoo is memory-safe without lifetimes, and its generics are compile-time
parameters. C and C++ have neither guarantee. Rust has safety but needs
lifetimes and macros. Zig has `comptime` but no safety. Hylo and Mojo share
the parameter conventions. What jihoo can do that none of them do comes from
one rule: **every borrow ends inside the function that made it**. The
roadmap follows from that rule:

- **Safe compile-time code instead of macros.** A generic body is checked
  per instance, so reflection over a type's fields is ordinary code, and
  the borrow kernel checks what it produces. `derive` is library code.
- **Concurrency that borrows.** A closure cannot outlive its scope, so a
  thread started in a scope can borrow the caller's data without `'static`,
  `Arc` or annotations.
- **Data-oriented design as the default.** No stored references means data
  refers to data by index. The compiler is written that way. The standard
  library should make that style the easy one, with typed indices, arenas,
  generational handles and struct-of-arrays layouts built by `comptime`.
- **Errors that fit in one function.** Every borrow error can be explained
  without leaving the function, and the messages should show it.

Features that weaken the rule, such as references stored in ordinary
structs, are out of scope.

## 0.1: the rewrite

Done ([design](redesign.md)):

1. One language and one compiler: a Rust crate writing LLVM IR text, with
   no VM, no garbage collector and no C++ backend.
2. Ownership: moves, explicit copies, destructors and drop flags; `let`,
   `var` and `inout` locals.
3. Borrowing: parameter conventions (`inout`, `sink`), projections
   (`-> ref T`, `-> inout T`), views and their lifetimes, and a borrow
   kernel that checks exclusivity on MIR.
4. Structs, enums, tuples, arrays, slices; `match` with exhaustiveness
   checking; `for` over ranges, collections and iterators.
5. Generics as compile-time parameters, inferred; traits with default
   methods, generic impls and associated types; marker traits from the
   compiler.
6. Closures that borrow, `comptime` closure parameters, function pointers.
7. `Option`, `Result` and `?`; panics.
8. `unsafe`: raw pointers, `static` globals, `extern fn` (with `...`),
   `export fn`, system calls, atomics.
9. The standard library in jihoo: `Vec`, `String`, `Map`, `Box`, sorting,
   files, arguments, the environment, running other programs
   (`std.process`), printing; native and freestanding.
10. x86_64 and aarch64 Linux.
    Native C FFI includes shared libraries (`std.ffi`), scalar callbacks,
    C default argument promotions and checked C signatures. LLVM 21's C
    API handles optimization and object emission in process; clang remains
    an optional comparison backend.
11. Speed: on the benchmarks (recursion, a sieve, matrix multiplication,
    n-body), within measurement noise of C compiled by clang at `-O2`, with
    bounds checks on.

Since 0.1:

- **The compiler in jihoo.** Every pass is ported, and the compiler in
  jihoo builds itself (stage 2) and writes the same LLVM IR as the Rust
  compiler did for every program. It is now the only compiler: the Rust
  one was removed after 0.1.1, and the released binary of the previous
  version bootstraps the next ([self-hosting](self-hosting.md)).
- **Compile-time evaluation** of ordinary function calls, recursion,
  control flow and fixed aggregates, through a separate MIR interpreter
  that uses the target's layout. `const` items, `comptime` expressions,
  array lengths and compile-time arguments use it.
- **Compile-time heap**: the interpreter provides the allocator and runs
  destructors, so `Vec`, `String` and `Map` work in `comptime` code, and
  `String` and `Vec` results become static `str` and slice constants
  ([the heap](../language/comptime.md#the-heap)).
- **Functional composition**: lazy iterator adapters and consumers in
  `std.iter`, with generic callback result inference and capture and
  forwarding of statically known closures.

## Next

Each step builds on the ones before it.

### 1. Reflection, and `derive` in the library

Done ([reflection and derive](../language/reflection.md)), with `Default`
and `field_type`; derived bounds on generic types and user-written derives
are left:

- `inline for i in a..b` repeats its body once per compile-time index.
  `inline if c` compiles only the branch its compile-time condition
  selects.
- Builtins that describe a type (`field_count`, `field_name`,
  `variant_count`, `variant_name`, `variant_field_count`, `is_struct`,
  `is_enum`), name its parts (`field(x, i)`, `variant_of(x)`,
  `variant_field(x, v, j)`), and build values from parts
  (`make(T, fn(i) { ... })`, `make_variant(T, v, fn(j) { ... })`).
- `#[derive(Clone, Eq, Ord, Hash, Show)]`, written in jihoo in
  `std/derive.jh` with those builtins. The compiler only connects the
  attribute to the library code. Privacy holds: reflection reads or builds
  another module's private fields only in the derived code of a type that
  asked for it.
- Then: `Default` (once a field's type can be named at compile time),
  derived bounds on generic types, and user-written derives.

### 2. Concurrency that borrows

Started ([threads](../language/threads.md)). `std.thread` has `join`,
`each`, `map` and `each_mut`, on POSIX threads in native programs. A
closure that runs on several threads at once is checked at compile time
with `captures_mut`. Left:

- Threads in a scope (`thread.scope(fn(s) { s.spawn(...) })`), whose
  closures must outlive each statement that starts one.
- Done: `#[interior]` memory, which changes behind shared borrows (no
  `readonly`/`noalias` there), and on it `std.sync.Atomic` and `Mutex`.
- Channels and once-cells, on the same foundation.
- A `Send`-like rule, if a type that one thread only may use ever exists.
  Today `#[interior]` types promise to be safe from several threads.
- Threads in freestanding programs: a thread-safe allocator, `clone` and
  futexes.

### 3. The data-oriented standard library

Done ([data by index](../language/data-oriented.md)): `std.arena`.

- Typed indices (`Id(T)`) and arenas that hand them out.
- Generational handles, which detect a use after the slot was reused.
- `Soa(T)`, a struct-of-arrays vector built from `T`'s fields at compile
  time with reflection (step 1).

### 4. Errors in one function

Done: one run reports every function's errors, in source order. A use
after a move notes each move that reaches it, a borrow conflict notes where
the borrow started, and an error in a generic instance notes the chain of
uses that made it.

- Notes that show where a moved value went and where a borrow started.
- More than one error per run.

### Later

- **Contracts** (which v0 had), checked by the kernel and the
  compile-time interpreter where possible.
- **Dynamic dispatch**: `dyn Trait` values, and closures that own what they
  capture, so they can be stored.
- **The C ABI**: structs by value to and from C functions.
- **Formatting**: `print` with several values, and formatting options.
- **Tail calls** that never grow the stack.
- **Macros**, if reflection turns out not to cover what they would do.
