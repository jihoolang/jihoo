# Roadmap

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

## Next

- **The compiler in jihoo.** The first goal after 0.1: port
  `crates/jihoo` to jihoo, then build it with itself
  ([plan and progress](self-hosting.md)). Done: every pass is ported, and the compiler in jihoo builds itself (stage 2) and writes the same LLVM IR as the Rust compiler for every program. It is now the only compiler: the Rust one was removed after 0.1.1, and the released binary of the previous version bootstraps the next.
- **Compile-time evaluation**: done for ordinary function calls, recursion,
  control flow and fixed aggregates, through a separate MIR interpreter
  using the target's layout. `const` items, `comptime` expressions, array
  lengths and compile-time arguments use it beyond simple folding.
  [Current limits](../language/comptime.md#checks-and-limits): heap allocation,
  destructors, pointer-bearing results and most intrinsics remain future work.
- **`#[derive]`** for `Clone`, `Eq`, `Ord`, `Hash` and `Show`.
- **Functional composition**: lazy iterator adapters and consumers are
  available through `std.iter`, with generic callback result inference and
  capture/forwarding of statically known closures. They also work with the
  compile-time interpreter for supported operations. Owning closures and
  broader type-level metaprogramming remain future work.
- **Dynamic dispatch**: `dyn Trait` values, and closures that own what they
  capture, so they can be stored.
- **Concurrency**: threads, channels and locks as library code over
  atomics, and `Send`-like rules for what may cross threads.
- **The C ABI**: structs by value to and from C functions.
- **Formatting**: `print` with several values, and formatting options.
- **Tail calls** that never grow the stack.
- **Contracts and macros**, which v0 had, on the new foundation.
- **Error messages**: more than one error per run, and notes that show where
  a moved value went or a borrow started.
