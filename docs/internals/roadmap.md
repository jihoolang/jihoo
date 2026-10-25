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
11. Speed: on the benchmarks (recursion, a sieve, matrix multiplication,
    n-body), within measurement noise of C compiled by clang at `-O2`, with
    bounds checks on.

## Next

- **The compiler in jihoo.** The first goal after 0.1: port
  `crates/jihoo` to jihoo, then build it with itself
  ([plan and progress](self-hosting.md)). The lexer, the parser, the loader and sema are done (for sema, jihoo gained `i128` and `u128`); next are elaboration and the borrow kernel.
- **Compile-time evaluation**: an interpreter of MIR with the target's
  memory layout, for `const` items, `comptime` expressions and compile-time
  arguments beyond the arithmetic sema folds today.
- **`#[derive]`** for `Clone`, `Eq`, `Ord`, `Hash` and `Show`.
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
