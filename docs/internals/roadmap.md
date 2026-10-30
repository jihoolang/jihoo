# Roadmap

## Direction

jihoo should make real systems programs easy to develop while retaining
memory safety without lifetime annotations, a garbage collector or implicit
reference counting. Compile-time generation with independently checked
results continues outside the language's repository, in
[jihoo-proofs](https://github.com/jihoolang/jihoo-proofs), until it has a
stable library interface.

Keep ownership and parameter conventions stable. Borrowing views remain
tracked by the compiler; long-lived owned data refers to other data by
typed indices and handles. Improve scoped concurrency, libraries and tools
within that model before adding more language mechanisms.

Use complementary applications to guide changes: the self-hosted
compiler exercises large programs and generic data structures; Banana, the
sibling `../banana` terminal, exercises C callbacks, graphics resources,
streaming binary input and PTYs; jihoo-proofs exercises compile-time
evaluation and its resource limits. A need found in an application starts as a
small reproducer. Fix it in a library when possible, and change the language
only when the existing model cannot express the required behavior safely.

## Next

This is the development order, with completion criteria rather than release
dates. Safety and runtime performance checks apply throughout.

### 1. Checking and editor tools

Implemented: [`jihoo check`](../reference/command-line.md#checking-without-code-generation)
loads imports, checks types, evaluates compile-time obligations, elaborates
moves and drops, and checks borrows without generating LLVM IR or calling a
linker. `--lib` checks modules without an entry point. The regression suite
checks valid programs without LLVM or linkers and compares negative-case
diagnostics with the existing compiler path.

Implemented: [`--error-format=json`](../reference/command-line.md#structured-source-diagnostics)
reports source diagnostics with start/end byte positions, related notes and
generic-instance context from the same data as text errors. An independent
JSON parser checks the negative corpus, source locations, escaping and
truncation. Command-line, file, backend and linker failures and `fmt --check`
results use the same document, with a `kind` for each diagnostic, so every
unsuccessful invocation has a machine-readable result.

Implemented: [`jihoo fmt`](../reference/command-line.md#source-formatting)
normalizes indentation and token spacing while preserving comments, literal
spellings and meaningful line breaks. `--check` detects files whose layout
differs. Parser-selected lists wrap at a soft width of 100 byte columns,
configurable with `--width`. It re-lexes and reparses its output and requires
the same syntax tree apart from positions. Corpus tests compare comment
bytes, syntax trees, idempotence and generated LLVM IR, including the compiler
and standard library on both supported targets. Narrow-width cases exercise
nested lists and significant newlines. Given directories or several files,
`fmt --check` reports every file that needs formatting and `fmt --write`
rewrites them; the suite checks the compiler and library that way.

Implemented: [`jihoo lsp`](../reference/command-line.md#language-server),
a Language Server Protocol server that checks open documents, unsaved text
included, with the compiler's loader, checker and diagnostics, publishes
errors with their notes as related information, finds definitions in the
loaded syntax trees and formats documents. A client test drives it over
the protocol in both position encodings.

Implemented: [`jihoo test`](../reference/command-line.md#tests) runs the
`#[test]` functions of a file and of the modules it imports outside the
standard library, each in a process of its own, so that a panic or a trap
fails one test, and prints their results and the output of those that
failed. Given a file of the standard library, it runs that module's tests;
the `test` suite checks its output and runs every std module's tests.

Next:

- Unit tests for more of the standard library, next to its code
  (`std.string` has the first).
- Definitions resolved by sema rather than by name, so that `value.method`
  finds the receiver type's method; hover with types; checks that do not
  block replies.
- Additional formatter layout rules, retaining syntax preservation checks.

Completion: valid checks are silent and create no output files; invalid
programs retain type, move and borrow diagnostics. Editor diagnostics use the
same source ranges and notes. Formatting the compiler and library twice
produces the same source, and formatted programs retain their behavior.

### 2. Application-driven library work

- Add an optional external regression command for a configurable Banana
  checkout. Check its modules and run its parser, selection and PTY tests
  against the compiler under development. Keep the compiler's ordinary test
  suite independent of sibling repositories and graphical drivers.
- Develop resource and callback wrappers in the application first. State
  registration lifetime, thread and reentrancy requirements before exposing
  a safe interface. Extract reusable pieces after their behavior is tested.
- Done: binary I/O and structured OS errors. `std.os` has an errno-based
  `Error` and `File` reads and writes of one system call each, so partial
  reads/writes, EOF, interrupted operations and nonblocking readiness
  (`set_nonblocking`, `wait_readable`, `wait_writable`) are explicit;
  `std.fs`, `io.BufReader` and `std.process` report `os.Error`; a program
  that cannot start fails with the error number of its `execve`.
- Done: library formatting for several values and options. `std.fmt`
  formats a tuple of values with `{}` patterns (positions, fill, alignment,
  sign, bases, width, precision, exponents), and floats print the shortest
  text that reads back as them, from exact big-integer digits.

Completion: the external regression command works with an explicitly selected
compiler; core application behavior is tested without a display. Extracted
wrappers have ownership and cleanup tests. Binary I/O tests cover partial
operations and error recovery in the profiles that support them.

Unicode shaping, IME integration and terminal conformance are application or
specialized library work; they do not by themselves require new syntax.

### 3. Safety and performance regression baselines

- Keep negative cases for moves, borrow effects, drops, scoped threads and
  callback boundaries alongside accepted programs. Continue stage 1/stage 2
  comparisons and native/freestanding checks on both supported targets.
  `tests/fail` now also covers moves inside loops, dropping or reassigning a
  borrowed value, and closures that capture where a C-compatible `fnptr`
  is required.
- Done: [compilation time and memory](testing.md#compilation-time-and-memory).
  `scripts/benchmark_compile.py` measures `check` and full compilation
  separately on the compiler, a compile-time generation program and the
  fusion kernels, plus jihoo-proofs (`--proofs`) and Banana (`--external`)
  when given their checkouts. Reports record compiler revision and version,
  target, options, host, elapsed time and peak process memory per sample;
  `--baseline` compares medians with a recorded report, and CI runs the
  structural `--check-only` mode on both targets.
- Maintain the [fusion benchmark](../../benchmarks/functional-fusion/README.md)
  and the compile-time costs jihoo-proofs records as compiler and library
  implementations change. jihoo-proofs' programs convert the library's
  errors with `to_string`, so they compile with the checkout's library
  (`os.Error`) as well as with the release they pin (`String`).

Completion: changes can be compared with a recorded baseline using a
reproducible command. Structural and correctness checks run in CI; timing
comparisons run on a controlled host with repeated samples. Self-hosting
agreement is a regression check, not a proof of memory safety.

### 4. Parallel compilation (0.3)

Programs use [threads](../language/threads.md)
at scale, starting with the compiler itself: its passes become parallel
where the work is independent, and what that needs from `std.thread` and
`std.sync` guides the library. Single-threaded costs come first, because
allocation-bound code does not scale across threads.

Measured on `compiler/main.jh` (x86_64, 8 CPUs, `-O2`, 0.2.1): `check`
took 17.0 s, of which 11.3 s was borrow-effect inference and 5.2 s the
borrow checks; sema and elaboration took under 0.5 s. A full build took
36.8 s, nearly all of the rest in LLVM (`opt -O2` about 12.5 s, object
emission about 6.7 s on the same IR). Every phase ran on one CPU.

- Done: the borrow kernel's dataflow uses one flat bit vector per program
  point and worklists, and effect inference revisits only callers of a
  function whose relation grew. `check` takes 1.3 s and a full build 20.7 s;
  peak memory fell by about a quarter.
- Done: object emission in parallel. The module is still optimized whole,
  so inlining is unchanged; a large one is then emitted as up to eight
  units of consecutive functions, each on its own thread and LLVM context,
  their number fixed by the module rather than the host. A full build of
  the compiler takes 15.6 s instead of 20.9 s, and the compiler it builds
  runs within measurement noise of a single-unit build (instruction and
  cycle counts too, within 0.2% either way); small programs are emitted
  exactly as before. Peak memory grows from 277 MiB to 374 MiB: the units
  are formed by halving so that only two copies of the module are read at
  once, freed memory is returned before the threads start, and the syntax
  trees are dropped before the backend.

Remaining for 0.3.0, in this order. Each step keeps the full test suite,
the self-hosting comparison and the recorded baseline
(`benchmarks/compile/baseline-x86_64.json`) green, and states its measured
effect in the commit and here.

1. Done: phase timings. `--time-passes` writes each phase's elapsed time,
   CPU time and peak memory on standard error
   ([phase timings](../reference/command-line.md#phase-timings)), and
   `scripts/benchmark_compile.py --time-passes` records them. Every other
   output is unchanged, and so is the compiler's speed (within noise of the
   baseline). Medians of five full `-O2` builds of the compiler: load
   0.08 s, sema 0.25 s, elaboration 0.11 s, effect inference 0.17 s,
   borrow checks 0.62 s, IR generation 0.19 s, LLVM parsing 0.46 s, LLVM
   optimization 11.7 s, emission 2.0 s (9.5 s of CPU) and linking 0.20 s,
   15.7 s in all. `check` takes 1.24 s, half of it borrow checks; peak
   memory grows from 258 MiB after the checks to 377 MiB during emission.
2. Done: borrow checks and elaboration in parallel. Each function is
   elaborated and checked independently, the costliest first (statements
   times locals predicts the time well), and errors are reported in
   function order, as before. Effect inference runs in rounds: every
   function whose callees' summaries grew is inferred at once from the
   previous round's summaries, which reaches the same least fixed point.
   The per-block loan sets now have rows only for the locals that can hold
   loans (views, arguments, borrowed locals and those assigned through a
   pointer, under half in the largest functions); without that, checking
   the four largest functions at once raised `check`'s peak memory from
   258 MiB to 400 MiB. `Types` is only read by these passes. Medians of
   five runs: elaboration 0.11 s to 0.025 s, effect inference 0.17 s to
   0.03 s, borrow checks 0.58 s to 0.08 s, `check` 1.26 s to 0.53 s (1.3 s
   of CPU) at 274 MiB; a full build takes 15.2 s, its peak unchanged at
   365 MiB. The borrow checks cannot go below the largest function,
   `Sema.call_decl_inner`, which alone takes 0.1 s.
3. Done: the library work step 2 needed. `thread.each`, `map` and
   `each_mut` halve their range by index, which left the compiler's largest
   functions, adjacent in `sema.jh`, on one thread (borrow checks 0.37 s,
   1.7 CPUs busy). `each_uneven`, `map_uneven` and `each_mut_uneven` start a
   thread per processor that each take the next item when free, at an
   atomic addition per item ([threads](../language/threads.md)). Malloc
   contention did not show up, and the compiler shares no data that would
   need a `Send`-like rule: the passes only read the program and types.
4. Measured: the LLVM optimization time (11.7 s of a 15.2 s build) is
   mostly the whole-module simplification pipeline around the inliner, and
   neither lever the plan named helps much. With every function first
   cleaned up by SROA, CSE, InstCombine and SimplifyCFG (a third of the
   IR's lines left), `default<O2>` still takes 11.4 s instead of 13.0 s
   (`opt`, one CPU); SROA alone saves 0.7 s, an upper bound for emitting
   fewer allocas and copies from `llvm.jh`. Only the function pipeline
   after inlining (about 1.4 s) could run per code generation unit without
   changing what is inlined where, and it would still see module-wide
   analyses (GlobalsAA) differently. Neither is done for 0.3.0; a full
   build stays about 2.4 times faster than at 0.2.1.
5. The release: jihoo-proofs' examples compile with the checkout's
   library again (its programs turn `os.Error` into their `String`
   errors with `to_string`, which also works with the 0.1.3 compiler it
   pins), README's Status describes 0.3, and this section records the
   final numbers. The seed need not move first: `std.thread` is already
   in 0.2.1.

Sema's instance queue stays sequential unless measurements show it
dominates: it shares the type interner.

Completion: on the controlled host, a full `-O2` build of the compiler is
several times faster than 36.8 s and `check` uses the available CPUs; the
output of every compilation, diagnostics included, is identical to a
sequential one, and the programs it builds are no slower.
At 0.3.0: a full build takes 15.2 s (2.4 times faster), `check` 0.53 s
(32 times faster, on 2.5 CPUs), with the same output.

### 5. Functional composition without cost (0.4)

jihoo already removes most functional abstraction at compile time: enums
and `match`, `comptime` closure parameters and `std.iter` pipelines compile
to the loop a C programmer would write, and the
[fusion benchmark](../../benchmarks/functional-fusion/README.md) checks it.
0.4 closes the places where a functional program still has to pay, or
fall back to flags and copies. Each item below starts from a reproducer that
the 0.3.0 compiler rejects or accepts with a runtime failure; that is the
condition the Direction section sets for changing the language. Lazy
evaluation, garbage collection, implicit reference counting and
higher-kinded types remain out of scope: they conflict with predictable
memory, not with any one feature.

1. Done: owned closures with static types
   ([design](move-closures.md)). A borrowing `fn` cannot leave the
   function that made it, and a `dyn fn` costs an allocation and an
   indirect call, so a function could not return a pipeline whose closure
   captures its own locals:

   ```jihoo
   fn scaled(n: i64) -> iter.MapIter(iter.Range, i64) {
       let k = n
       iter.range(0, 5).map(fn(x) { x * k })   // error: borrows `k`
   }
   ```

   `move fn(x) { ... }` owns its captures with a type of its own, so calls
   stay direct and nothing is allocated; `-> impl Iterator` and
   `-> impl fn(A) -> R` name such types in results, and
   `comptime F: impl fn(A) -> R` takes them as type parameters. `map` and
   `filter` hold either kind of closure, so the reproducer is
   `fn scaled(n: i64) -> impl Iterator` with `move fn(x) { x * k }`
   (`tests/run/move_closures.jh`, `tests/fail/move_closure_*`,
   `tests/fail/impl_*`). The fusion benchmark's `iterator_returned`
   kernel returns such a pipeline; its optimized IR has no allocations and
   no callbacks, the other kernels' optimized IR is unchanged, and `dyn fn`
   is unchanged.
2. Done: patterns and `match` as expressions. Three gaps pushed
   programs toward flags and clones:
   - Done: `A(x) | B(x)` binds the same names in every alternative, with
     the same types and `var`-ness, in `match` arms (guards included) and
     in `let` (`tests/run/or_patterns.jh`, `tests/fail/or_pattern_*`).
   - Done: `let t = match o { Some(t) => t, None => return 0 }` with `o`
     borrowed. When the first arm that gives a value gives a place it
     cannot move out of, the `match` is a view (a borrow of what each arm
     gives), checked by the borrow kernel like any other view
     (`tests/run/match_views.jh`, `tests/fail/match_view_*`).
   - Done: `let Some(t) = o else { return 0 }`, a pattern that must
     match, with a diverging `else` that does not see its names
     (`tests/run/let_else.jh`, `tests/fail/let_else_*`).

   Each form has `tests/run` and `tests/fail` cases (borrowed and owned
   scrutinees, values with destructors, moves on only some paths),
   `from-rust.md` and the pattern reference describe them, and the
   formatter preserves them (`tests/format/input.jh`).
3. Done: format patterns checked while compiling. A function's
   `#[literal_check(param, check)]` runs `check` in the interpreter for a
   literal argument; `std.fmt` checks syntax, placeholders against the
   values and integer or float kinds against their types
   (`tests/fail/fmt_*`). The checks run after the program is lowered and
   the functions only they need are dropped, so valid calls give the same
   IR. On [200 checked calls](../../benchmarks/compile/format.jh) with 8
   value types, `check` takes 0.18 s and 33 MiB instead of 0.055 s and
   22 MiB, a full build 1.0 s and 87 MiB instead of 0.90 s and 77 MiB
   (each checking instance keeps its prepared functions while the checks
   run); the compiler workload, which does not use `std.fmt`, is
   unchanged.
4. Done: the release. 0.4.0 is tagged and the seed is 0.4.0, so the
   compiler now uses these features: `let ... else` replaces 39
   `match`es that only unwrapped an `Option` or left. `Map.get` results with
   a `str` key stay `match`es until the next seed: in 0.4.0 the `String`
   such a key is lent as ends with the statement, while `let ... else`
   keeps it borrowed; it now lives to the end of the block
   ([from Rust](../language/from-rust.md)). The
   editor work in section 1 (sema-resolved definitions, hover) continues
   alongside.

Completion: the three reproducers compile and run, or fail while
compiling with a diagnostic, on both targets in both profiles; the
fusion benchmark and the compile-time baseline show no regression;
README's Status and the language pages describe 0.4.

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
   `export fn`, system calls, atomics, volatile accesses.
9. The standard library in jihoo: `Vec`, `String`, `Map`, `Box`, sorting,
   files, arguments, the environment, running other programs
   (`std.process`), printing; native and freestanding.
10. x86_64 and aarch64 Linux.
    Native C FFI includes shared libraries (`std.ffi`), structs by value,
    nested structs and arrays, 128-bit integers, aggregate callbacks and
    variadic function pointers with C default argument promotions and
    checked C signatures on both targets. LLVM 21's C
    API handles optimization and object emission in process; clang remains
    an optional comparison backend.
11. Speed: on the benchmarks (recursion, a sieve, matrix multiplication,
    n-body), within measurement noise of C compiled by clang at `-O2`, with
    bounds checks on.

## 0.2: self-hosting and tools

Done, in the 0.1.x releases and since 0.1.3:

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
- **Dynamic dispatch**: owned `dyn Trait` values, called through a table
  of functions, and `dyn fn` closures that own what they capture, so they
  can be returned and stored ([dynamic dispatch](../language/dyn.md)).
  Left: traits with parameters, methods that return borrows, and a borrowed
  `dyn` that does not allocate.
- **Functional composition**: lazy iterator adapters and consumers in
  `std.iter`, with generic callback result inference and capture and
  forwarding of statically known closures.
- **Checking and editor tools**: `jihoo check` without code generation,
  JSON source diagnostics, `jihoo fmt` with syntax preservation checks
  (Next, step 1), compile-time resource reports, and `jihoo --version`.
- **No experiments in the repository**: functional fusion is a benchmark,
  and the proof work lives in jihoo-proofs (completed milestone 5).

## Completed milestones

These capabilities are available already; they are not the next work queue.

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
- `Default` uses `field_type` to name field types at compile time.

### 2. Concurrency that borrows

Done ([threads](../language/threads.md)). `std.thread` has
`scope`, `join`, `each`, `map` and `each_mut`, on POSIX threads in native programs
and `clone` in freestanding ones. A closure that runs on several threads
at once is checked at compile time with `captures_mut`.

- Done: scoped threads (`thread.scope(fn(s) { s.spawn(...) })`), with
  heap-backed capture tuples, consuming result handles and compiler-inserted
  joins before captured locals die, including on early returns. The scope
  retains loans and owns jobs even when handles are forgotten.
- Done: `#[interior]` memory, which changes behind shared borrows (no
  `readonly`/`noalias` there), and on it `std.sync.Atomic` and `Mutex`.
- Done: channels (`std.sync.Channel`, bounded or not) and once-cells
  (`Once`), on the same foundation.
- A `Send`-like rule, if a type that one thread only may use ever exists.
  Today `#[interior]` types promise to be safe from several threads.
- Done: threads in freestanding programs: a thread-safe allocator,
  `clone` and futexes.

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

### 5. Closing the experiments

The repository no longer has experimental directories:

- Functional fusion is the
  [benchmark](../../benchmarks/functional-fusion/README.md) in `benchmarks/`.
  Its iterator API is `std.iter`; CI runs its correctness, allocation and
  optimized-IR checks without timing, and `tests/run` keeps the iterator,
  trap order, streaming parser and compile-time closure regressions.
- The Horn kernel port, the general proof development and the checked codec
  moved with their history to
  [jihoo-proofs](https://github.com/jihoolang/jihoo-proofs), whose README
  holds their remaining work: codec scaling, stable wire tags, an executable
  proof consumer, and libraries. The compiler keeps what they needed from
  it: [compile-time resource reports](../reference/command-line.md#compile-time-resource-reports)
  and the evaluator speedups. Whether any of it belongs in the standard
  library is decided once it has a stable interface.

### 6. UEFI applications (0.4.1)

Done ([profiles](../language/profiles.md#uefi)): a third profile,
`#![uefi]`, for programs that firmware starts.

- PE32+ images for x86_64 and aarch64: COFF objects with the Windows
  calling convention, linked by lld's COFF linker, with `efi_main`,
  `__chkstk` and the memory functions written by the compiler.
- The Microsoft x64 C ABI in `cabi.jh`, checked against clang with the
  aggregate C oracle.
- `std.sys` on the boot services (consoles and memory pools), and
  `std.uefi` for the firmware's tables.
- The uefi test suite runs the programs of `tests/uefi` and most of
  `tests/run` under OVMF in QEMU.

Left: files (the simple file system protocol), program arguments from the
loaded image's options, and calling a service through a field of a raw
pointer without `(*p)`.

## Verification boundaries and deferred features

- **Proofs and checked generation**: jihoo-proofs checks general theorems
  by structural induction and ground certificates bound to generated codec
  tables, during compile-time evaluation and without language syntax or
  runtime semantics. It does not verify arbitrary generated function bodies.
- **Contracts** (which v0 had), checked by a kernel and the compile-time
  interpreter where possible. Translating jihoo semantics and contracts into
  trusted theories and caller-selected goals needs an explicit semantics;
  jihoo-proofs plans a bounded executable model first.
- **Generic derives**: inferred derived bounds on generic types and
  user-written derives, when concrete library users need them.
- **Dynamic dispatch extensions**: traits with parameters, methods returning
  borrows, and borrowed trait objects without allocation.
- **Project tooling**: use the existing Nix setup while collecting concrete
  requirements for project manifests, dependency management and caching.
  A package registry is not an immediate milestone.
- **Tail calls** that never grow the stack.
- **Macros**, if reflection turns out not to cover what they would do.
