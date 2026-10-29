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

Next:

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
  implementations change. jihoo-proofs' examples currently fail to compile
  with the checkout's library: its lexer still expects `read_line` to report
  `String` errors rather than `os.Error`.

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
2. Borrow checks and elaboration in parallel. After effect inference, each
   function's check is independent. `Types` must not change while they run
   (layout and drop caches filled beforehand), and errors are still
   reported in source order, exactly as a sequential run reports them.
   Effect inference may stay sequential if the timings show it is small.
3. The library work that step 2 shows is needed, driven by the compiler
   rather than speculation: `thread.map` over uneven work (chunks or a
   pool), per-thread allocation if malloc contention shows up, deterministic
   parallel reduction, and the `Send`-like rule if shared compiler data
   needs one. Each addition gets tests in `tests/run` and `tests/fail` and
   documentation in [threads](../language/threads.md).
4. The LLVM optimization time (about 12.5 s of a 15.6 s build). Measure
   first whether smaller IR from `llvm.jh` (fewer allocas and copies before
   LLVM sees them) reduces it without slowing the programs it builds;
   parallel optimization is acceptable only if it does not change what is
   inlined where. The fusion and runtime benchmarks must not regress.
5. The release: jihoo-proofs' examples compile again with the checkout's
   library (its lexer must accept `os.Error` from `read_line`, or the
   migration is documented), README's Status describes 0.3, and this
   section records the final numbers. The seed need not move first:
   `std.thread` is already in 0.2.1.

Sema's instance queue stays sequential unless measurements show it
dominates: it shares the type interner.

Completion: on the controlled host, a full `-O2` build of the compiler is
several times faster than 36.8 s and `check` uses the available CPUs; the
output of every compilation, diagnostics included, is identical to a
sequential one, and the programs it builds are no slower.

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
