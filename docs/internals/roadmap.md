# Roadmap

## Direction

jihoo should make real systems programs easy to develop while retaining
memory safety without lifetime annotations, a garbage collector or implicit
reference counting. Compile-time generation with independently checked
results is the research direction on that foundation.

Keep ownership and parameter conventions stable. Borrowing views remain
tracked by the compiler; long-lived owned data refers to other data by
typed indices and handles. Improve scoped concurrency, libraries and tools
within that model before adding more language mechanisms.

Use two complementary applications to guide changes: the self-hosted
compiler exercises large programs and generic data structures; Banana, the
sibling `../banana` terminal, exercises C callbacks, graphics resources,
streaming binary input and PTYs. A need found in an application starts as a
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
truncation. Command-line and backend errors remain text.

Next:

- A source formatter that preserves comments and is idempotent.
- A small language server that uses the compiler's checking and diagnostic
  representation, starting with diagnostics and navigation.
- Structured command-line and backend failures for clients that need a
  machine-readable result for every unsuccessful invocation.

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
- Extend binary I/O and structured OS errors so partial reads/writes, EOF,
  interrupted operations and nonblocking readiness are explicit.
- Add library formatting for several values and formatting options.

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
- Measure frontend checking and full compilation separately on the compiler,
  Banana and compile-time generation workloads. Record compiler revision,
  target, options, elapsed time and peak process memory.
- Extend the [functional pipeline measurements](../../experiments/functional-fusion/README.md)
  to representative compositions and parser workloads. Inspect optimized IR
  and allocations as well as runtime; preserve callback, trap and drop order.

Completion: changes can be compared with a recorded baseline using a
reproducible command. Structural and correctness checks run in CI; timing
comparisons run on a controlled host with repeated samples. Self-hosting
agreement is a regression check, not a proof of memory safety.

### 4. Observable compile-time execution

- Report interpreter steps, allocation consumption and call context for each
  compile-time obligation, especially when it reaches a limit.
- Distinguish the user obligation from the library operation at which the
  limit was reached. Measure proof production and checking separately.
- Profile the existing unary encoding, string serialization and repeated
  parsing before changing representations. Preserve pointer provenance,
  lifetime validation and deterministic constant persistence.
- Consider explicit budget controls after reporting explains what each
  budget measures. Raising a limit alone is not a scalability improvement.

Completion: the current four-variant codec limit is a reproducible regression
case with an understandable source context and resource report. Each
optimization records its effect on larger inputs and keeps all invalid-memory
and execution-limit cases rejected.

### 5. Practical checked code generation

Build on the [generated codec experiment](../../experimental/verified-codec/README.md):

- Compare exhaustive compile-time checking with certificates for finite
  tables. Use a proof system when the benefit warrants its cost.
- Scale enum codecs to tens and then hundreds of variants, recording compile
  time and resource use. Add explicit stable wire tags rather than deriving
  protocol compatibility from enum declaration order.
- Try a second bounded executable representation, such as a protocol
  dispatch or state-transition table. The checker chooses the theory and
  goals from the actual generated representation; the generator supplies
  candidates and evidence.

Completion: invalid, stale and unrelated evidence is rejected; safe callers
cannot mutate checked data; runtime operations use exactly that data; and
checking code disappears from optimized runtime code. Document the trusted
adapter and the correspondence between its model and execution.

Keep the [general theorem library](../../experimental/proofs/README.md) as a
separate research track. Proof-domain induction does not establish properties
of arbitrary jihoo functions or fixed-width machine arithmetic. General
source contracts need semantics and obligations derived from actual functions
before they receive language syntax.

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
- **Dynamic dispatch**: owned `dyn Trait` values, called through a table
  of functions, and `dyn fn` closures that own what they capture, so they
  can be returned and stored ([dynamic dispatch](../language/dyn.md)).
  Left: traits with parameters, methods that return borrows, and a borrowed
  `dyn` that does not allocate.
- **Functional composition**: lazy iterator adapters and consumers in
  `std.iter`, with generic callback result inference and capture and
  forwarding of statically known closures.

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

## Research boundaries and deferred features

- **Theorem-proving research**: `experimental/proofs` defines a proof-domain
  addition relation, checks a general theorem by structural induction, and
  reuses its derivation in a second theorem during compile-time evaluation.
  Its restricted schematic checker adds a trust obligation beyond the ground
  checker. Connecting proof-domain definitions to ordinary jihoo functions
  remains open; this experiment adds no language syntax or runtime semantics.
- **Checked metaprogramming research**: `experimental/verified-codec` reflects
  payload-free enums, generates encoding/decoding tables, and checks ground
  round-trip certificates against those exact tables at compile time. A small
  trusted adapter executes the frozen tables. It does not verify arbitrary
  generated function bodies; the unary proof encoding currently limits scale.
- **Contracts** (which v0 had), checked by the kernel and the
  compile-time interpreter where possible. `experimental/kernel` contains
  a jihoo port of Horn's ground certificate checker and a compile-time
  certificate example. Translating jihoo semantics and contracts into
  trusted theories and caller-selected goals remains a separate design.
- **Generic derives**: inferred derived bounds on generic types and
  user-written derives, when concrete library users need them.
- **Dynamic dispatch extensions**: traits with parameters, methods returning
  borrows, and borrowed trait objects without allocation.
- **Project tooling**: use the existing Nix setup while collecting concrete
  requirements for project manifests, dependency management and caching.
  A package registry is not an immediate milestone.
- **Tail calls** that never grow the stack.
- **Macros**, if reflection turns out not to cover what they would do.
