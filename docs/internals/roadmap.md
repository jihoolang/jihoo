# Roadmap

## Direction

jihoo should make real systems programs easy to develop while retaining
memory safety without lifetime annotations, a garbage collector or implicit
reference counting. Compile-time generation with independently checked
results is the next implementation priority on that foundation.

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

### 1. Bring the existing experiments into supported use

Finish the work exposed by `experiments/functional-fusion` and `experimental/`
before starting the language server or unrelated library expansion. These
are the next implementation inputs, not an indefinite research backlog.
Moving directories or adding another demonstration does not complete this
milestone: reusable code needs a supported home, regression coverage and a
caller outside its original experiment.

| Current directory | Intended outcome | Work required before migration |
| --- | --- | --- |
| [Functional fusion](../../experiments/functional-fusion/README.md) | A maintained benchmark under `benchmarks/`; compiler and `std.iter` regressions under `tests/` | Separate deterministic CI checks from timing and cover representative compositions |
| [Ground kernel](../../experimental/kernel/README.md) | An importable checking library under `lib/`, with a CLI example | Stabilize the API and trust boundary, and make rejection tests independent of a sibling checkout |
| [General proofs](../../experimental/proofs/README.md) | A proof-development library under `lib/`, with executable consumers | Exercise induction and derivation reuse beyond natural-number demonstrations and connect one bounded executable model |
| [Verified codec](../../experimental/verified-codec/README.md) | A checked-generation library under `lib/`, with an example under `examples/` | Remove the four-variant bottleneck, define stable tags and retain evidence-to-table binding |

Work through the following steps in order. Existing safety fixes and
regression maintenance continue throughout.

#### A. Establish regression coverage for the existing implementations

- Add a repository-level command selecting the compiler and running the
  deterministic fusion, ground-checker, schematic-checker and codec suites.
  Keep valid and invalid cases in ordinary CI on both supported targets.
  The current proof/codec CI step runs only the two positive examples.
- Separate local ground and schematic rejection cases from differential
  validation against Horn. Local CI must not require `../horn`; the
  differential job must select and record its reference revision explicitly.
- Retain the recorded fusion measurements. Keep callback, trap, drop and
  short-circuit order tests, and add compositions using `take`, `zip` and a
  streaming parser workload. Inspect allocations and optimized IR for the
  cases expected to fuse. Timing thresholds belong on a controlled host.

Completion: one documented command runs local acceptance, rejection and
fusion structure checks without sibling repositories or timing thresholds;
CI invokes it. The existing `std.iter` implementation and closure fixes are
already integrated and must not be counted as new work.

#### B. Resolve the compile-time codec bottleneck

- Preserve the four-variant reverse codec as the first scalability
  reproducer. Report interpreter steps, allocation consumption and call
  context, distinguishing certificate production from checking.
- Profile unary terms, serialization and repeated parsing; optimize the
  measured costs while preserving pointer provenance, lifetime validation,
  deterministic constant persistence and rejection of invalid memory.
- Make four variants succeed, then measure 16, 64 and 256 variants. Record
  checking time, full compile time, peak process memory and evaluator usage
  for each size. Raising the evaluator limit alone does not complete this
  work; any remaining limit needs a measured cause and a follow-up fix.
- Compare exhaustive compile-time table checking with the certificate path.
  Use the simpler path for the finite codec if measurements justify it, and
  retain the certificate path as a tested consumer of the ground kernel.
- Add explicit stable wire tags and tests for declaration reordering,
  duplicate tags and unknown tags. Preserve immutable checked tables and
  rejection of invalid, stale or unrelated evidence.

Completion: the four-variant reproducer and the 16/64/256-variant cases pass
with recorded resource use. Runtime operations use exactly the checked data,
and optimized runtime code contains no proof producer or checker. Both
checking paths agree on the existing exhaustive small-table corpus.

#### C. Give the proof libraries an executable consumer

- Use a finite state-transition table as the second checked representation.
  Generate its theory and caller-selected goals from the exact immutable
  table used at runtime. Test a safety invariant for every reachable state
  using the schematic checker's induction and derivation reuse.
- State the correspondence between runtime transitions and proof-domain
  steps, including bounds and integer behavior. A theorem about constructor
  trees alone does not establish a property of a jihoo function.
- Reject changed transitions with stale evidence, missing reachable cases,
  invalid induction assumptions and evidence for another table. Measure
  proof construction and checking separately, and keep the runtime adapter
  and all additional trust assumptions explicit.

Completion: a consumer beyond the natural-number example uses the general
proof API, and mutations of the executable representation invalidate its
proof. The executable model and its limits are documented and tested. This
is the concrete next step toward contracts; general source syntax requires
obligations derived from actual function semantics.

#### D. Migrate the supported pieces and close the experiments

- Move the reusable checking, proof-development and codec modules into
  `lib/`, with documented imports and separate ground/schematic trust
  boundaries. Update examples, test commands, CI and all importing modules
  together; normal use must not depend on `-I experimental/...`.
- Move the fusion harness and reproduction scripts into `benchmarks/`,
  preserving raw measurements and their compiler/host provenance. Keep
  semantic regressions in `tests/` and reference the benchmark from the
  performance documentation.
- Leave only historical results or explicitly identified unsupported
  prototypes in the experimental directories. Give each retained prototype
  a concrete unresolved issue and a next reproducer; remove superseded code
  only after its behavior and tests have a maintained replacement.

Completion: documented library examples work with the packaged compiler
outside this checkout; CI covers the supported APIs on x86_64 and aarch64.
Every current experiment has either migrated with its checks or has a
specific recorded reason and next action for what remains. A directory
rename alone is not completion.

### 2. Checking and editor tools

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

Implemented: [`jihoo fmt`](../reference/command-line.md#source-formatting)
normalizes indentation and token spacing while preserving comments, literal
spellings and meaningful line breaks. `--check` detects files whose layout
differs. Parser-selected lists wrap at a soft width of 100 byte columns,
configurable with `--width`. It re-lexes and reparses its output and requires
the same syntax tree apart from positions. Corpus tests compare comment
bytes, syntax trees, idempotence and generated LLVM IR, including the compiler
and standard library on both supported targets. Narrow-width cases exercise
nested lists and significant newlines.

Next:

- A small language server that uses the compiler's checking and diagnostic
  representation, starting with diagnostics and navigation.
- Structured command-line and backend failures for clients that need a
  machine-readable result for every unsuccessful invocation.
- Additional formatter layout rules and project traversal, retaining syntax
  preservation checks. The current command formats a single file to stdout.

Completion: valid checks are silent and create no output files; invalid
programs retain type, move and borrow diagnostics. Editor diagnostics use the
same source ranges and notes. Formatting the compiler and library twice
produces the same source, and formatted programs retain their behavior.

### 3. Application-driven library work

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

### 4. Safety and performance regression baselines

- Keep negative cases for moves, borrow effects, drops, scoped threads and
  callback boundaries alongside accepted programs. Continue stage 1/stage 2
  comparisons and native/freestanding checks on both supported targets.
- Measure frontend checking and full compilation separately on the compiler,
  Banana and compile-time generation workloads. Record compiler revision,
  target, options, elapsed time and peak process memory.
- Maintain the fusion and checked-generation baselines established in
  milestone 1 as compiler and library implementations change.

Completion: changes can be compared with a recorded baseline using a
reproducible command. Structural and correctness checks run in CI; timing
comparisons run on a controlled host with repeated samples. Self-hosting
agreement is a regression check, not a proof of memory safety.

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

## Verification boundaries and deferred features

- **General proof boundary**: `experimental/proofs` defines a proof-domain
  addition relation, checks a general theorem by structural induction, and
  reuses its derivation in a second theorem during compile-time evaluation.
  Its restricted schematic checker adds a trust obligation beyond the ground
  checker. Connecting proof-domain definitions to ordinary jihoo functions
  starts with the bounded executable model in milestone 1C; arbitrary function
  contracts still need a semantics. The current experiment adds no language
  syntax or runtime semantics.
- **Checked generation boundary**: `experimental/verified-codec` reflects
  payload-free enums, generates encoding/decoding tables, and checks ground
  round-trip certificates against those exact tables at compile time. A small
  trusted adapter executes the frozen tables. It does not verify arbitrary
  generated function bodies. Milestone 1B addresses the current unary encoding
  bottleneck before promotion to a supported library.
- **Contracts** (which v0 had), checked by the kernel and the
  compile-time interpreter where possible. `experimental/kernel` contains
  a jihoo port of Horn's ground certificate checker and a compile-time
  certificate example. Translating jihoo semantics and contracts into
  trusted theories and caller-selected goals needs an explicit semantics.
  Milestone 1C delivers a bounded executable model before general syntax.
- **Generic derives**: inferred derived bounds on generic types and
  user-written derives, when concrete library users need them.
- **Dynamic dispatch extensions**: traits with parameters, methods returning
  borrows, and borrowed trait objects without allocation.
- **Project tooling**: use the existing Nix setup while collecting concrete
  requirements for project manifests, dependency management and caching.
  A package registry is not an immediate milestone.
- **Tail calls** that never grow the stack.
- **Macros**, if reflection turns out not to cover what they would do.
