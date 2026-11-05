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
evaluation and its resource limits, and is where verification (0.5) and
proofs as a library (0.6) begin. A need found in an application starts as a
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

### 6. Verification (0.5)

Direction revised: the replacement is a
[native dependent core](dependent-core.md). Programs and their proofs
are checked together, then erased and lowered directly from those terms
to MIR. Recreating the MIR program in Horn is not part of this path;
Horn theory/certificate compatibility is not a requirement.

Started: `jihoo core` checks a small dependent core with levelled
universes, dependent functions, erased evidence and immutable indexed
arrays. `examples/core_index.jhc` compiles a runtime index through the
checked program to MIR/LLVM, with the evidence erased and no added bounds
assertion. Both targets, host execution at `-O0`/`-O2`, independent
evaluation and false-proof rejection run in the `core` suite.

Implemented source slice: `#![dependent_core]` routes a restricted ordinary
`.jh` AST directly into that same checker and lowering. Explicit
`erased(Lt(i, n))` proof parameters remain distinct from `comptime`;
`if_lt` introduces scoped symbolic evidence and dependent application
connects it to an immutable array's length. `examples/core_index.jh`
supports ordinary checking, both targets' objects and host execution.
Its library MIR equals the `.jhc` example, with no evidence locals or
extra bounds assertion. Positive, negative and differential execution
tests run in the same `core` suite, and the compiler still bootstraps
from the unchanged release seed.

Implemented equality slice: `Eq(a, b)` for U64, symbolic reflexivity,
proposition-only transport and `if_eq` branch evidence work in both
frontends. User-written symmetry/transitivity and range-rewriting lemmas
compose through ordinary dependent application. `examples/core_equality.jh`
rewrites a runtime bound to a local array's length; its MIR equals the
textual core program with no proof storage, closures or added bounds
assertions. Both targets at `-O0`/`-O2`, native differential execution,
false-equality rejection and direct kernel tests run in the `core` suite.
No runtime data casts or equality reflection are enabled.

Implemented first inductive proposition: indexed `EqChain(a, b)` has
reflexive and strictly positive step constructors. Its structural induction
checks an arbitrary proposition family on the endpoints, the base case
and the exact tail hypothesis; only that tail is used for recursive
reduction. Both frontends support named or contextual proof cases,
including captured endpoints and erased evidence. `examples/core_chain.jh`
uses a universally checked chain-to-equality lemma to justify a runtime
array load, with no proof storage, recursion or added bounds checks in
MIR. Paired core/source tests cover both targets, host execution, invalid
indices/cases and raw kernel reduction. The supported inductive family is
fixed in the kernel. General declarations and dependent elimination over
chain evidence remain future work.

Implemented declared inductive propositions: in a marked module,
`trait F(a: u64, ...) { fn c(...) -> F(...) }` declares a U64-indexed
proposition whose bodiless signatures are its constructors, and
`induct(P, case..., evidence)` eliminates it into a proposition family on
its indices. The kernel checks constructor telescopes (u64 data fields,
erased proof fields, the family only as a whole recursive field or the
result) and derives each case's type and the reduction on recursive
fields. The built-in `EqChain` and its four kernel terms are removed;
`examples/core_chain.jh` declares the chain itself, so the trusted
kernel has three general terms instead of a fixed family.
`examples/core_inductive.jh` proves that nodes reachable along declared
graph edges are in bounds and indexes an array with no bounds check.
Both frontends, both targets at `-O0`/`-O2`, native differential
execution, 52 source and 21 core rejections and raw kernel tests of
positivity, ordering and elimination run in the `core` suite.

Implemented loops and arithmetic: i64 `+ - *`, trapping on overflow and
folded only when that cannot happen, and `fold(n, init, fn(i, p, acc) {
body })`, a loop whose body has erased evidence of `Lt(i, n)`.
`examples/core_loop.jh` sums and multiplies arrays of symbolic length
with no bounds checks, its MIR one real loop per export; the normalizer
never unrolls loops, and keeps the overflow traps of arguments that
substitution would discard, so calls stay call-by-value. Both frontends,
both targets, native differential execution, overflow traps, 18 source
and 8 core rejections and kernel tests run in the `core` suite.

Implemented index arithmetic: U64 terms denote naturals, `+` on them
traps at run time instead of wrapping, and conversion compares sums in a
canonical order. Three kernel rules, `lt_add`, `lt_cancel` and the
discreteness rule `lt_le` (x < y <= z gives x < z), with closed
`decide_lt`, give the order of the naturals; weakening, transitivity and
`a < a + 1` are user lemmas. `examples/core_order.jh` reads `xs[i + 1]`
in a loop, sums a prefix after one comparison and loads at a computed
`i + 1`, with no bounds checks. Both frontends, both targets, native
differential execution, u64 traps, 18 source and 7 core rejections and
kernel tests run in the `core` suite.

Implemented subtraction: `sub(a, b, p)` needs evidence of `b <= a` and
never underflows; conversion cancels it (`(k - 1) + 1` is `k`) with
proof irrelevance, and `zero_le(a)` gives the lower bound 0.
`examples/core_sub.jh` reads arrays backwards and loads `xs[k - 1]`,
with no bounds checks. Both frontends, both targets, native differential
execution, 14 source and 5 core rejections and kernel tests run in the
`core` suite.

Implemented refinements: `refine(fn(j) { P(j) })` is a u64 with erased
evidence of `P`, made by `pack(a, p)` and taken apart by `witness(s)`
and `proof(s)`; it is the u64 alone at run time, and an export may
return one. `examples/core_refine.jh` returns a clamped index with its
bound and `k - 1` with `(k - 1) + 1 = k`, and loads with them without
bounds checks. Both frontends, both targets, native differential
execution, kept witness traps, 18 source and 7 core rejections and
kernel tests run in the `core` suite.

Implemented non-recursive data types: in a marked module, `enum E { V(T,
...) }` declares a data type whose fields are u64, i64, refinements,
earlier data types or erased propositions; `E.V(...)` builds a value,
`match` takes it apart into the expected type and `induct(fn(x) {
P(x) }, case..., v)` proves `P` by cases, with a motive that depends
on the value. Data values have no runtime representation: case analysis
of a branch is the branch of the cases, so `examples/core_data.jh`
compiles to comparisons and loads with no tag or bounds check. Both
frontends, both targets, native differential execution, kept field
traps, 25 source and 12 core rejections and kernel tests run in the
`core` suite.

Implemented erased indices and indexed data: `n: erased(u64)` is a u64
used only in types and evidence, never passed or evaluated at run time.
`enum Slot(n: u64)` declares a data type for each `n`; each constructor
binds the parameter first, erased, and returns it, so matching on a
`Slot(n)` knows its `n`, and a value takes its parameter from the
expected type. In the kernel and `.jhc`, data types also have true
indices, which each case learns through a motive over the indices and
the value. `examples/core_indexed.jh` reads tables of any length
through slots, widens a slot to a larger table and reads the head of a
nonempty array, with exports that take no erased length. Both
frontends, both targets, native differential execution, 19 source and
11 core rejections and kernel tests run in the `core` suite.

Next: owned memory, then recursive data types on it, following the
[memory plan](dependent-core.md#owned-memory-plan): allocation is
explicit, and memory is freed explicitly or when its owner's scope ends.
The kernel checks that every owned value is used exactly once, so the
untrusted source elaborator inserts the frees, and a wrong free is a
compile error rather than a leak or a double free. The steps: (1) the
kernel's linearity check, owned heap buffers and explicit `free`;
(2) recursive data types as heap nodes; (3) structural recursion that
consumes them; (4) frees inserted in source where ownership ends;
(5) borrows, reading without consuming. Broader lemma libraries;

Implemented step (1), owned buffers: `buffer(n)` is n i64 values on the
heap, made by `alloc(n, x)` and read, written and freed with `load`,
`store` and `free`, at indices with evidence and without bounds checks;
a loop may carry one as its accumulator. The kernel counts each owned
value's runtime uses and requires exactly one, alternatives alike; no
function value, loop body or partial application can hold one, and
normalization binds an argument that touches memory once instead of
substituting it. `examples/core_buffer.jh` computes running sums in
place and reads a table at a runtime index; its MIR calls malloc and
free once each per export. Both frontends, both targets, native
execution counting allocations and frees, valgrind on the example, 23
source and 12 core rejections and kernel tests run in the `core` suite.

Implemented steps (2) and (3), recursive data and structural recursion:
a data type with a recursive field (or a field on the heap) is boxed: its
values are heap nodes, owned and used exactly once. `match` takes one
node apart, frees it and gives its fields; `induct(fn(t) { T }, ...)`
is structural recursion, compiled to a recursive function that frees
each node, whose cases see the recursive fields only erased and receive
their results; into a proposition it is a proof by induction.
Conversion now treats a sum's operands in any order, while code keeps
their evaluation order. `examples/core_list.jh` builds, doubles, sums,
measures and takes apart lists and proves that doubling keeps the
length. Both frontends, both targets, native execution counting
allocations and frees, valgrind on the example, 17 source and 8 core
rejections and kernel tests run in the `core` suite.
establish the kernel's soundness and elaboration/erasure/lowering
preservation.
The `.jhc` prototype does not complete the 0.5 release gate. The existing
verifier and its gaps described below remain applicable to unmarked `.jh`
programs until their supported operations and guarantees move to the core.
Only the explicit pure source subset bypasses legacy VC generation today;
no broader legacy path is retired by this slice. Horn implementation or
certificate compatibility is not a constraint on its replacement.

Research ([design](verification.md)): 0.5 proves, while compiling, that
the checks MIR inserts cannot fail and that functions meet their contracts.
Proofs are checked and erased; a proved check is removed. A small trusted
checker accepts certificates that untrusted provers produce, and the
obligations come from MIR after `elab` and `check`. The work starts in
[jihoo-proofs/obligations](https://github.com/jihoolang/jihoo-proofs/tree/main/obligations)
and moves into the compiler once its trust boundary is stated.

1. Started: obligations from a model of MIR's integer part, proved by
   Fourier–Motzkin and checked as Farkas certificates. `clamp`'s
   `ensures` and `sum`'s bounds and counter-overflow checks (from
   `emit-mir`, by hand) are proved, `s + xs[i]` is not, and ten rejection
   cases pass. The finding: the two functions take 1.35 and 3.96 million
   interpreter steps, against 1 million per compile-time evaluation.
2. The generator on real MIR. Started:
   [`emit-obligations`](../reference/command-line.md#verification-model)
   prints each function's MIR as the model (`compiler/obligations.jh`),
   with every `assert` and checked `+ - *`, in the debug and `--release`
   overflow modes; what it cannot follow, including locals whose address is
   taken, is opaque. `tests/obligations.py` checks it with an independent
   reader, and jihoo-proofs verifies the compiler's output with the same
   verdicts as the hand-written models, plus an off-by-one loop and a local
   changed through `inout` that must stay unproved. Started: the generator
   against the interpreter. Each check carries its span; jihoo-proofs'
   `differential.py` evaluates random inputs that meet a function's
   `requires` at compile time and fails if a check it proved fails there,
   or a proved `ensures` does not hold, in debug and `--release` builds. Two
   deliberately wrong models are caught. The test runs over all 98 programs
   of `tests/run` and `examples` (317 checks, 25 proved, no proved check
   failing; 69 proved with the untrusted invariant inference that step 4
   needs, started early). Each unproved check reports why: most depend on
   a value loaded from memory or a call's result, which contracts (steps 4
   and 5) address. Done: contracts in the source (step 4), which
   `emit-obligations` prints over MIR's locals.
3. The checker in the compiler: a pass after `check` that runs the trusted
   checker as compiled code, outside the interpreter's budget, and removes
   proved checks. Library proofs keep using compile-time evaluation, so
   its cost is reduced alongside (the `Vec` operations that dominate the
   experiment). Started:
   [`jihoo verify`](../reference/command-line.md#verification) lists each
   check that stays and each unproved contract clause (`--all` the proved
   ones too), and `--verify` builds without the proved checks. A proof
   counts only when what it rests on (a `requires`, a callee's `ensures`,
   a cut point) is proved, and cut points where paths meet keep the work
   linear, so it runs on the compiler itself: 378 of 2,489 checks proved
   in 22 seconds. The `verify` suite runs `tests/run` with `--verify`, and
   jihoo-proofs' differential test checks the compiler's verdicts against
   the interpreter. Done: verification in parallel, proving each
   obligation as it is generated, which takes it on the compiler from 25
   to 3.5 seconds and 1.6 GB to 530 MB
   ([design](verification.md#verification-in-parallel)). Done:
   verification by default ([design](verification.md#unproved-contracts-are-errors)):
   every command that generates code proves the program and removes the
   proved checks, `--no-verify` keeps them all, and an unproved contract
   is a compile error.
4. Contracts: `requires`/`ensures` on functions, `invariant` on loops, and
   `old(x)` for `inout` parameters. A call proves the callee's `requires`
   and assumes its `ensures`. An unproved contract is a compile error;
   untrusted inference proposes the invariants of loops over `0..n`.
   Started ([contracts](../language/contracts.md)): the syntax, linear
   clauses over integers and lengths, which sema checks and
   `emit-obligations` prints; jihoo-proofs proves them from the source,
   modularly at calls, with `inout` integers and locals lent to a call as
   variables, and the differential test tells failures under an unproved
   contract from bugs. `tests/fail` has a case for each malformed
   contract. Fields, `Vec` lengths (`v.len()`) and `old` of them are
   part of clauses (step 5), and so are `||` and `!`: a clause is then a
   few cases, assumed one at a time and proved by refuting them all
   failing. Done: unproved contracts are compile errors (with step 3),
   and `tests/fail` has a case for each kind of rejected contract.
5. `std` contracts: `Vec.index`, `Vec.push`, slicing and `str` lengths,
   so that ordinary loops over vectors and slices have no bounds checks
   left. Started ([design](verification.md#fields-panics-and-calls)):
   integer fields of locals and borrowed parameters are variables, so
   clauses name them (`self.len`, `old(self.len)`, `x.len()`); a call to a
   function that never returns is a check, removed when proved; and a call
   to a small function that may panic proves the panic away itself, so
   `Vec.index` states no `requires` and each `v[i]` keeps or loses its own
   check. `std` states `ensures` on `Vec` (`new`, `len`, `reserve`,
   `push`, `pop`, `insert`, `remove`, `as_slice`) and `String`, all proved.
   On the compiler, bounds and overflow checks proved went from 378 to
   720, and 120 calls prove `Vec.index`'s panic away (746 and 125 once the
   prover also looks for a case that contradicts the path, below the
   claim). Started: type invariants
   ([design](verification.md#type-invariants)), `invariant` clauses on a
   struct that every function assumes of the values it is given and every
   writer of the type proves; stating `Vec`'s found three ways to give it
   a negative length. `std` states `0 <= len && 0 <= cap` for `Vec`, and
   the compiler proves 939 bounds and overflow checks. Done: slicing
   ([design](verification.md#slices)): its checks compare `hi <= len` and
   `lo <= hi` without a `+ 1` that could overflow, and a slice's length
   keeps a length's range, so slicing after a length test keeps no check.
6. Self-verification, before 0.5.0: jihoo verifies jihoo, as lean4lean
   checks Lean with a kernel written in Lean and proves that kernel's
   properties in Lean. First, the compiler verifies its own source:
   `jihoo verify compiler/main.jh` runs in CI and every check it keeps is
   listed with its reason, while `std` and compiler contracts raise the
   share proved; the `verify` suite fails when it proves fewer of any kind
   than `tests/verify/compiler.proved` records. Then the trusted parts verify themselves: the checker
   (`linear.jh`) and the generator (`vc.jh`) state contracts, proved by the
   compiler they are part of, until no check is left in the checker.
   Last, the checker's soundness (an accepted certificate means the facts
   cannot all hold) is proved in jihoo, by induction over the weighted sum,
   with the Horn kernel that 0.6 makes a library. Started
   ([design](verification.md#the-checkers-own-checks)): `linear.jh`'s
   loops state invariants and every bounds check in the checker is proved,
   once the verifier follows wrapping `+%` (range `for` counters), infers
   that a range's end equals the length it copies, and its prover looks
   for a negative cycle among difference facts before elimination; the
   compiler proves 969 bounds and overflow checks and 155 calls' panics.
   Done: no check is left in the checker. Its sums are exact, with
   arithmetic that reports overflow, and a certificate whose sum does not
   fit an i128 is rejected; the `verify` suite fails if a check in
   `linear.jh` is kept. The compiler proves 1,145 of its bounds and
   overflow checks, and its contracts and `std`'s hold in both overflow
   modes. The soundness proof needs a statement about every integer
   point (an implication), implication goals, induction under hypotheses
   and integers. These pulled 0.6's first steps before 0.5.0, in this
   order; the remaining proof connections below are release requirements:
   1. Done: Horn's whole schematic checker as a library,
      [`lib/proof`](../../lib/proof/schematic.jh): implication goals,
      rule hypotheses, `apply`, induction under hypotheses and `invert`,
      whose algorithm Horn's Agda development proves sound. Horn's
      acceptance and rejection tests pass on it.
   2. Done ([design](verification.md#the-checkers-soundness)): the
      algorithm. A Horn theory of the integers (ordered commutative ring
      axioms) and of `linear.jh`'s merge, weighted sum and acceptance,
      and a certificate, checked by `lib/proof` in a test, that an
      accepted certificate's facts and negated claim have no common
      point. Done with it: the adequacy of the theory for ℤ (step 3).
   3. The code: a trusted translation of MIR (a fragment: integers,
      `Vec` reads and pushes, `Option`, loops) into Horn rules, which
      says what the code computes the way `vc.jh` says what it checks,
      and a proof in Horn that `check` returning `Ok` gives `accepts`.
      `linear.jh`'s `add` and `mul` compute with bit tricks the
      translation would have to model; 0.4.7's `overflowing_add` and
      `overflowing_mul` builtins replace them with exact semantics.
      Done ([design](verification.md#the-proof-of-the-code)): `jihoo
      emit-horn` translates `check` and what it calls, and
      `lib/proof/refine.jh` proves that `check` returning `Ok` means the
      certificate's facts and negated claim have no common point (36,631
      steps, also accepted by Horn's checker). Done
      ([design](verification.md#the-checkers-soundness)): the adequacy
      of reading the theory in ℤ. Horn's Agda development proves its
      certificates sound in every model of the rules, and
      [`agda/`](../../agda/Adequacy.agda) gives the theory's model in
      the integers, so the theorem says of integers what the code
      computes: when `check` returns `Ok`, no integer point satisfies
      the facts and the negated claim. `nix flake check` checks it.
      What it rests on is trusted as `vc.jh` is: the translation
      (`horn.jh`), `std`'s `Vec` as the rules' lists, and `lib/proof`'s
      port of Horn's checker. Done: the translation and `Vec` tested
      against the code ([design](verification.md#the-proof-of-the-code)):
      on random inputs, the rules derive what the compiled checker
      returns, and nothing else but overflow results.
   4. Required before 0.5.0: independently check the actual certificate
      produced by `refine.jh` in Agda. Export its proof steps, not only
      its theory, and use the checked certificate to supply
      `Valid goalH goalJ` to `Adequacy.sound`. Today that validity is a
      premise of the Agda theorem, established by the jihoo checker;
      checking the theorem alone does not discharge it. Completion:
      `nix flake check` regenerates and checks the certificate from the
      current source, rejects corrupted certificates, and no longer
      relies on the correctness of the jihoo Horn checker for this proof.
      Done ([details](../../agda/README.md)): Horn's
      `agda/ImplicationCheck.agda` is a checker for implicational
      certificates that Agda runs by evaluation, proved sound in every
      model of the rules from `Implication.agda`'s lemmas and `Unify.agda`'s
      unifier; Horn's `schematic-kernel --agda` exports the certificate
      for it. `nix flake check` regenerates the certificate from the
      current source, exports it, and has Agda check it;
      [`agda/Certified.agda`](../../agda/Certified.agda) gives its theorem
      Adequacy's model in the ring, so `Adequacy.sound` no longer takes
      `Valid goalH goalJ` as a premise. Agda rejects a certificate for a
      goal without one of its hypotheses (Horn's test on `le_trans`); the
      `certificate` check keeps the Rust checker's rejection of corrupted
      results. Doing this found that Horn's checkers, Rust and jihoo's
      port, accepted a rule hypothesis as a premise without proving its
      premises, so they accepted false implications; both now reject it,
      and this proof never relied on it.
   5. Required before 0.5.0: prove the connection from execution to the
      Horn model. Define the execution semantics of the MIR fragment
      used by `linear.jh`, including overflow and the `Vec` operations
      it calls, and prove that a run returning `Ok` satisfies the
      generated Horn execution relation. Connect the library operations
      to their list model, with any remaining memory and runtime
      assumptions explicit. Completion: compose this theorem with step 4
      to prove the checker's soundness for that execution semantics;
      differential tests remain regression checks, not this proof.
      Started: [`agda/ListExecution.agda`](../../agda/ListExecution.agda)
      proves that executable finite-list length, successful lookup and
      push derive the actual generated `len`, `nth` and `snoc` relations
      for the checker's term, fact and weight lists. The proofs cover all
      well-sorted ground elements and indices; an index may be any ground
      integer expression with the appropriate value. Nix/CI regenerates
      the theory and rejects incorrect length, index and push rules.
      Connecting `std.Vec`'s memory and capacity semantics to finite lists,
      MIR arithmetic and overflow, calls and the path-to-rule translation
      remains required before composing a whole checker run with step 4.
      Started: [`agda/VecMemory.agda`](../../agda/VecMemory.agda) specifies
      typed backing cells, initialized prefixes, length and capacity,
      including zero-capacity borrowed buffers. Reads match list lookup;
      successful pushes append without changing other backing cells, and
      relocation preserves the prefix. Constructive theorems give copying
      and push executions with sufficient capacity. `VecHornExecution.agda`
      composes these operations with the generated list rules for terms,
      facts and weights. Nix checks both targets and rejects six wrong
      memory operations. This is a backing-store specification: actual
      `std.Vec` MIR and checker loops, byte/pointer layout, allocator and
      borrow semantics, growth policy and machine-width arithmetic still
      need their connections; step 5 remains incomplete.
      Started: [`agda/ScalarExecution.agda`](../../agda/ScalarExecution.agda)
      defines executable bounded addition and multiplication and proves
      that the exact/overflow flag projection used by `linear.add` and
      `linear.mul` has a numerical result represented by their actual Horn
      rules. Bounds are parameters, including signed i128; rejected
      operations are outside them. Nix checks boundary examples and
      rejects wrong operations and a missing overflow result. Independent
      numeral tests found and now cover translation overflow at i128's
      minimum and the negative encoding of upper-half u128 constants, on
      both targets. The raw wrapped bits and the LLVM intrinsic
      implementation, general MIR paths/calls and `Vec`'s memory model
      still need correspondence proofs; step 5 remains incomplete.
      Started: [`agda/MirExecution.agda`](../../agda/MirExecution.agda)
      gives scalar MIR frame, statement, branch and call semantics, with
      direct calls running the selected callee's graph. A
      serializer exports the actual helper/caller MIR after sema and
      borrow/drop checking. `MirCorrespondence.agda` proves returning
      executions of `add`, `mul` and two direct callers have numerical
      representations in their generated Horn relations, and constructs
      executions for every permitted intrinsic outcome. Nix checks both
      targets and rejects incorrect operations, returns, callees,
      lifetimes and caller rules, plus unsupported wrapping arithmetic.
      Started: [`agda/MirLoopCorrespondence.agda`](../../agda/MirLoopCorrespondence.agda)
      uses inductive block invariants, proved sound in `MirExecution.agda`,
      to connect an exported accumulator loop to its generated Horn entry,
      back-edge and exit rules. Every return from an initially in-range
      accumulator gives its last in-range value before the next sum
      overflows. The proof has no fixed iteration bound or termination
      premise and constructs graph executions for finite sequences of
      permitted intrinsic outcomes. Nix checks both targets, multiple
      iterations in both directions, equivalent integer representations
      and a non-returning cycle, and rejects incorrect loop operations,
      returns, updates, branches and Horn steps or a missing Horn exit.
      The serializer/frontend remain trusted; general MIR operations,
      invariants for the checker's list-processing loops, borrow/pointer
      and `Vec` memory semantics, and the backend still need their
      connections. This covers these five exported graphs, not the entire
      checker or all MIR paths/calls.
   6. Required before 0.5.0: prove verification-condition generation and
      check removal sound. For `obligations.jh`, `vc.jh` and `verify.jh`,
      show that valid generated obligations imply that removed checks
      cannot fail, accepted contracts hold, and erasure preserves
      behavior under the stated MIR assumptions. Start with integers and
      branches, then cover loops, calls, recursion, mutable borrows and
      type invariants, including dependencies on other contracts and
      incomplete analysis. Completion: every rule used to remove a check
      or accept a contract is covered by the composed proof; unsupported
      cases keep their checks and do not silently establish contracts.
      Started: [`agda/CheckRemoval.agda`](../../agda/CheckRemoval.agda)
      defines a graph semantics and generates semantic local conditions
      for assertions, guarded operations, branches, loops, jumps, returns
      and traps. Discharging those conditions proves one-step
      correspondence and preservation of finite traces and final states
      in both directions after local check removal, including retained
      failures and arbitrary primitive effects. `CertifiedRemoval.agda`
      uses the independently checked linear certificate to discharge a
      guard when the path-fact and negated-claim connections hold. Nix/CI
      checks the proofs, loop and opaque-effect examples, and rejection
      of false guards, invalid state preservation, missing branches and
      unestablished postconditions.
      These are semantic specifications: the implementation-to-condition
      connection, concrete arithmetic and memory semantics, contracts and
      dependencies, incomplete analysis and panic/call erasure remain
      required. This does not complete step 5 or step 6.
   7. Required before 0.5.0: publish the composed theorem, its supported
      semantics and its remaining trusted components, and check the proof
      chain in CI. Distinguish checks proved in the compiler's own source
      from the soundness of its verifier. Source-to-MIR and MIR-to-LLVM
      semantic preservation are a separate compiler-correctness milestone;
      specify their proof obligations and whether LLVM remains trusted.
      Until those are proved too, do not describe this as formal
      verification of the entire compiler or its emitted executables.
7. The releases. A 0.4.x release that parses contracts lets `lib/std`
   state its contracts (step 5) before 0.5.0, since the seed compiles
   `lib/std`; contracts' syntax is fixed from then on. 0.5.0 comes when
   jihoo can verify its own compiler, and the seed moving to it lets the
   compiler state contracts itself. 0.4.6 verifies every build and makes
   an unproved contract an error, so with it as the seed, stage 1 is
   verified too. 0.5.0 waits for all of step 6, including independent
   certificate checking, execution-to-model correspondence and the
   soundness of verification-condition generation and check removal.
   The existing conditional adequacy proof and passing self-verification
   tests alone do not satisfy this release gate.

Status of the completion criteria: the `verify` suite runs `tests/run`
with and without verification, and checks that the proved checks of
`tests/verify/slices.jh` are absent from its IR while the unproved one
stays; `tests/fail` has a case for each rejected contract (`unproved_*`);
jihoo-proofs' CI runs the differential test against the interpreter, with
its own verdicts and the compiler's, on both targets; the design lists the
trusted parts and their sizes.

Completion: every `tests/run` program compiles with the same output, with
or without verification; proved checks are absent from optimized IR and
unproved ones remain. `tests/fail` has a case for every rejected contract
(wrong `ensures`, missing `requires` at a call, an invariant that fails on
entry or is not preserved, an off-by-one loop). The generator's
interpreter tests run in CI on both targets, and the trusted parts and their
sizes are listed in the design. Step 6's composed soundness proof and
independent certificate checks run in CI, with all remaining assumptions
and the separate compiler-correctness boundary documented.

### 7. Proofs as a library (0.6)

Proof libraries target the [native dependent core](dependent-core.md).
Users prove properties of integers, sequences and their own data by
induction (`sum(xs[0..i])` and the like), import those lemmas and use them
in program specifications. Mathematics beyond what programs need grows
as libraries of the same core terms. Preserving Horn's proof format or
its kernel API is not a requirement.

1. A theory library: natural numbers, integers, lists and slices, and the
   properties needed by standard-library specifications.
2. Lemmas in specifications: a contract that needs induction applies an
   imported theorem, checked by the same native core as its program.
3. Automation produces core proof terms; the small checker remains the
   authority, independently of the proof search strategy.
4. Compile-time evaluation fast enough for real developments, with
   explicit resource limits and measurements using
   [resource reports](../reference/command-line.md#compile-time-resource-reports).

Completion: a program proves a loop's `ensures` with a lemma by induction,
from imported library code, and the checked program is erased and lowered
from the same core. Rejection cases for the kernel, proof libraries and
erasure run in this repository's suites.

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
7. `Option`, `Result` and `?`; panics, and `#[panic_handler]` to report
   them another way.
8. `unsafe`: raw pointers, `static` globals, `extern fn` (with `...`),
   `export fn`, system calls, atomics, volatile accesses; kernel code
   without the red zone or vector registers.
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
  runtime semantics. It does not verify arbitrary generated function bodies;
  [0.6](#7-proofs-as-a-library-06) makes it a library.
- **Contracts** (which v0 had) are [0.5](#6-verification-05): obligations
  from MIR, whose semantics the generator states, checked by a small kernel.
- **Generic derives**: inferred derived bounds on generic types and
  user-written derives, when concrete library users need them.
- **Dynamic dispatch extensions**: traits with parameters, methods returning
  borrows, and borrowed trait objects without allocation.
- **Project tooling**: use the existing Nix setup while collecting concrete
  requirements for project manifests, dependency management and caching.
  A package registry is not an immediate milestone.
- **The standard library on another operating system**: a library object
  with a [`#[panic_handler]`](../language/profiles.md#embedding-in-another-system)
  makes no system calls of its own, but `std.sys` (allocation, output) is
  Linux's, libc's or UEFI's. A `std.sys` that the program supplies through
  `extern fn`s would let a custom kernel use `Vec` and `String`.
- **Tail calls** that never grow the stack.
- **Macros**, if reflection turns out not to cover what they would do.
