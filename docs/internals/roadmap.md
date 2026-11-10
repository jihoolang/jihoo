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

0.5.0 is the completion of dependent types in jihoo itself, and formally
verifying the compiler comes after 0.5.0.

Direction revised: the replacement is a
[native dependent core](dependent-core.md). Programs and their proofs
are checked together, then erased and lowered directly from those terms
to MIR. The earlier path, which recreated the MIR program as Horn rules and
checked the result in Agda, was removed before 0.5.0 and is in the repository's
history.

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
(5) borrows, reading without consuming.

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

Implemented step (4), frees where ownership ends: in source, an owned
value that a scope (a function, a match arm, a load's continuation, a
loop body or a recursion case) does not use is freed there, and an
owned value that one alternative of a branch, `match` or flat `induct`
uses is freed at the start of the others. `free(v, rest)` also frees
heap data, through one new kernel term, `Drop(F, v, rest)`, which frees v
and every node it owns; lowering makes one drop function per type. The
kernel checks the inserted frees with the same exactly-once count, so
the elaborator stays untrusted. `examples/core_scope.jh` writes no
`free` and compiles to the same MIR as `examples/core_scope.jhc`, which
writes them out, as do twelve more implicit/explicit pairs; native
execution counts allocations and frees, valgrind finds none left, and
10 source and 8 core rejections and kernel tests run in the `core`
suite.

Implemented step (5), borrows: a `ref T` parameter reads a buffer or
heap data without consuming it, passing an owned local lends it for the
expression or `let` value that borrows it, and `match`, `induct` and
`index` read borrows in place. The kernel adds `Ref(T)`, `Lend(x, f,
g)`, whose f reads x through a borrow and returns no borrow or function
before g gets x back, and `View`, one-level or recursive reading that
frees nothing; the elaborator, untrusted, finds the lends.
`examples/core_borrow.jh` compiles to the same MIR as the hand-written
`examples/core_borrow.jhc`; its recursions over borrows call no `free`.
Native execution counts allocations and frees against an evaluator whose
borrows expire with their lend, valgrind finds none left, and 21 source
and 15 core rejections, five whole programs and kernel tests run in the
`core` suite. A review by Codex found that a type variable could stand
for a borrow or an owned type, and that a continuation given owned
values could return a closure holding them (the latter since step 1);
type arguments at run time are now first order and such continuations
return no function. This completes the memory plan.

Implemented borrows in types and evidence
([design](dependent-core.md#borrows-in-types-and-evidence)): a function
that reads a borrow, such as `length(xs: ref List)`, applies in types
and proofs to any value, including a temporary or a value moved or
freed meanwhile. One kernel term, `Borrow(x)`, borrows an owned value
in types and evidence only, where nothing runs or is lent; conversion
computes a view of a known node and a lend as its continuations applied
to such a borrow, while code to run keeps both. `doubled_length` is
proved by induction about a borrowing `length`, `length(pair(x)) = 2` and
a function that lends a local list compute by `refl`, and preconditions
mention the lists their functions consume. `examples/core_borrow_proof.jh`
compiles to the same MIR as its `.jhc`, with every proof erased; native
execution against the evaluator, counted allocations, valgrind, 7 source
and 6 core rejections and kernel tests run in the `core` suite. An
independent review (Codex) found no unsound case and one evidence
position the elaborator missed, now fixed.

Implemented dependent lends
([design](dependent-core.md#dependent-lends)): when a lend lends a
variable, its reader is checked with the borrow equal to `Borrow(x)`,
and its continuation with the owner given back equal to x, which the
continuation uses exactly once instead of the lend. Lowering is
unchanged. `examples/core_lend.jh` reads a buffer at a list's length
without a bounds check, from a precondition about the owner or from a
size whose type mentions it; its MIR equals the `.jhc`'s, and native
execution against the evaluator, counted allocations, 6 source and 10
core rejections and kernel tests run in the `core` suite.

Implemented induction over a borrow
([design](dependent-core.md#induction-over-a-borrow)): `induct` into a
proposition on a borrow proves by induction about the value it reads.
One kernel term, `Deref(r)`, is that value, in types and evidence only,
with `Deref(Borrow(x)) = x` and `Borrow(Deref(r)) = r`.
`examples/core_borrow_induct.jh` proves `twice(xs) = length(xs) +
length(xs)` for a borrowed list and uses it to read a buffer at
`twice(xs)` without a bounds check; its MIR equals the `.jhc`'s, and
native execution against the evaluator, a lemma about borrowed trees, 6
source and 5 core rejections and kernel tests run in the `core` suite.

Implemented views whose result depends on the borrow
([design](dependent-core.md#views-whose-result-depends-on-the-borrow)): a
view's result may be a motive over the borrow, whose cases compute it at the
node they read, and may be a function, so arguments change along a recursion;
a `match` on a borrowed variable refines the evidence that mentions it, and
into a proposition is a proof by cases. `absurd(p)`, from evidence of `Lt(i,
0)`, closes a case that cannot run. `examples/core_nth.jh` reads the i-th
element and the head of a list with evidence and no bounds check, and counts
nodes in a recursion that returns its evidence; its MIR equals the `.jhc`'s,
and native execution against the evaluator, counted allocations, 11 source and
15 core rejections with their reasons and kernel tests run in the `core`
suite.

Implemented loops whose invariants are types
([design](dependent-core.md#loops-whose-invariants-are-types)):
`fold(n, fn(k) { T(k) }, init, body)` turns `T(i)` into `T(i + 1)`, and into a
proposition is a proof by induction on the naturals.
`examples/core_invariant.jh` reads a table at a count bounded by its loop's
invariant, with no bounds check, and proves `Even(n + n)`; its MIR equals the
`.jhc`'s, and native execution against the evaluator, counted frees, 8 source
and 12 core rejections with their reasons and kernel tests run in the `core`
suite.

Implemented inout parameters
([design](dependent-core.md#inout-parameters)): `inout b: buffer(n)` changes a
value its caller keeps, `f(&b)` rebinds it and `old(b)` is its first value in
types and evidence. A function takes the owner and gives it back with its
result, through three kernel terms, `Back`, `Give` and `Take`; the owner moves
in and out, so the existing count of uses is the safety argument and the kernel
gains no mutable reference. `examples/core_inout.jh` changes buffers in place
with no bounds check; its MIR equals the `.jhc`'s, and programs with branches,
two owners and heap data run natively with counted allocations. `xs =
List.Cons(x, xs)` assigns, a `match` on an owned list refines what the function
promises, and a node rebuilt at its own size is reused in place, so `push` and
`pop` prove what they do to a list's length and a recursion that rebuilds a list
allocates nothing. 29 source and 22 core rejections with their reasons, and 26
more from an independent review (Codex) that found no unsound case and one
program only lowering rejected, now the kernel's, run in the `core` suite.
Changing the i-th element of a list still walks all of it, since a recursion on
owned data has no function result; a buffer changes any element directly.

Implemented a vector with contracts as types
([design](dependent-core.md#a-vector-with-contracts-as-types)):
`lib/dependent/vec.jh` is a growable vector of i64, an owned buffer with its
length and capacity, whose `get`, `set`, `push`, `drop_last` and `clear` state
their `requires` as erased evidence and `ensures` as result types. Data may hold
buffers, source has `struct`s whose fields name earlier fields, a `match` on an
owned variable refines evidence, and marked modules import marked modules.
`examples/core_vec.jh` reads and writes with no bounds check; native runs against
a model with counted allocations, valgrind on the example, and 16 source, 2 module
and 10 core rejections with their reasons run in the `core` suite, with 23
rejections and 15 accepted programs from an independent review (Codex) that found
no unsound case and one leak in lowering, now fixed. Vectors of other element
types wait for type parameters in the core, after 0.5.0.

#### The 0.5.0 release gate for the native core

0.5.0, released on 2026-11-06, is the completion of dependent types: what programs
can state and check in the core. Proofs about the kernel itself come after it, by
the decision of the same day to release it sooner.

With the native core, what must be trusted is the kernel (`compiler/core.jh`),
erasure and lowering (`core_lower.jh`), so the gate is stated for them. The
existing verifier keeps verifying unmarked programs and the compiler's own source
until the core replaces it. 0.5.0 requires:

1. **Coverage.** The 0.5 promise, that the checks code needs cannot fail
   and functions meet their contracts, holds for programs in the core:
   indexing without bounds checks (done: arrays, buffers, borrowed
   buffers), contracts as types (`requires` as erased evidence, `ensures`
   as refined or equality results), loops whose invariants are types,
   and enough ownership for ordinary code. Done: (a) dependent lends
   ([design](dependent-core.md#dependent-lends)): a lend of a variable
   is checked with its borrow reading the owner and the owner given back
   as itself, so evidence about the owner holds of the borrow and after
   the lend, and a borrowing call's result type may mention the owner.
   Done: (b) proofs by induction over a borrow
   ([design](dependent-core.md#induction-over-a-borrow)), an induction
   over the value the borrow reads. Done: (c) case analysis and recursion
   over a borrow whose result type depends on it
   ([design](dependent-core.md#views-whose-result-depends-on-the-borrow)),
   such as reading the i-th element with evidence that i is below the
   length. Done: (d) loops whose invariants are types
   ([design](dependent-core.md#loops-whose-invariants-are-types)). Done: (e)
   [inout parameters](dependent-core.md#inout-parameters), which change buffers
   and heap data in place. Done: (f)
   [a vector](dependent-core.md#a-vector-with-contracts-as-types) as an owned
   buffer with its length and capacity, with its contracts stated as types.
2. **Specification.** Done: [the core specification](core-spec.md) describes the
   terms, typing with quantities (erased, owned, scalar) and the ghost position,
   the pure model's reductions and erasure, one entry per term of `infer` and
   `normal`. `tests/core_spec.py` fails on a term without an entry and tests
   preservation on the core examples. An independent review (Codex) against the code
   gave 28 corrections and two findings in the code: loop eta-expansion that made
   normal forms ill-typed, fixed, and branches without a motive. The latter is
   addressed by the first 0.6 stabilization step below.

For 0.6, complete and stabilize the dependent-type kernel first, then
mechanize its soundness, starting from that specification:

1. **Dependent-type stabilization.** Started: pure normalization retains
   dependent elimination and view motives on symbolic branches, while runtime
   lowering still distributes data cases. The core examples and preservation
   fixtures must all recheck, with no expected preservation failures. This
   fixes the known branch-normalization gap, not the whole 0.6 milestone.
   Sum ordering now ignores exactly the evidence that conversion ignores, so
   replacing an irrelevant proof inside nested subtraction cannot make equal
   sums fail to convert. Source, textual-core and raw-kernel tests check this
   congruence boundary while retaining rejection of different runtime operands
   and malformed proof graphs.
   Explicit indexed record literals now supply their own checked context,
   including imported and nested records. Contextual and explicit constructions
   lower identically; malformed indices and duplicate/unknown fields are rejected.
   This changes source elaboration, not the kernel or its soundness coverage.
   Flat constructor fields that touch memory now sequence through scalar bindings
   during runtime normalization, so repeated/discarded records preserve effects
   without acquiring a heap layout. Paired source/core/explicit-binding tests
   check this boundary; flat results crossing continuations remain restricted.
   Continue auditing conversion, substitution, erased indices, indexed
   elimination and ownership boundaries against accepted and rejected programs.
   Record remaining source-subset restrictions and settle the kernel rules
   before proving them; retain both-target execution and self-hosting checks.
2. **Kernel soundness, mechanized.** A proof in Lean 4, checked in CI, of
   the specified rules: logical consistency (no closed evidence of
   `Lt(0, 0)`), preservation of types by the pure model's reductions, and
   quantity soundness: in the erased program every owned value is used
   exactly once and no borrow outlives its lend. The kernel's
   implementation is tested against the specification (independent
   evaluator, rejection suites, independent reviews), and remains
   trusted to implement it. Started: [the Lean arithmetic fragment](lean-proofs.md)
   proves open-context evidence soundness, absence of closed `Lt(0, 0)`, and
   semantic soundness and substitution stability of a selected conversion
   relation. A second extrinsically typed index-dependent calculus proves
   capture-avoiding index substitution and beta preservation, including nested
   binders and dependent result instantiation. Value lets now have a separate
   capture-avoiding substitution theorem, and an independent finite-scoping
   judgment excludes dangling indices and value variables while preserving
   typing through reduction. Conversion now participates throughout typing and
   preservation; a classical logical interpretation proves no closed false
   bound or equality evidence for this calculus. The value lets remain
   nondependent, general value domains remain open, and this interpretation
   establishes inhabitance rather than operational adequacy. CI checks the
   proofs and their axioms. A [representation bridge](core-bridge.md) now maps
   a bounded annotated subset to unified core constructor trees, with scope,
   renaming, literal-bound and closed-subtraction certificate proofs plus
   Lean-generated implementation fixtures. A restricted annotation-checking source
   judgment translates to independent ghost-mode target typing, with proved
   codomain substitution correspondence. It is not an executable-checker proof. This is not full-core consistency or preservation, quantity soundness
   or a refinement proof for `core.jh`; those remain open.
   [Graph artifact certificates](graph-certificates.md) now check exported
   shift/substitution snapshots against the formal operations. They certify
   artifacts with a trusted exporter/run association, not all checker executions.
   Canonical byte roundtrip/injectivity and checked replay chains narrow artifact
   identity to exact bytes, graphs and roots, without proving the importer or
   execution path. Target renaming, typed substitution and head-beta retyping
   connect accepted structural transforms to conditional output typing, without
   changing conversion rules. Fixed-type contextual beta preservation does not
   hold for that deliberately restricted conversion relation. A separate beta-aware
   target extends conversion and proves contextual beta preservation, including
   dependent arguments and annotations, via confluence and context transport.
   This does not prove the executable checker implements that relation, or cover
   all core reductions, runtime effects, erasure or lowering.
   A strict evaluation strategy for that same restricted target now proves
   closed progress modulo explicit unsigned-addition overflow and fixed-type
   preservation for every finite execution. Ordinary arguments and array entries
   retain their evaluation; proof arguments are erased. This does not cover the
   whole specified core or prove native evaluation/erasure correspondence.
   An intermediate annotation/proof-payload erasure now commutes with typed-core
   syntax substitution and forward-simulates strict steps, values and traps.
   It retains binder slots and uses an untyped Raw carrier; complete ghost-slot
   deletion, reverse execution correspondence and native lowering remain open.
   [Checked typing artifacts](typing-certificates.md) independently validate
   closed typing/formation derivations for exact exported graph roots, with
   explicit conversion evidence. The producer is untrusted for artifact typing;
   exporter/source association and all-program checker refinement remain open.
   The ownership control model additionally proves checked usage preservation
   through ghost computation removal and erased-binder slot compaction, with
   bidirectional finite-trace correspondence and exact-once/at-most-once guarantees for all
   transformed control executions. This is not native Core erasure or value
   correspondence; those release obligations remain open.
   A capture-layout model now proves reconstruction of mixed ghost, value and
   recursive-hypothesis environments and conditional caller/callee lookup
   agreement. Native frame construction and MIR call semantics remain trusted
   and tested, not formally refined by that result.
   A composed ownership endpoint now connects those layouts to ghost erasure
   and checked usage through an injective source-slot-to-operand map. Its
   guarantees cover all transformed control traces and reconstructed callee
   values, conditional on authentic projection and positional argument assignment.
   The missing native trace/heap interpretation still prevents a full release claim.
   Sequential parameter numbering and a concrete positional entry store now
   discharge the decoder/assignment assumptions inside that model. Current-module
   MIR probes test contiguous typed parameter locals and recursive call arities;
   native execution fidelity to the modeled entry rule remains unproved.
   A primitive heap/lease semantics now supplies allocation identities, permanent
   lease expiry, invariant preservation, no double free and a nested-reader
   payload frame theorem. Exact free-event observations connect checked quantity
   traces to actual deallocation, conditional on authentic trace projection.
   Whole-Core typing must still establish lease authority/non-escape and the
   transition preconditions; recursive heap fields and native simulation remain
   open. This does not add checker-implementation refinement as a release gate.
   A structured scalar-reader Lend fragment now derives reader authority,
   primitive heap steps and an exact free-event/control projection. Its
   original/returned owner alternatives instantiate the existing quantity rule;
   a complete execution frees that allocation once and expires its local token.
   Full-Core graph/context correspondence, owned reader results and nested-source
   ownership threading remain open; no full-language release claim is made.
   A bounded original-constructor graph bridge now derives the scalar Lend
   fragment from exact roots, annotations and lexical roles. Forward/reverse
   correspondence makes its heap endpoint apply to every admitted constructor
   execution. The constructor semantics remains restricted; native export fidelity,
   general ownership contexts and the broader specified-Core rules remain open.
   Finite allocation/admitted-call programs now thread distinct live, lease-free
   capabilities, derive callee guards and conserve concrete allocation/free IDs.
   Closed complete executions release every allocation and leave no live heap
   object. General native caller translation, allocation failure, recursive
   fields and the rest of the specified runtime remain outside this result.
   Original finite caller graphs now recognize literal allocation/App/Lam
   spines, preserve concrete lexical-owner identities across consumption, and
   prove all-run closed heap safety. This restricted heap-effect subset retains
   exporter trust and does not discharge general caller/result/lowering adequacy.

3. **Erasure and lowering.** A proof that the erased program computes
   the pure model's value, and a statement of lowering to MIR against
   a semantics of MIR stated in Lean, proved for the core's runtime fragment (scalars, arrays, buffers,
   heap nodes, cases, recursions, views, lends, frees). Differential
   tests remain regression checks, not this proof.
4. **The published theorem.** What an accepted core program is
   guaranteed to do, under which semantics, and what stays trusted: the
   kernel's implementation, lowering where not proved, MIR to LLVM, LLVM
   and the runtime. The elaborator is untrusted, since the kernel checks
   its output. Until source-to-MIR and MIR-to-LLVM preservation are
   proved, this is not described as verification of whole executables.

Until those are done, 0.5.0's soundness rests on testing: the independent
evaluator, rejection suites with their reasons, and reviews. Its release notes
say so, and it is not described as a verified kernel.

Self-verification also comes after 0.5.0: the compiler verifying its own
source with the existing verifier continues in CI, and the compiler's
code moves into the core only once the core covers it (item 1).

The `.jhc` prototype does not complete the 0.5 release gate. The existing
verifier and its gaps described below remain applicable to unmarked `.jh`
programs until their supported operations and guarantees move to the core.
Only the explicit pure source subset bypasses legacy VC generation today;
no broader legacy path is retired by this slice.

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
6. Self-verification (no longer a release requirement: see
   [the native core's gate](#the-050-release-gate-for-the-native-core)): jihoo verifies jihoo, as lean4lean
   checks Lean with a kernel written in Lean and proves that kernel's
   properties in Lean. First, the compiler verifies its own source:
   `jihoo verify compiler/main.jh` runs in CI and every check it keeps is
   listed with its reason, while `std` and compiler contracts raise the
   share proved; the `verify` suite fails when it proves fewer of any kind
   than `tests/verify/compiler.proved` records. Then the trusted parts verify themselves: the checker
   (`linear.jh`) and the generator (`vc.jh`) state contracts, proved by the
   compiler they are part of, until no check is left in the checker. Started
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
   modes. A proof of the checker's soundness, through Horn and Agda, was
   done here and removed with that path before 0.5.0: the core has its own
   proof to come, in Lean 4, and a proof of `linear.jh` would not carry over.
7. The releases. A 0.4.x release that parses contracts lets `lib/std`
   state its contracts (step 5) before 0.5.0, since the seed compiles
   `lib/std`; contracts' syntax is fixed from then on. 0.5.0 comes when
   jihoo can verify its own compiler, and the seed moving to it lets the
   compiler state contracts itself. 0.4.6 verifies every build and makes
   an unproved contract an error, so with it as the seed, stage 1 is
   verified too. 0.5.0 waits for
   [the native core's gate](#the-050-release-gate-for-the-native-core).
   Passing self-verification tests alone do not satisfy it.

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
sizes are listed in the design.

### 7. Proofs as a library (0.6)

Bounded `auto()` now constructs ordinary Eq/Lt evidence from visible local facts
and explicit hints, including imported induction lemmas. Generated terms are
checked against their original goal before use; no kernel inference rule changes.
The acceptance example composes a proof-producing loop and imported structural
lemma for a bounded read. Search has explicit fact/depth/work/node limits and
remains incomplete; this starts automation, not general `ensures` or automatic
induction. Exact erasure, forged producer inputs and resource exhaustion are tested.


`dependent.vec_bulk.extend` appends a borrowed buffer with an old-to-new length
postcondition. It reuses available capacity or copies the prefix into exact-fit
storage, and callers compose its evidence across mutations. An acceptance
example supplies a buffer through imported structural list materialization
before two extensions. Tests cover proof erasure, stale evidence, source
independence and measured allocation costs; no amortized growth or pointwise
content theorem is claimed.

Structural list-to-buffer transfer now preserves a single destination owner
through imported recursion, with capacity evidence for every write. Sized
results convert without a length-discovery pass; bounded collections materialize
as existing vectors with exact runtime length/capacity and a checked length
lemma. Tests cover erasure, allocation costs, source independence and rejected
evidence. Pointwise content preservation remains a regression-tested boundary.

`dependent.collect` adds variable-cardinality construction: a Keep/Skip callback
produces a private exact-length payload and a runtime count proved no greater
than the input count. The indexed loop transfers or extends its owner while
maintaining this bound; a consumer uses it for a subsequent array read. Exact
erasure, skipped callback effects, ownership, allocation costs and rejected
invariants are tested. This is not a pointwise membership theorem or ordinary
`ensures` syntax.

`dependent.range.copy_into` now reuses an existing destination owner, and
`move_within` supports overlapping ranges with directional copying through one
owner. A compositional subrange lemma supplies bounds to the acceptance example.
Exhaustive small snapshot models, exact erasure and allocation/ownership tests
cover these slice-library operations; pointwise contents remain a tested boundary,
not a formal content theorem or a new kernel rule.

`dependent.range` supplies proof-bounded owned buffer snapshots and a reusable
offset-bound theorem. Its runtime copy loop applies imported evidence to each
read; the result retains its exact count in its buffer type. Tests compare exact
erasure to primitive proofs, model small ranges and owner independence, and
reject invalid bounds and malformed imported lemmas. This starts slice-library
work with explicit copies, not stored borrowing views or generic elements.

`dependent.sized_list.tabulate` now constructs exact-length lists directly
from bounded-index callbacks. Buffer and proved-range conversion reuse the
imported mirror/offset lemmas, with no intermediate buffer or repeat-then-map
pass. Callback order, traps, erasure, owner independence and real allocation
costs are regression-tested; this is not a pointwise content theorem.

`dependent.sized_list` packages an owned list with a private erased length
proof in `Sized(n)`. Its runtime repeat loop maintains `Sized(iteration)`;
imported structural map evidence preserves the index for subsequent bounded
reads. Exact MIR agrees with an unindexed wrapper reference, while native
allocation tests state the real wrapper overhead. This supplies a typed loop
postcondition and imported induction in one executable library consumer, not
ordinary `ensures` syntax or full mechanized soundness. Indexed `append_into`
now transfers an owned suffix and copies only a borrowed prefix. The repeated
pair example uses its imported structural lemma in each runtime loop step to
establish `Sized(iteration + iteration)`, with exact erasure against an unindexed
reference and linear allocation regressions.

`dependent.list` supplies owned i64 lists, borrowing observations, clone/append
operations, proof-bounded head/nth access and higher-order map with structural
length theorems. Imported append/map lemmas prove executable array bounds.
Map preserves element order while invoking callbacks tail-to-head; callback
allocation traces, ghost erasure and overflow/underflow are regression-tested.
Both-target object tests, native O0/O2 models and counted allocations cover the runtime operations; unused malformed imported induction
cases are rejected. This fills an initial list-theory library slice, not the full
0.6 completion criterion or a mechanized compiler soundness proof.

`dependent.nat` now supplies reusable equality, order and subtraction lemmas,
plus a finite `Steps` relation with structurally proved bounds and translation.
The executable `core_nat` example uses imported induction to derive an array bound
from a runtime loop's dependent invariant. Tests compare its erased MIR with an
independent primitive-proof implementation, check both object targets and u64
boundaries, and reject invalid evidence and unused malformed induction cases
with exact diagnostics and exported positive controls. `dependent.vec` reuses the
shared lemmas without removing its existing API. This advances typed library
specifications; ordinary `requires`/`ensures` syntax remains unsupported in marked
modules, and no full native-core or compiler soundness theorem is claimed.


Fully annotated local dependent functions now synthesize their Pi telescope and
can be called directly or partially applied. Their domains, result and body are
checked, including discarded evidence and unused functions. Runtime normalization
distinguishes passing a lambda value from invoking its body, preserving effects
before value creation and on invocation. Tests compare local and named function
MIR, exercise both object targets and native ownership/traps, and require intended
rejection diagnostics with an exported positive control. Missing annotations,
zero-argument lambdas, owned captures and unrestricted runtime closures remain
outside this increment; no general elaborator or runtime soundness theorem follows.


Explicit dependent constructor qualifiers, `Slot(n).Empty` and
`Slot(n).Full(value)`, now supply field context without requiring a local type
annotation. They preserve erased parameters, module identity/private boundaries
and ownership, with checks before annotation normalization. The regression suite
compares their MIR to contextual construction and checks both targets, native
execution and invalid proofs. This changes source ergonomics, not the core rules
or the scope of the mechanized soundness results.

Nested irrefutable record lets now elaborate through hygienic intermediate
bindings and existing case elimination. Whole-pattern duplicate names are
rejected before any binding enters scope; each nested level retains dependent
indices, evidence, privacy and ownership checks. The regression suite compares
nested patterns with explicit matches, including borrowed and inout values,
checks deep/reordered patterns and allocation balance, and preserves initializer
traps. Nested irrefutable record patterns also work inside match arms, including
indexed enum payloads, using the same hygienic expansion. Outer exhaustiveness
is unchanged, and duplicate names across an entire arm are rejected. Tests
compare explicit nested matches, conditional owned/borrowed payloads and
constant-result inference. Refutable subpatterns and general pattern inference
remain outside this change. No kernel rule or Lean claim changes.

Empty higher-order applications now reject rather than silently returning the
callee unchanged, including chained scalar, owned and erased results. Only a
direct declared call whose source arity is checked may have no arguments.
Regression controls preserve local/imported nullary functions, callback factories,
erased certificates and fresh owned results, with exact MIR and native allocation
checks. This closes a source arity-validation gap, not a kernel soundness claim.

Repeated wildcard parameters are now consistent across contextual and annotated
lambdas, proof families and extended data motives. Each `_` is a distinct,
inaccessible binder; named duplicates remain errors. Regression tests compare
named/wildcard MIR, prove ignored fields still enforce ownership/evidence, and
exercise captured effects, traps, folds and structural induction. This is a
source ergonomics change with no new kernel rule or formal soundness claim.

Computed i64 unary negation now lowers to the existing checked subtraction
operation rather than rejecting every nonliteral operand. The signed minimum
literal retains its special parsing path; negating that value at runtime traps.
Exact-MIR, boundary, ignored-result, partial-capture and owned-effect regressions
check single evaluation and distinguish lazy branches/zero-iteration loops from
executed arithmetic. No kernel or Lean rule changes.

Compound call stabilization accepts function-producing blocks directly, with
scope, partial-capture ordering, erased proofs and existing single-use ownership
semantics. Function-valued match results remain rejected by the continuation
boundary, with a precise diagnostic instead of a false missing-field error;
real constructor arity failures retain their own checks. Paired references,
allocation/effect traces, traps and exact negative diagnostics cover both paths.
No kernel continuation rule is weakened and no new soundness claim is made.

The final source stabilization pass infers constant match results and conditional
results without a local annotation, validates conditional result annotations,
and reconciles historical design notes with the normative core specification.
Dependent motives still require context; no kernel term or typing rule changes.
Formalization starts with the explicit boundary in `core-spec.md`, not a claim
that the current tests prove soundness.

The first step is stabilizing dependent types and their source ergonomics;
mechanized soundness in Lean 4 follows that stabilization, before claiming the
kernel is verified. Completed preparation includes preservation of dependent
motives during pure normalization, proof-irrelevant sum ordering, and contextual
source elaboration: scalar literals take their type from either arithmetic
operand, contextual lambdas accept checked annotations, and extended data
motives reject duplicate binders. The annotation regressions check invalid
proofs before conversion, exact erasure, both targets and native execution.
Module stabilization now records declaration provenance, separates imported
namespaces, enforces public items and struct fields, and checks qualified pattern
identity. Regression modules reuse helper/type/constructor names, preserve opaque
APIs, and reject visibility bypasses through induction or discarded binders.
These improvements do not themselves constitute a soundness proof.

Proof libraries target the [native dependent core](dependent-core.md).
Users prove properties of integers, sequences and their own data by
induction (`sum(xs[0..i])` and the like), import those lemmas and use them
in program specifications. Mathematics beyond what programs need grows
as libraries of the same core terms.

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
