# Testing

```sh
jihoo run tests/runner.jh                       # everything
jihoo run tests/runner.jh -- run fail           # some suites
jihoo run tests/runner.jh -- check fail         # checking and diagnostics
jihoo run tests/runner.jh -- format             # formatting and syntax preservation
JIHOO_TEST=maps jihoo run tests/runner.jh       # the files whose path has `maps`
JIHOO_TEST_OPT=-O0 jihoo run tests/runner.jh -- run
JIHOO_COMPILER=out/jihoo jihoo run tests/runner.jh  # with this compiler
nix flake check --max-jobs 1 -L                  # what CI runs
```

Run them from the checkout, in the dev shell (`nix develop`), where
`jihoo` is the seed and `JIHOO_PATH` the checkout's `lib`.

## The runner

[`tests/runner.jh`](../../tests/runner.jh) tests a compiler:
`JIHOO_COMPILER`, else `compiler/main.jh` built by the `jihoo` that runs
the runner. Its suites:

- **format**: `tests/format.py` formats the compiler, standard library,
  examples, tests and benchmarks into a temporary tree. It checks exact
  comment bytes, syntax trees with positions removed, idempotence, golden
  output, `fmt --check` and rejection of invalid syntax. Emitted LLVM IR must
  agree before and after formatting on both targets for the compiler, runtime
  corpus and examples. Profile cases also check that spaces, line breaks and
  leading block comments do not change the freestanding attribute's meaning.
  `--external ../banana` additionally checks that
  project's source files and compares its entry point's IR. Source files in
  the checkout and external project are read without modification.
  The files of `compiler/` and `lib/` must already be formatted
  (`fmt --check`); replace a file the suite names with the output of
  `out/jihoo fmt`.
  Wrapping cases cover narrow widths, nested lists, comments, tuple and enum
  forms, and deterministic generated lists. A separate syntax-comparison
  fixture checks that return, call and index newlines and parameter modes
  remain distinct when positions are omitted. A 40-column golden and IR
  comparisons check the parameter, array and field layout together.
- **run**: every file in `tests/run/` is built and run, and its output
  compared. `//> text` lines are the expected standard output in order,
  `// exit: N` the exit status (default 0; a trap is 132), `// args: a b`
  the program's arguments, and `// link: tests/ffi/native.c` adds link
  inputs relative to the checkout.
- **check**: every file in `tests/run/` and `examples/` passes `jihoo check`
  with LLVM, C compiler, linker and backend settings pointing to unavailable
  tools. Success is silent. Additional cases cover both targets, modules
  without `main`, unresolved externals, rejected output/link/run options,
  and absence of generated files. `tests/diagnostics.py` uses Python's JSON
  parser to validate structured errors against the negative corpus and text
  diagnostics, checking both ends of source ranges, related notes, Unicode,
  invalid UTF-8, escaping and truncation. Python is supplied by the dev shell
  and Nix test derivation, not required by the installed compiler.
- **test**: `jihoo test` runs every file in `tests/test/`, with the
  directives of `tests/run`: the expected output is the list of tests,
  failures and the summary, and `// args:` holds `--` and names. Modules
  they import are in `tests/test/lib`. Every file of `lib/` with
  `#[test]` functions must then pass `jihoo test`.
- **fail**: every file in `tests/fail/` must not compile, and each
  `// error: text` must appear in the error message and no `// no-error: text`
  may. `check` must return the
  same diagnostics even with the debug `JIHOO_NO_ELAB` switch set. A file
  with a `// verify` line fails verification instead (an unproved
  contract): it is compiled with `emit-llvm`, and checked with
  `check --verify`.
- **core**: `tests/core.py` checks the dependent core's proofs, erasure and
  direct MIR lowering from both `.jhc` and marked `.jh` source on both
  targets, compares their MIR, exercises ordinary `run` and source
  diagnostics, and compares native objects with an
  independent evaluator at `-O0` and `-O2`, and requires rejection of bad
  evidence, types, scopes and ABI preconditions. Kernel unit tests also
  bypass the parser to check malformed term graphs and false evidence.
  `tests/core_bindings.py` compares record lets, including nested patterns,
  with explicit match MIR, including nested record patterns in enum arms and
  constant-result matches. It checks owned/borrowed dependent fields, nested
  inout reconstruction, discarded initializer traps, both object targets and
  native allocation balance at O0/O2, plus exact privacy, type and ownership
  diagnostics. Allocation counts do not replace memory instrumentation.
  `tests/core_functions.py` also rejects empty higher-order calls and chained
  scalar/owned/proof applications, with valid local/imported nullary factories,
  exact reference MIR, erased certificates and native ownership controls.
  `tests/core_lambdas.py` compares repeated wildcard parameters with named
  binders in callbacks, proof families and extended induction motives. It checks
  inaccessible values/evidence, owned argument drops, captured effects/traps and
  duplicate real names without changing runtime MIR.
  `tests/core_negation.py` compares computed unary negation with explicit
  subtraction MIR and checks signed boundaries, native traps, lazy branches,
  zero-iteration loops, imported map callbacks, single operand evaluation and
  exact rejection of unsigned/owned/evidence operands on both object targets.
  `tests/core_equality.py` adds equality/transport cases to this suite:
  paired source/core execution, user lemmas, proof-only elimination,
  shadowing, false equalities and incorrect rewriting.
  `tests/core_chain.py` adds a declared equality chain, structural induction,
  captured proof cases, normalization checks and rejection of forged
  hypotheses, incorrect indices, data elimination and unchecked dead cases.
  `tests/core_inductive.py` adds other declared inductive propositions and
  rejects non-positive, relevant or misordered declarations and wrong cases.
  `tests/core_loop.py` adds bounded loops and i64 arithmetic, including
  overflow traps and loop bounds checked against array lengths.
  `tests/core_order.py` adds u64 addition and the order rules: computed
  indices, prefixes, u64 traps and rules with wrong premises.
  `tests/core_sub.py` adds subtraction with evidence and its cancellation.
  `tests/core_refine.py` adds refinements: projections, kept witness traps,
  false or mismatched evidence and the export ABI.
  `tests/core_data.py` adds data types: `match`, proofs by cases, kept
  field traps, positivity of fields and motives.
  `tests/core_indexed.py` adds erased u64 indices, parameterized data
  types and, in `.jhc`, a true index.
  `tests/core_buffer.py` adds owned buffers: native calls are linked
  with counting `malloc`/`free` wrappers, and each must free what it
  allocates; leaks, double frees, uses after free and captures are rejected.
  `tests/core_sized_concat.py` checks ownership-transferring concatenation and
  imported induction inside an indexed loop, including exact erasure, linear
  allocation costs, suffix ownership and malformed imported equalities.
  `tests/core_sized_list.py` checks indexed owned-list construction and mapping,
  exact erasure against an unindexed reference, allocation costs, private fields
  and malformed imported loop/induction proofs.
  `tests/core_list_map.py` checks reusable higher-order maps and proof-bounded
  list access, with callback order, erased proofs, counted allocations, signed
  traps and malformed imported induction cases.
  `tests/core_list.py` adds recursive data on the heap: `match`,
  structural recursion, trees and parameterized lists, proofs by
  induction, and counted nodes.
  `tests/core_scope.py` adds frees inserted where ownership ends: each
  implicit program must compile to the same MIR as the one with those
  frees written out, and free what it allocates.
  `tests/core_borrow.py` adds borrows: lends and views against an
  evaluator whose borrows expire with their lend.
- **examples**: the programs in `examples/` build and run.
- **backend**: the C ABI (`tests/run/ffi.jh` and `ffi_aggregates.jh`) at
  `-O0` to `-O3` with
  both backends; an object without `main` (`emit-obj --lib`) that C links,
  statically and as a shared library, with aggregate and 128-bit signatures;
  objects cross-compiled with no C
  compiler; link errors; and a missing LLVM.
- **selfhost**: the compiler builds `compiler/main.jh`, and the compiler it
  builds writes the same `emit-llvm` output, errors included, for every
  `.jh` file in the checkout on both targets
  ([Self-hosting](self-hosting.md)).
- **uefi**: the programs of `tests/uefi`, and those of `tests/run` that need
  nothing UEFI lacks (files, processes, threads, arguments, dynamic
  libraries), are built as `#![uefi]` programs for x86_64, with their C link
  inputs compiled by clang for `x86_64-unknown-windows`, and checked to be
  PE images for the machine; some are also built for aarch64. Given
  `JIHOO_QEMU`, `JIHOO_OVMF` and `JIHOO_UEFI_SHELL`, one QEMU boot runs
  them all: the UEFI shell runs a `startup.nsh` that writes each program's
  standard output, standard error and `%lasterror%` to files, and the
  runner compares them with the `//>` lines and `// exit:`. Without those
  variables the programs are only built.

`nix flake check` runs every suite with the installed compiler; on x86_64
it sets the UEFI variables. In a checkout, `nix develop .#uefi` is the dev
shell with them:

```sh
nix develop .#uefi -c jihoo run tests/runner.jh -- uefi
```

Unit tests of the standard library are `#[test]` functions at the end of
its files (`out/jihoo test lib/std/string.jh`).

Add a `tests/run` program for every feature and every bug fixed, and a
`tests/fail` one for every error the compiler should give, in particular
every way the borrow rules can be broken.

## Memory

Programs should neither leak nor touch memory they do not own. Build with
`-O0` and run them under valgrind:

```sh
jihoo build -O0 tests/run/maps.jh -o /tmp/maps
nix-shell -p valgrind --run 'valgrind --leak-check=full --error-exitcode=9 /tmp/maps'
```

## Other machines

`jihoo build --target aarch64` cross-compiles; freestanding programs run
under `qemu-aarch64` (`nix-shell -p qemu`). The aggregate C ABI test can
also run without libc on either target; the C oracle only needs Clang's
freestanding headers:

```sh
{ echo '#![freestanding]'; cat tests/run/ffi_aggregates.jh; } > /tmp/ffi-aggregates.jh
clang --target=aarch64-linux-gnu -ffreestanding -fno-stack-protector -O2 \
  -c tests/ffi/aggregates.c -o /tmp/ffi-c.o
out/jihoo build --target aarch64 /tmp/ffi-aggregates.jh /tmp/ffi-c.o -o /tmp/ffi-arm
qemu-aarch64 /tmp/ffi-arm
```

`compiler/cabi.jh` implements the classification described by the
[AMD64 psABI](https://gitlab.com/x86-psABIs/x86-64-ABI/-/blob/master/x86-64-ABI/low-level-sys-info.tex),
[AAPCS64](https://github.com/ARM-software/abi-aa/blob/main/aapcs64/aapcs64.rst)
and, for UEFI on x86_64, the
[Microsoft x64 convention](https://learn.microsoft.com/en-us/cpp/build/x64-calling-convention);
the uefi suite runs `ffi_aggregates.jh` against the C oracle compiled for
Windows.

A UEFI program for aarch64 runs in `qemu-system-aarch64 -M virt` with
ARM firmware, such as the `edk2-aarch64-code.fd` that QEMU ships, whose
internal shell runs `startup.nsh` from the first FAT disk:

```sh
out/jihoo build --target aarch64 examples/uefi.jh -o esp/uefi.efi
printf 'fs0:\r\nuefi.efi\r\nreset -s\r\n' > esp/startup.nsh
qemu-system-aarch64 -M virt -cpu max -nographic \
  -bios $QEMU/share/qemu/edk2-aarch64-code.fd \
  -drive format=raw,file=fat:rw:esp,if=virtio
```
The C oracle exercises mixed register classes, homogeneous aggregates,
register exhaustion and rollback, stack alignment, independent argument
copies, callbacks, dynamic symbols, and variadic promotions and aggregates.

## Backend performance

```sh
jihoo build -O2 compiler/main.jh -o out/jihoo
python3 scripts/benchmark_backends.py --compiler out/jihoo --selfhost --json /tmp/backends.json
```

The script builds the same runtime workloads through LLVM's C API and
clang at `-O2 --release`, keeps bounds checks, checks their output, warms
up both executables, and alternates run order. It reports median runtime
for recursion, a sieve, matrix multiplication and floating point loops,
and median compilation time. `--selfhost` also builds the compiler with
each backend and compares its IR and frontend runtime. Runtime regressions
above `--max-regression` (10% by default) cause failure. Use an idle machine
and the same LLVM/clang version and linker driver for both paths; small
differences need repeated measurements.

## Functional pipelines

```sh
python3 benchmarks/functional-fusion/run.py --compiler out/jihoo --iterations 128
```

This compares ordinary higher-order functions, comptime producers, the
public iterator API, eager vectors, a handwritten jihoo loop, and C. It
checks randomized results at O0/O2 with checked/wrapping arithmetic, records
allocations and optimized IR, and measures interleaved runtimes. See the
[benchmark](../../benchmarks/functional-fusion/README.md) for the method,
recorded results, and the filter/fold fusion optimization. The program
suite additionally checks callback order, trap order, ownership,
streaming parsers using `take` and `zip`, and compile-time use.

`--check-only` runs the correctness, allocation and optimized-IR checks
without timing samples or thresholds. CI runs it with the packaged compiler
on x86_64 and aarch64 Linux and keeps `out/functional-fusion/results`.

## Compilation time and memory

```sh
jihoo build -O2 compiler/main.jh -o out/jihoo
python3 scripts/benchmark_compile.py --compiler out/jihoo --json /tmp/compile.json \
  --baseline benchmarks/compile/baseline-x86_64.json
```

The script measures each workload twice: `jihoo check` (loading, types,
compile-time evaluation, moves, drops and borrows) and full compilation
(`build` at `-O2` for the host, `emit-obj` for another `--target` or a
module without `main`). The built-in workloads are the compiler itself,
[a compile-time generation program](../../benchmarks/compile/comptime.jh)
(tables, maps, sorting and derived code evaluated by the interpreter),
[200 calls of `std.fmt`](../../benchmarks/compile/format.jh) whose literal
patterns are each checked while compiling, and the fusion benchmark's
iterator kernels. `--proofs ../jihoo-proofs` adds that
repository's proof and codec examples, and `--external NAME=ENTRY[:INCLUDE...]`
any other program, such as Banana's entry point; their revisions are
recorded too.

Every sample is a new compiler process run through GNU `time` (in the dev
shell), so peak resident memory belongs to the compiler rather than to the
Python process that started it. Samples of all cases are interleaved. The
report records the compiler's revision (marked `-dirty` when `compiler/`,
`lib/` or `benchmarks/` differ from it) and version, each case's command,
target and options, the host, every sample and the medians.

`--baseline` compares median elapsed time and median peak memory with a
recorded report and fails when either grows by more than 10%
(`--max-time-regression`, `--max-memory-regression`); time differences under
20 ms are ignored. Compare only reports taken on the same idle host;
`benchmarks/compile/baseline-x86_64.json` is one such recording, a reference
for that host rather than a threshold for others. `--check-only` runs every
case once and checks that it succeeds, that `check` prints nothing and
creates no files, and that full compilation writes its output, without
thresholds. CI runs it for both targets with the packaged compiler.

`--time-passes` adds the compiler's own
[phase timings](../reference/command-line.md#phase-timings) to every sample
and their medians to each case, and prints them; against a baseline that
recorded them too, each phase's elapsed ratio is printed, without
thresholds. Use it to see which phase a change moved: the totals stay the
measure that `--baseline` checks.

```sh
python3 tests/time_passes.py --compiler out/jihoo
```

The check suite validates the table, that its phases add up to the total,
and that output, objects, statuses and diagnostics are the same without it.

## Compile-time resource measurements

```sh
python3 tests/comptime_report.py --compiler out/jihoo
```

The check suite validates the report schema and source spans, accounting
totals, unchanged LLVM IR, and step/memory/depth and invalid-memory failures.
The [jihoo-proofs](https://github.com/jihoolang/jihoo-proofs) repository
uses these reports to measure its checked codec construction at 4 to 256
variants.
