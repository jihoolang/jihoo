# Testing

```sh
jihoo run tests/runner.jh                       # everything
jihoo run tests/runner.jh -- run fail           # some suites
jihoo run tests/runner.jh -- check fail         # checking and diagnostics
JIHOO_TEST=maps jihoo run tests/runner.jh       # the files whose path has `maps`
JIHOO_TEST_OPT=-O0 jihoo run tests/runner.jh -- run
JIHOO_COMPILER=out/jihoo jihoo run tests/runner.jh  # with this compiler
nix flake check                                 # what CI runs
```

Run them from the checkout, in the dev shell (`nix develop`), where
`jihoo` is the seed and `JIHOO_PATH` the checkout's `lib`.

## The runner

[`tests/runner.jh`](../../tests/runner.jh) tests a compiler:
`JIHOO_COMPILER`, else `compiler/main.jh` built by the `jihoo` that runs
the runner. Its suites:

- **run**: every file in `tests/run/` is built and run, and its output
  compared. `//> text` lines are the expected standard output in order,
  `// exit: N` the exit status (default 0; a trap is 132), `// args: a b`
  the program's arguments, and `// link: tests/ffi/native.c` adds link
  inputs relative to the checkout.
- **check**: every file in `tests/run/` and `examples/` passes `jihoo check`
  with LLVM, C compiler, linker and backend settings pointing to unavailable
  tools. Success is silent. Additional cases cover both targets, modules
  without `main`, unresolved externals, rejected output/link/run options,
  and absence of generated files.
- **fail**: every file in `tests/fail/` must not compile, and each
  `// error: text` must appear in the error message. `check` must return the
  same diagnostics even with the debug `JIHOO_NO_ELAB` switch set.
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

`nix flake check` runs every suite with the installed compiler.

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
[AMD64 psABI](https://gitlab.com/x86-psABIs/x86-64-ABI/-/blob/master/x86-64-ABI/low-level-sys-info.tex)
and [AAPCS64](https://github.com/ARM-software/abi-aa/blob/main/aapcs64/aapcs64.rst).
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
python3 experiments/functional-fusion/run.py --compiler out/jihoo --iterations 128
```

This compares ordinary higher-order functions, comptime producers, the
public iterator API, eager vectors, a handwritten jihoo loop, and C. It
checks randomized results at O0/O2 with checked/wrapping arithmetic, records
allocations and optimized IR, and measures interleaved runtimes. See the
[experiment](../../experiments/functional-fusion/README.md) for the method,
recorded results, and the filter/fold fusion optimization. The program
suite additionally checks callback order, ownership and compile-time use.
