# Functional composition and fusion experiment

This experiment asks whether jihoo can express a `map` → `filter` → `fold`
pipeline over runtime data and remove the functional abstraction at compile
time. The initial run used the existing compiler without language or library
changes. The experiment now also exercises the public `std.iter` API and
the updated closure lowerer. Neither version depends on Horn.

## Implementations

`stream.jh` implements push streams: a producer is a function taking a
consumer, of type `fn(fn(i64))`. `map` and `filter` wrap that consumer;
`fold` supplies a consumer that updates its accumulator. These are separate,
reusable higher-order functions, rather than a dedicated fused loop.

`kernels.jh` compares:

- `functional`: ordinary borrowed closures throughout.
- `staged`: the same composition with `comptime` producer parameters.
- `iterator`: the public `.iter().map(...).filter(...).fold(...)` API.
- `eager`: separate map/filter passes constructing two `Vec` values with
  ordinary `new`/`push` growth, followed by a summation pass.
- `handwritten`: a single jihoo loop.
- `reference.c`: a single C loop, built with `-fwrapv` for release semantics.

All compute the sum of `x * scale + offset` values greater than `limit`.
The input pointer, length, scale, offset and limit arrive from C at runtime.
Closures capture runtime values: the compiler cannot evaluate the answer
in advance. `ordered` reuses the combinators with an order-sensitive fold
and a nonzero initial accumulator.

## Reproduce

From the repository root, with a current self-hosted compiler in `out/jihoo`:

```sh
nix develop --command python3 experiments/functional-fusion/run.py --iterations 128
```

For a performance regression check on an otherwise idle host, add
`--max-iterator-over-c 1.5`. The report is preserved even if this check fails.

Use `--compiler PATH` for another compiler. The script writes artifacts under
`out/functional-fusion/results`, including raw and optimized LLVM IR,
disassembly, and `report.json`. It uses jihoo's `emit-llvm`, LLVM 21 `opt`
with `default<O2>`, and clang for object emission/linking. It does not load
LLVM into the compiler process. The C reference also passes through the O2
IR pipeline. The C harness is always built at O2, without LTO.

For both checked and wrapping arithmetic, at O0 and O2, the harness checks
600 differential cases against C for all six implementations and 600
order-sensitive folds. Cases include empty input, negative values and
scales, zero scales, and selection extremes; wrapping runs additionally
use full-width random integers. Performance uses wrapping arithmetic/O2.
Timed calls vary offset and threshold; every run's checksum is checked.
Run order rotates, with one warm-up round and seven measured rounds.

Allocator wrappers count `malloc`/`realloc` and `free` during a separate
single kernel call, excluding input setup. Timing excludes those counters.
IR inspection follows reachable functions to check that the three composed
implementations retain no indirect or external calls. Object inspection
compares their function bytes with the handwritten jihoo loop.

## Initial result

The recorded run on 2026-10-26 used x86_64 Linux/WSL2, an Intel i7-12700,
LLVM/clang 21.1.8, 1,000,000 input elements, and 128 calls per sample.
`sample-results.json` preserves all measurements.

Both functional implementations compiled to **exactly the same 144 bytes
of machine code as the handwritten jihoo loop**. Each has one traversal,
no callback calls, and no heap allocation. All four correctness configurations
passed: 14,400 comparisons in this initial five-implementation run.

| Implementation | Median seconds | Relative to C | Allocations/reallocations per call |
| --- | ---: | ---: | ---: |
| Ordinary closures | 0.0510 | 1.027 | 0 |
| Comptime producer | 0.0481 | 0.968 | 0 |
| Handwritten jihoo | 0.0470 | 0.946 | 0 |
| C loop | 0.0497 | 1.000 | 0 |
| Eager Vec passes | 0.7148 | 14.377 | 37 |

The three jihoo loops have identical bytes, so their timing differences are
noise/layout effects rather than different abstraction costs. The C timings
are comparable on this workload; they do not establish general performance
parity. The eager baseline includes vector growth and is not a tuned
preallocated implementation; its slowdown is not a universal eager/lazy ratio.

## Public iterator API

`iterator-results.json` records the six-implementation run after adding
the library API. The same four correctness configurations passed, now
covering 16,800 comparisons. The iterator pipeline allocated no memory and
retained no callback or external calls. Its median runtime was 0.0474 s,
compared with 0.0470 s for C on the same host, input and repetition count.
These timings are comparable rather than a general speedup claim.

A straightforward pull-iterator implementation initially retained nested
filter/search loops and measured 8.9 times the C runtime on this workload,
despite having no allocation or callback calls. `FilterIter.fold` now
accumulates directly while traversing its source, retaining callback and
drop order while giving LLVM one loop to optimize. The final iterator code
is 207 bytes; it is not byte-identical to the handwritten loop. Functional
tests check side-effect order, short-circuiting, and destruction separately.

## Repeated measurements

The original 1.009 iterator/C ratio was one run, not a persistent penalty.
After committing the feature as `cdaed59`, we repeated the original protocol
ten times and then measured ten longer sessions on guest logical CPU 2:

```sh
nix develop --command python3 experiments/functional-fusion/repeat.py --cpu 2
```

Both phases use 1,000,000 input elements. The original protocol uses seven
samples of 128 kernel calls per implementation per session. The pinned
phase uses fifteen paired samples of 512 calls per session, with AB/BA
order alternated and warm-ups excluded. Measurements run sequentially;
all results and checksums are checked. The ten rebuilt executables had the
same SHA-256. No compiler or library code changed between measurements.

| Protocol | Sessions with jihoo faster | Sessions with C faster | Median session iterator/C ratio | Session bootstrap 95% interval |
| --- | ---: | ---: | ---: | ---: |
| Original | 7 | 3 | 0.98048 | 0.94937–1.00321 |
| CPU 2 pinned, longer samples | 5 | 5 | 0.99761 | 0.98569–1.02962 |

Ratios below 1 mean a shorter jihoo runtime. Each session ratio divides
the median iterator time by the median C time. In the pinned phase, jihoo
was faster in 76 of 150 individual pairs and C in 74. The pinned median
session ratio corresponds to a 0.24% shorter jihoo runtime, while the
bootstrap interval spans both directions, including a 1% difference.

The `functional` and `handwritten` functions have identical instruction
bytes and serve as a control. Their measured session ratios also varied:
0.897–1.044 without affinity and 0.928–1.034 when pinned. These functions
occupy different addresses, so this control includes placement effects as
well as timing variation. CPU affinity applies to a WSL2 guest CPU; it
does not isolate the host CPU or fix its frequency.

The intervals resample whole session ratios 25,000 times, taking the
median each time, rather than treating all correlated samples as independent.
They describe this experiment, not every workload or host. The observations
do not support a consistently slower jihoo iterator in this environment;
they also do not establish exact equality or exclude every small systematic
difference.

[Raw measurements and summaries](repeat-results.json),
[session table](repeat-results.csv), and [comparison chart](repeat-results.svg)
are retained alongside the reproduction script.

## What this establishes

For the initial push pipeline, ordinary closure conversion and LLVM optimization
already erase the abstraction. Producer specialization gives the same
result. The MIR compile-time interpreter is not involved: no `comptime`
expression evaluates the data. A new symbolic evaluator or Horn kernel is
therefore unnecessary to obtain fusion for this example.

The push representation avoids intermediate collections by construction.
This is not an optimizer discovering fusion in arbitrary eager vector code.
Its callbacks execute element by element, so replacing an eager pipeline
with it can change side-effect, trap, and allocation order. The map/filter
callbacks in this experiment are pure. This is also not a demonstration of
owning/escaping closures, higher-kinded types, arbitrary function-valued
returns, general laziness, or reliable fusion for much larger compositions.
The nested producer syntax is retained as a baseline; the public API uses
the iterator method chain in `kernels.jh`.

## Closure limitation found and fixed

If `transform` itself is a comptime closure parameter and an inner closure
calls it, the original compiler reported `` `transform` is not a function ``.
The updated compiler accepts the isolated reproducer and prints 42:

```sh
out/jihoo run experiments/functional-fusion/comptime_capture.jh
```

The lowerer now preserves the function identity through immutable aliases
and nested captures, while carrying environments through ordinary MIR
places and borrow checking. Interpreter reads of projected closure fields
also preserve pointer provenance. `stream.jh` keeps its original ordinary
callback parameters for the baseline comparison; compile-time captures are
tested in `tests/run/comptime_closure_capture.jh`.
