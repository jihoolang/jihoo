# jihoo

A systems programming language that is as fast as C and memory-safe without
lifetime annotations or a garbage collector.

- **Ownership without lifetimes.** Every value has one owner. Functions
  borrow their arguments (`x: T`), borrow them to change them (`inout x: T`)
  or take them (`sink x: T`). Borrows are scoped to a function body, so the
  compiler sees all of them and needs no annotations.
- **No hidden costs.** No GC, no reference counting, no implicit copies of
  anything that owns memory: those move, and `.clone()` copies them.
- **As fast as C.** Programs compile through LLVM; on the benchmarks they
  match C compiled by clang, with bounds checks on.
- **Generics at compile time**, as in Zig: `comptime T: type` parameters,
  inferred at calls, with traits as bounds.
- **A standard library written in jihoo** (`Vec`, `String`, `Map`, `Box`,
  sorting, files, processes), with or without libc.

Documentation: **<https://jihoolang.github.io/jihoo/>**, built from
[docs/](docs) and [examples/](examples).

```jihoo
enum Expr {
    Num(i64)
    Add(Box(Expr), Box(Expr))
}

fn eval(e: Expr) -> i64 {
    match e {
        Num(n) => n
        Add(a, b) => eval(a) + eval(b)
    }
}

fn main() {
    var counts = Map(String, i64).new()
    for w in "a b a".split(" ") {
        match counts.get_mut(w) {
            Some(n) => n += 1
            None => {
                counts.insert(w.to_string(), 1)
            }
        }
    }
    println(counts["a"])                                        // 2
    println(eval(Expr.Add(Box.new(Expr.Num(2)), Box.new(Expr.Num(3)))))  // 5
}
```

```jihoo
fn main() {
    var v = Vec(i64).new()
    v.push(1)
    for x in v {
        v.push(x)   // error: `v` is changed here while it is borrowed
    }
}
```

## Install

```sh
nix run github:jihoolang/jihoo -- run hello.jh     # try it
nix profile install github:jihoolang/jihoo         # install `jihoo`
```

Without Nix, each [release](https://github.com/jihoolang/jihoo/releases)
has the compiler for x86_64 and aarch64 Linux with its standard library; it
needs glibc and LLVM 21 (libLLVM, clang, lld).

## Build from source

jihoo is written in jihoo. Everything comes from `flake.nix` (libLLVM,
clang and lld from LLVM 21, and the seed: the compiler of the latest
release). `nix build` bootstraps the compiler: the seed builds
`compiler/`, which builds itself again and is installed.

```sh
nix build                                    # ./result/bin/jihoo
nix develop                                  # `jihoo` is the seed
jihoo build -O2 compiler/main.jh -o out/jihoo
out/jihoo run examples/hello.jh
out/jihoo check examples/hello.jh              # no code generation or linking
out/jihoo fmt examples/hello.jh                # formatted source on stdout
out/jihoo emit-mir examples/hello.jh
jihoo run tests/runner.jh                    # the tests
```

## Layout

| path | what |
|------|------|
| `compiler` | the compiler, in jihoo: parser, type checker, MIR, borrow checker, LLVM IR writer |
| `lib/std` | the standard library, in jihoo |
| `tests/run`, `tests/fail` | programs and their expected output or error; `tests/runner.jh` runs them |
| `examples` | example programs, which the website shows |
| `benchmarks` | backend and iterator fusion benchmarks, with recorded measurements |
| `docs` | the documentation, one Markdown file per page |
| `site` | the website ([site/README.md](site/README.md)) |

## Status

Version 0.4: the 0.1 rewrite, which broke compatibility with everything
before it ([why](docs/internals/redesign.md)), with a self-hosted compiler
and checking, testing, diagnostic and formatting tools. Native (libc) and
freestanding (no libc, static) programs for x86_64 and aarch64 Linux, and
[UEFI applications](docs/language/profiles.md#uefi) (PE32+ images) for
both machines.

The compiler uses its own threads: it elaborates, infers borrow effects and
checks borrows one function per thread, the costliest first, and emits
large programs in parallel code generation units, with the same output as
one thread. On 8 CPUs, `jihoo check` of the compiler takes 0.53 s and a
full `-O2` build 15.2 s, against 17.0 s and 36.8 s at 0.2.1
([phase timings](docs/reference/command-line.md#phase-timings),
[roadmap](docs/internals/roadmap.md#4-parallel-compilation-03)).

Done: ownership with moves, destructors and drop flags; borrowing with
parameter conventions, projections and views, checked by a separate borrow
kernel; integers up to 128 bits; structs, enums, tuples, arrays, slices;
`match` with exhaustiveness, `|` patterns that bind names, `let ... else`,
and `match`es that are views of the borrowed parts they give; generics
with inference; traits with default
methods and generic impls; closures that borrow, `comptime` closures
that inline, and `move fn` closures that own their captures without
allocating, returned as `-> impl Iterator` or `-> impl fn(A) -> R`; `Option`, `Result` and `?`; `unsafe` pointers, `static`
globals, C functions and callbacks (including structs by value, 128-bit
integers and variadic function pointers on both targets), dynamic libraries
(`std.ffi`), system calls, atomics and volatile accesses for device
registers; [panic handlers](docs/language/errors.md#panic-handlers) for
library objects that another operating system links, and
[kernel code generation](docs/language/profiles.md#kernel-code-generation)
without the red zone or vector registers; the standard library,
including running other programs.

[Compile-time evaluation](docs/language/comptime.md) runs ordinary functions
and blocks in a separate MIR interpreter for `const` values, `comptime`
expressions, array lengths and compile-time arguments. It supports loops,
recursion, aggregates and the heap: `Vec`, `String`, `Map` and destructors
work, and a `String` or `Vec` result becomes a static `str` or slice.
External calls remain unavailable during evaluation.
[`--comptime-report PATH`](docs/reference/command-line.md#compile-time-resource-reports)
records evaluator steps, cumulative allocations and per-function costs;
failures report resource use and the originating compile-time obligation.

Proof checking at compile time (a Horn certificate kernel, general theorems
by induction, and enum codecs bound to checked tables) is developed in the
separate [jihoo-proofs](https://github.com/jihoolang/jihoo-proofs)
repository. [Verification](docs/reference/command-line.md#verification)
is in the compiler: `jihoo verify` proves bounds and overflow checks,
panics that cannot be reached (also at each call to a small function that
may panic, such as `v[i]`), and
[contracts](docs/language/contracts.md) (`requires`, `ensures`, loop
`invariant`s and structs' type invariants, over integers, fields and
lengths, with `&&`, `||` and `!`) with linear certificates
that a small trusted checker accepts. Every build verifies: it removes
the proved checks, and an unproved contract is a compile error
(`--no-verify` keeps every check). It runs on the compiler's own source
(`jihoo verify compiler/main.jh`), and CI fails if it proves fewer; no
check is left in the trusted checker itself, and the checker is proved
sound: [`lib/proof`](lib/proof/refine.jh) checks a Horn proof, from the
rules `jihoo emit-horn` writes for its code, that when it accepts a
certificate no integer point satisfies the facts and the negated claim,
and [`agda/`](agda/Certified.agda) checks that proof in Agda with Horn's
proved checker and reads it in the integers. The translation of the code
into rules is still trusted, and the composed proof of the verifier
(execution semantics, condition generation, check removal) is pending.
Agda currently connects exported scalar helpers, direct callers and an
[accumulator loop](agda/MirLoopCorrespondence.agda) to their generated Horn
relations, with inductive invariants for arbitrary finite loop executions.
A [typed Vec backing-store specification](agda/VecMemory.agda) also
connects initialized prefixes, capacity-checked pushes and copying
relocation to the list relations; connecting the library's actual MIR,
allocator and pointer/borrow behavior remains required.

The replacement direction is a [native dependent core](docs/internals/dependent-core.md)
that checks programs and proofs together and emits MIR directly from the
checked terms. The experimental `#![dependent_core]` source subset
compiles [`examples/core_index.jh`](examples/core_index.jh) through the
ordinary AST into the same core as [`core_index.jhc`](examples/core_index.jhc):
a runtime array lookup whose proof is erased before code generation,
without Horn, Agda or legacy VC generation. The
[equality example](examples/core_equality.jh) adds erased U64 equality
and proposition-only transport, with user-written lemmas rewriting the
runtime bound to the array length. Programs declare their own
strictly positive inductive propositions: the
[graph example](examples/core_inductive.jh) proves by structural induction
that every node reachable along its declared edges is in bounds, and the
[chain example](examples/core_chain.jh) declares equality chains, which
were built into the kernel before. The recursive proofs are erased before
the array loads are emitted. The [loop example](examples/core_loop.jh)
sums arrays of any length with `fold`, whose body has a proof of its
index's bound, so the loads have no bounds checks. In the
[order example](examples/core_order.jh), u64 indices are natural numbers
whose `+` traps instead of wrapping; three kernel rules of their order
justify loads at `i + 1` and over prefixes, and the
[subtraction example](examples/core_sub.jh) reads arrays backwards with
`sub(n, i + 1, p)`, whose evidence shows it cannot underflow. A
[refinement](examples/core_refine.jh) `refine(fn(j) { Lt(j, n) })` is a
u64 returned together with its evidence, and is the u64 alone at run time.
[Data types](examples/core_data.jh) declared as `enum` are taken apart
with `match`, or proved about by cases, and compile to no tag at all;
they can be [parameterized](examples/core_indexed.jh) by u64 values such
as a table's length, which `n: erased(u64)` passes only to types and
evidence. [Owned buffers](examples/core_buffer.jh) are allocated
explicitly and freed exactly once, which the kernel checks, with loads
and stores at proved indices, and [recursive data](examples/core_list.jh)
lives on the heap, taken apart by `match` or consumed by structural
recursion, with proofs by induction. An owned value is
[freed where its scope ends](examples/core_scope.jh) without a written
`free`, and the kernel checks those frees too, and a `ref List`
parameter [borrows](examples/core_borrow.jh) a value without consuming
it. Types and proofs may [borrow any value](examples/core_borrow_proof.jh),
so a proof by induction can be about `length(xs: ref List)` and a
precondition about the list its function consumes. A
[lend](examples/core_lend.jh) of an owned list knows that its borrow
reads that list, so such evidence applies to the borrow, and a borrowing
call's result type may mention the owner. Wider `.jh` coverage
and mechanized proofs of the kernel, erasure and lowering remain
required before this replaces the existing verifier; the
[roadmap](docs/internals/roadmap.md#the-050-release-gate-for-the-native-core)
states the 0.5.0 gate.

Buffered UTF-8 input (`std.io.BufRead`, `StrReader`, `BufReader`) and
Unicode scalar decoding/iteration (`std.utf8`) support streaming parsers.
[`std.os`](docs/reference/standard-library.md#files-and-errors) reports
failures as an errno-based `os.Error`, which `std.fs` and `std.process`
also return, and reads and writes bytes with one system call each, so
partial operations, the end of input, interrupted calls and nonblocking
readiness are explicit, in both profiles.
[`std.fmt`](docs/reference/standard-library.md#formatting) formats several
values with patterns such as `"{:>8.2} {:#x}"`, checked while compiling
when they are literals ([`#[literal_check]`](docs/language/comptime.md#checking-literal-arguments)),
and floats print the shortest text that reads back as the same value.
The borrow kernel infers argument escape effects for direct calls, including
recursive functions, so methods on views keep only the borrows they can
actually retain; unknown calls and raw memory effects remain conservative.

[Reflection](docs/language/reflection.md): `inline for` and `inline if`
unroll and select code at compile time, and builtins name a type's fields
and variants. `#[derive(Clone, Eq, Ord, Hash, Show, Default)]` is library code
written with them, in `std/derive.jh`, and keeps privacy.

[Threads](docs/language/threads.md): `std.thread.scope`, `join`, `each`, `map` and
`each_mut` run work on several threads that borrows what the caller owns,
in native and freestanding programs; the `_uneven` forms hand out one item
at a time, for work of very different sizes.
Scopes start any number of workers, collect results with `handle.join()`
and join every remaining worker before the body's locals go away.
The borrow rules and a compile-time check of the closures rule out data
races. `std.sync.Atomic`, `Mutex`, `Channel` and `Once` are shared through
plain borrows.

[Data by index](docs/language/data-oriented.md): `std.arena` has typed ids
and arenas, generational handles and pools, and `Soa(T)`, a
struct-of-arrays vector that reflection lays out from `T`'s fields.

[Dynamic dispatch](docs/language/dyn.md): `dyn Trait` values own a value of
any type with the trait and call it through a table of functions;
`dyn fn` closures own what they capture, so they can be returned and
stored.

[Iterator pipelines](docs/language/iterators.md) compose `map`, `filter`,
`take`, `zip` and `fold` without intermediate collections. Callback types
are inferred, and compile-time closures can be named, captured and forwarded.
Supported pipelines also run in the compile-time interpreter.

LLVM 21's C API optimizes and emits objects directly, with loop and SLP
vectorization at `-O2`/`-O3`. Native linking uses a C driver; freestanding
linking uses lld, and UEFI linking lld's COFF linker. `JIHOO_BACKEND=clang` selects the previous backend for
comparison. [Backend benchmarks](docs/internals/testing.md#backend-performance)
compare compilation time and generated program speed.
[Compilation baselines](docs/internals/testing.md#compilation-time-and-memory)
measure checking and full compilation of the compiler and compile-time
generation workloads, with elapsed time and peak memory, and compare them
with a recorded report.

The compiler is written in jihoo, in `compiler/`, and
[self-hosted](docs/internals/self-hosting.md): the compiler of the latest
release builds it, and it builds itself to the same LLVM IR. There is no
Rust left; the Rust compiler that first bootstrapped it is in the history
up to v0.1.1.

Errors come several per run, in source order, with notes on where a
moved value went and where a conflicting borrow started.

[`jihoo check`](docs/reference/command-line.md#checking-without-code-generation)
checks types, moves, borrows and compile-time obligations without generating
code or requiring LLVM or a linker. `--lib` checks modules without `main`.
`--error-format=json` reports source errors with byte ranges and related
notes for editor integration, and every other failure (usage, files, the
backend and linker) in the same document; text remains the default.
[`jihoo fmt`](docs/reference/command-line.md#source-formatting) formats
source files while preserving comments, literals and meaningful line breaks.
Long argument, parameter and field lists wrap at a soft width of 100 byte
columns; `--width N` adjusts it. `--check` checks layout without printing
formatted source and `--write` rewrites files, including every `.jh` file in
the directories given. The output is reparsed and must retain the same syntax tree.

[`jihoo lsp`](docs/reference/command-line.md#language-server) is a language
server built on the same checking and diagnostics: errors in unsaved
documents, go to definition and formatting.

Next ([roadmap](docs/internals/roadmap.md)): application-driven library work.
