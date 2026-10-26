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
| `docs` | the documentation, one Markdown file per page |
| `site` | the website ([site/README.md](site/README.md)) |

## Status

Version 0.1, a rewrite that broke compatibility with everything before it
([why](docs/internals/redesign.md)). Native (libc) and freestanding (no
libc, static) programs for x86_64 and aarch64 Linux.

Done: ownership with moves, destructors and drop flags; borrowing with
parameter conventions, projections and views, checked by a separate borrow
kernel; integers up to 128 bits; structs, enums, tuples, arrays, slices;
`match` with exhaustiveness; generics with inference; traits with default
methods and generic impls; closures that borrow, and `comptime` closures
that inline; `Option`, `Result` and `?`; `unsafe` pointers, `static`
globals, C functions and callbacks, dynamic libraries (`std.ffi`), system calls and atomics; the standard library,
including running other programs.

[Compile-time evaluation](docs/language/comptime.md) runs ordinary functions
and blocks in a separate MIR interpreter for `const` values, `comptime`
expressions, array lengths and compile-time arguments. It supports loops,
recursion and fixed aggregates; external calls and heap allocation remain
unavailable during evaluation.

[Iterator pipelines](docs/language/iterators.md) compose `map`, `filter`,
`take`, `zip` and `fold` without intermediate collections. Callback types
are inferred, and compile-time closures can be named, captured and forwarded.
Supported pipelines also run in the compile-time interpreter.

LLVM 21's C API optimizes and emits objects directly, with loop and SLP
vectorization at `-O2`/`-O3`. Native linking uses a C driver; freestanding
linking uses lld. `JIHOO_BACKEND=clang` selects the previous backend for
comparison. [Backend benchmarks](docs/internals/testing.md#backend-performance)
compare compilation time and generated program speed.

The compiler is written in jihoo, in `compiler/`, and
[self-hosted](docs/internals/self-hosting.md): the compiler of the latest
release builds it, and it builds itself to the same LLVM IR. There is no
Rust left; the Rust compiler that first bootstrapped it is in the history
up to v0.1.1.

Next ([roadmap](docs/internals/roadmap.md)): `derive`, dynamic dispatch, threads.
