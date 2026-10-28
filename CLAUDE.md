# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

jihoo is a systems language: as fast as C, memory-safe without lifetimes or a
GC. Every value has one owner; parameters borrow (`x: T`), borrow mutably
(`inout x: T`, called with `f(&x)`) or take (`sink x: T`). Values that own
memory move; `.clone()` copies. Generics are `comptime` parameters
(Zig-style, checked per instance). Two profiles: native (libc, the default)
and freestanding (`#![freestanding]`: syscalls, static binary). Targets are
x86_64 and aarch64 Linux. Version 0.1 is a rewrite; `docs/internals/redesign.md`
says why.

## Writing jihoo code

jihoo looks like Rust but differs in ways that are easy to get wrong
(`Vec(T)` not `Vec<T>`, `.` not `::`, `let x = place` borrows, no `if let`,
newlines end statements, range patterns include their end). Before writing or
reviewing `.jh` code, read `docs/language/from-rust.md` (the differences) and
`docs/reference/grammar.md` (the exact syntax, from `compiler/parse.jh`); `lib/std/` is
the largest body of idiomatic jihoo. When unsure whether something works,
compile a small program with `jihoo run` rather than guessing, and when you
find a difference the docs do not mention, add it to `from-rust.md` and a
test (`tests/run/from_rust.jh`).

## Environment and build

Everything comes from `flake.nix` (clang, lld from LLVM 21, and the seed: the
compiler of the latest GitHub release). There is no Rust. Work inside
`nix develop` (or `direnv allow`), where `jihoo` is the seed and
`JIHOO_PATH` is the checkout's `lib/`; for tools not in the dev shell use
`nix-shell -p <pkg>`.

```sh
jihoo build -O2 compiler/main.jh -o out/jihoo    # the current compiler, built by the seed
out/jihoo run examples/hello.jh                  # compile + run
out/jihoo check examples/hello.jh                # check without code generation
out/jihoo check examples/hello.jh --error-format=json  # source diagnostics for editors
out/jihoo fmt examples/hello.jh                  # formatted source on stdout
out/jihoo fmt examples/hello.jh --check          # check layout without rewriting
out/jihoo fmt examples/hello.jh --width 80       # change the soft byte width
out/jihoo run examples/calc.jh -- a b            # args after --
out/jihoo build examples/freestanding.jh -o out/hello
out/jihoo emit-mir examples/hello.jh             # the compiler's MIR
out/jihoo emit-llvm examples/hello.jh            # the LLVM IR it writes
nix build                                        # seed → stage 1 → stage 2 → ./result/bin/jihoo
nix build .#jihoo-seed                           # the seed alone
```

The compiler writes LLVM IR text in memory and uses LLVM 21's C API
(`JIHOO_LLVM`) to optimize and emit objects. `JIHOO_CC` is the native linker
driver; `JIHOO_LD` is the freestanding linker. `JIHOO_BACKEND=clang` keeps
the previous pipeline for comparison. `import` searches the importing file's directory, `-I` dirs,
`JIHOO_PATH`, then the `lib/` or `share/jihoo/lib` above the compiler's binary.

## Tests

```sh
jihoo run tests/runner.jh                          # everything (tests compiler/ built by the seed)
jihoo run tests/runner.jh -- check fail            # suites: format check run fail examples backend selfhost
JIHOO_TEST=maps jihoo run tests/runner.jh          # those whose path contains `maps`
JIHOO_COMPILER=out/jihoo jihoo run tests/runner.jh # with a compiler already built
nix flake check                                    # everything CI runs
```

- `tests/run/*.jh`: `//> text` lines are expected stdout in order, `// exit: N`
  the exit status (a trap is 132), `// args: a b` the arguments.
- `tests/fail/*.jh`: each `// error: text` must appear in the compile error.
  Add one for every error the compiler should give, especially borrow rules.
- `selfhost`: the tested compiler builds `compiler/main.jh`, and the result must
  write the same `emit-llvm` (both targets, errors included) for every `.jh` file.
- After changing ownership, drops or the std library, run programs under
  valgrind (`-O0`, see `docs/internals/testing.md`).
- `JIHOO_NO_ELAB=1 jihoo emit-mir f.jh` prints MIR before elaboration and
  checking, to debug those passes.

## Architecture

```
source.jh → lex/parse → load → sema (check + lower) → MIR → elab → check → llvm (text) → LLVM C API → object → linker
```

The compiler, in jihoo, `compiler/`:
- `sema.jh`: names, types, generic instances (`instance()`, a queue), lowering to
  MIR in one pass per instance (`body.jh`: expressions, calls, closures;
  `pat.jh`: match, destructuring, exhaustiveness; `builtins.jh`;
  `interp.jh`: compile-time evaluation of MIR). Sema inserts drops at scope ends and
  decides move/copy/borrow for each use.
- `elab.jh`: init dataflow → use-after-move errors, removes drops of moved
  values, adds drop flags.
- `check.jh`: the borrow kernel. Loans from `Ref`/`RefMut`, followed through
  view-typed locals, live while a holder is live (liveness), checked against
  every access. It must not trust sema.
- `llvm.jh`: allocas + byte offsets + memcpy; aggregates by pointer, `sret`;
  `noalias` on borrowed params; drop glue per type. `backend.jh`: the LLVM C API.
- Layout lives once in `types.jh` (C-like structs; enums = tag then fields).
- Views (`str`, slices, closures, borrows, types containing them, `#[view]`
  structs) carry loans; `types.is_view`.

Data is index-based (`TyId`-like `u32`s, `Local`, `FnId`), with references
only as parameters and enums/match/Vec/Map. Each pass has a dump command
(`emit-tokens`, `emit-ast`, `emit-program`, `emit-mir` with and without
`JIHOO_NO_ELAB`, `emit-llvm`).

## Self-hosting and releases

`compiler/` and the `lib/std` it imports use only what the seed (the latest
release, pinned in `flake.nix`) knows. To use a new feature there: add it
without using it in `compiler/`, tag a release (`.github/workflows/release.yml`
attaches x86_64 and aarch64 binaries), move the seed's version and hashes in
`flake.nix`, then use it. Never replace a released archive. `nix build` checks
that stage 1 (built by the seed) and stage 2 (built by stage 1) write the same
IR for `compiler/main.jh`. See `docs/internals/self-hosting.md`.

## Standard library

`lib/std/*.jh`, in jihoo. `prelude.jh` is seen everywhere, plus modules it
`pub import`s. Files per profile/target: `sys.jh` (libc) vs
`sys.freestanding.jh` (syscalls + allocator), `sysno.<target>.jh`. Std modules
see each other's private items.

## Docs and website

`docs/` is the website's source (one Markdown file per page) along with `examples/*.jh`
(header comment becomes the page text). Every page must be listed in `docs/README.md`;
the site build (`site/`, Astro: `nix develop .#site; cd site; npm ci; npm run build`)
fails on missing TOC entries or broken links/anchors. When a feature changes, update the
relevant `docs/` page, README's Status section and `docs/internals/roadmap.md` as appropriate.
Docs and comments are written in English.

## Commits

Commit messages: short imperative subject (e.g. "Closures in native programs"), then
prose paragraphs explaining what changed and why.
