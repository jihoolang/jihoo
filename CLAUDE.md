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
`docs/reference/grammar.md` (the exact syntax, from `parse.rs`); `lib/std/` is
the largest body of idiomatic jihoo. When unsure whether something works,
compile a small program with `jihoo run` rather than guessing, and when you
find a difference the docs do not mention, add it to `from-rust.md` and a
test (`tests/run/from_rust.jh`).

## Environment and build

Everything comes from `flake.nix` (Rust, clang, lld from LLVM 21). Work inside
`nix develop` (or `direnv allow`); for tools not in the dev shell use `nix-shell -p <pkg>`.

```sh
cargo build
cargo run -- run examples/hello.jh               # compile + run
cargo run -- run examples/calc.jh -- a b         # args after --
cargo run -- build examples/freestanding.jh -o out/hello
cargo run -- emit-mir examples/hello.jh          # the compiler's MIR
cargo run -- emit-llvm examples/hello.jh         # the LLVM IR it writes
nix build                                        # packaged compiler → ./result/bin/jihoo
```

The compiler writes LLVM IR text and runs `clang` (`JIHOO_CC`) to optimize and
link. `import` searches the importing file's directory, `-I` dirs,
`JIHOO_PATH`, then the checkout's `lib/`.

## Tests

```sh
cargo test                                         # everything
cargo test --test programs                         # tests/run and tests/fail
JIHOO_TEST=maps cargo test --test programs         # those whose path contains `maps`
cargo clippy --all-targets --locked -- -D warnings # CI runs this
nix flake check                                    # everything CI runs
```

- `tests/run/*.jh`: `//> text` lines are expected stdout in order, `// exit: N`
  the exit status (a trap is 132), `// args: a b` the arguments.
- `tests/fail/*.jh`: each `// error: text` must appear in the compile error.
  Add one for every error the compiler should give, especially borrow rules.
- After changing ownership, drops or the std library, run programs under
  valgrind (`-O0`, see `docs/internals/testing.md`).
- `JIHOO_NO_ELAB=1 jihoo emit-mir f.jh` prints MIR before elaboration and
  checking, to debug those passes.

## Architecture

```
source.jh → lex/parse → load → sema (check + lower) → MIR → elab → check → llvm (text) → clang
```

One crate, `crates/jihoo`:
- `sema/`: names, types, generic instances (`instance()`, a queue), lowering to
  MIR in one pass per instance (`body.rs`: expressions, calls, closures;
  `pat.rs`: match, destructuring, exhaustiveness; `builtins.rs`;
  `consts.rs`: compile-time folding). Sema inserts drops at scope ends and
  decides move/copy/borrow for each use.
- `elab.rs`: init dataflow → use-after-move errors, removes drops of moved
  values, adds drop flags.
- `check.rs`: the borrow kernel. Loans from `Ref`/`RefMut`, followed through
  view-typed locals, live while a holder is live (liveness), checked against
  every access. It must not trust sema.
- `llvm.rs`: allocas + byte offsets + memcpy; aggregates by pointer, `sret`;
  `noalias` on borrowed params; drop glue per type.
- Layout lives once in `types.rs` (C-like structs; enums = tag then fields).
- Views (`str`, slices, closures, borrows, types containing them, `#[view]`
  structs) carry loans; `types.is_view`.

The Rust is written to be ported to jihoo: index-based data (`TyId`,
`Local`, `FnId`), references only as parameters, enums/match/Vec/HashMap.
Keep it that way.

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
