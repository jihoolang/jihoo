# Self-hosting

The compiler is being rewritten in jihoo, in `compiler/`, so that jihoo
compiles itself. This page is the plan and where it stands.

## Stages

- **Stage 0** is the Rust compiler, `crates/jihoo`.
- **Stage 1** is `compiler/main.jh` compiled by stage 0.
- **Stage 2** is `compiler/main.jh` compiled by stage 1.

jihoo is self-hosted when stage 1 can build stage 2 and the two agree: for
every program, stage 2 writes the same LLVM IR as stage 1. After that the
Rust compiler is only needed to bootstrap a machine that has no jihoo yet.

## Pass by pass, compared all the way

The port goes one pass at a time, in the order the compiler runs them. Each
pass gets a command that prints what it makes, in both compilers, in the
same format; `crates/jihoo/tests/selfhost.rs` builds stage 1 and runs both
compilers on every `.jh` file in the repository (`lib/`, `tests/`,
`examples/`, `compiler/`), comparing output, errors and exit status byte for
byte:

```sh
cargo test --test selfhost
```

Error messages are part of the comparison, so stage 1 gives the same
errors, at the same places, as stage 0. Inputs meant to exercise one pass
live in `tests/selfhost/<pass>/`.

| step | jihoo | Rust | compared by | state |
|------|-------|------|-------------|-------|
| 1 | `diag.jh`, `lex.jh` | `diag.rs`, `lex.rs` | `emit-tokens` | done |
| 2 | `ast.jh`, `parse.jh` | `ast.rs`, `parse.rs` | `emit-ast` (to add) | |
| 3 | `load.jh` | `load.rs` | `emit-ast` of the whole program | |
| 4 | `types.jh`, `mir.jh`, `sema/` | `types.rs`, `mir.rs`, `sema/` | `emit-mir` before elaboration (`JIHOO_NO_ELAB=1`), and the errors of `tests/fail` | |
| 5 | `elab.jh`, `check.jh` | `elab.rs`, `check.rs` | `emit-mir`, `tests/fail` | |
| 6 | `llvm.jh`, the driver | `llvm.rs`, `main.rs` | `emit-llvm`; then `build` and `run` through `std.process` | |
| 7 | stage 2 | | stage 2's `emit-llvm` against stage 1's, on everything | |

Sema (step 4) is half of the compiler, about 6,000 of its 12,000 lines; it
will be ported file by file behind the same `emit-mir` comparison, starting
with the declarations and simple bodies.

## How the port is written

The Rust compiler was written to be ported: index-based data (`TyId`,
`Local`, `FnId`), references only as parameters, enums, `match`, `Vec` and
`HashMap`. The port follows it closely, function by function, so that a
change to one compiler can be carried to the other. Where jihoo has a
better way the port takes it and says so in a comment; so far:

- A token's kind is a plain enum (`lex.Tok`), compared with `==`, and its
  payload (name, value, operator) lives in the `Token`. The parser tests
  token kinds constantly, and a plain enum compares without a `match`.
- Enum variants with named fields (`StmtKind::Let { .. }` in Rust) become
  variants holding a struct.
- `format!` becomes `String` building with `push_str` and `show`.

While both compilers exist, a language change has to be made in both:
stage 0 must compile `compiler/`, and stage 1 must agree with stage 0.

## What porting has found

Writing a large program in jihoo is also a test of jihoo. Problems found so
far, each fixed in stage 0 with a test:

- `for _ in 0..n` was rejected ("a range loop binds one name").
- `Vec.first` and `Vec.last` did not compile: the borrow kernel rejected
  returning a reborrow (`&*r`) of a `ref` that a call had returned, though
  `r`'s own loans were checked. (`tests/run/borrows_ok.jh`,
  `tests/fail/borrow_return_reborrow_local.jh`.)
