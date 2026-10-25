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
live in `tests/selfhost/<pass>/`. A `// load-args: ...` line in a file gives
`emit-program` more options (`-I dir`, `--target aarch64`). Both compilers
find the standard library through `JIHOO_PATH`, so they name its files the
same way.

| step | jihoo | Rust | compared by | state |
|------|-------|------|-------------|-------|
| 1 | `diag.jh`, `lex.jh` | `diag.rs`, `lex.rs` | `emit-tokens` | done |
| 2 | `ast.jh`, `parse.jh` | `ast.rs`, `parse.rs` | `emit-ast` (`astdump.rs`, `astdump.jh`) | done |
| 3 | `load.jh`, `target.jh`, `os.jh` | `load.rs`, `target.rs` | `emit-program` (every module, its file and imports, then its tree) | done |
| 4 | `types.jh`, `mir.jh`, `sema/` | `types.rs`, `mir.rs`, `sema/` | `emit-mir` before elaboration (`JIHOO_NO_ELAB=1`), and the errors of `tests/fail` | needs `i128` (below) |
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
- Pattern literals (`i128` in Rust) are a sign and a `u64` (`ast.PatInt`)
  until jihoo has `i128`.
- Rust's `Display` for floats, which messages use, is `fmt.push_f64`
  (the shortest `%e` that reads back exactly, through libc).
- What `std` does not offer yet (whether a file exists, canonical paths,
  the running program's path, the system's reason for a failure, worded
  like Rust's `io::Error`) is in `os.jh`, over libc. The host target comes
  from the loader's own per-target files: `host.x86_64.jh` and
  `host.aarch64.jh`.

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
- A struct pattern could not name its type through an alias
  (`type Stmt = ast.Stmt`, then `Stmt { kind, .. }`), though an enum
  variant pattern could. (`tests/run/structs.jh`.)
- There was no way to take the values of a `Vec` one by one: `for x in v`
  borrows. `Vec.into_iter()` now gives them away. (`tests/run/drops.jh`.)
- A debug build of the Rust compiler overflowed its stack on deeply nested
  code before the parser's depth limit stopped it; it now runs on a thread
  with a 256 MiB stack.
- Two nested `for` loops, the inner one over a part of the outer one's
  element, were rejected (`m` changed while borrowed). The kernel gave the
  loans of a call with an `inout` view argument to every local sharing any
  loan with that argument, which included the outer iterator. It now gives
  them to what the argument borrows (`&mut v` → `v`, through reborrows).
  The old rule also missed the case it was for: after `v.push(s.as_str())`
  with `v: Vec(str)`, `s` could change while `v` still pointed into it.
  (`tests/run/loops.jh`, `tests/fail/borrow_view_pushed*.jh`.)

And differences from Rust that are by design, now documented in
[Coming from Rust](../language/from-rust.md): `let (var a, b)`, and
`match` using up a whole owned variable on every path.

## Next: `i128`

Sema folds constants in `i128` (a `u64` and a negative number both fit) and
MIR keeps integer constants that way. Before step 4, jihoo gets `i128` and
`u128`, which LLVM has already.

## Known issues

- Built at `-O0`, stage 1 needs more than 16 MiB of stack to reach the
  parser's depth limit (500 levels of nesting), since every temporary has
  its own stack slot; built at `-O1` or more it needs about 4 MiB. The Rust
  compiler runs on a thread with a large stack for the same reason; stage
  1 will need the same once it has threads, or a smaller depth limit.
