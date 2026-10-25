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
| 4 | `types.jh`, `mir.jh`, `sema/` | `types.rs`, `mir.rs`, `sema/` | `emit-mir` before elaboration (`JIHOO_NO_ELAB=1`), and the errors of `tests/fail` | in progress: `types.jh`, `mir.jh`, `sema.jh` (`mod.rs`, `consts.rs`), `body.jh` (functions, statements, operators, control flow, calls); `emit-mir` agrees on `tests/selfhost/sema/` |
| 5 | `elab.jh`, `check.jh` | `elab.rs`, `check.rs` | `emit-mir`, `tests/fail` | |
| 6 | `llvm.jh`, the driver | `llvm.rs`, `main.rs` | `emit-llvm`; then `build` and `run` through `std.process` | |
| 7 | stage 2 | | stage 2's `emit-llvm` against stage 1's, on everything | |

Sema (step 4) is half of the compiler, about 6,000 of its 12,000 lines.
Every program loads the prelude, which uses nearly the whole language, so
`emit-mir` on ordinary programs can only agree once almost all of sema is
ported. Until then the comparison runs on small programs in
`tests/selfhost/sema/` compiled with `--no-prelude` (an option for this
only, in both compilers), and grows feature by feature: functions and
integers, control flow, structs and enums, patterns, generics, traits,
closures. Then the standard library, then everything. Until elaboration is
ported too, the comparison is of MIR before it (`JIHOO_NO_ELAB=1`). The
parts of `body.rs` not ported yet stop with "the compiler in jihoo cannot
lower ... yet".

The Rust `Sema` keeps references into the syntax tree (`&'a ast::FnDecl`).
In jihoo a `ref T` read out of a table (`self.fns[f].decl`) carries the
borrow of the table, since there are no lifetimes to say that it points
elsewhere; changing `self` while holding it is then an error. The port
keeps raw pointers into the tree instead (`*ast.FnDecl`), read through
`sema.at`: the tree outlives sema and never changes, which is what Rust's
`'a` says.

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
- Rust's `Display` for floats, which messages use, is `fmt.push_f64`
  (the shortest `%e` that reads back exactly, through libc).
- What `std` does not offer yet (whether a file exists, canonical paths,
  the running program's path, the system's reason for a failure, worded
  like Rust's `io::Error`) is in `os.jh`, over libc. The host target comes
  from the loader's own per-target files: `host.x86_64.jh` and
  `host.aarch64.jh`.
- Types are interned by a short text spelling the kind out
  (`types.kind_key`), where Rust hashes the `TyKind` with a derived
  `Hash`; jihoo has no `derive` yet.

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
  (`tests/run/loops.jh`, `tests/fail/borrow_view_pushed*.jh`.) The first
  version of that fix went too far and rejected keeping a loop's element
  after its iteration (`last = w.as_str()`, `views.push(w.as_str())`); a
  local is exempt from its own loans, a value moved out of a local no
  longer carries that local's loans on itself, and giving a reference a
  new value no longer conflicts with reborrows through its old one.
  (`tests/run/borrows_ok.jh`.)
- Moving a part out of a call's result (`self.struct_layout(ts).1`) was an
  internal error: the rest of the temporary was dropped whole. Its other
  parts are now dropped when the part moves out (`tests/run/temp_parts.jh`,
  `tests/fail/move_part_of_drop.jh`).
- Language gaps filled while porting `sema/mod.rs`, each with tests and
  documentation: patterns see through `ref`/`inout` values
  (`Some(Circle(r))` on an `Option(ref Shape)`; `tests/run/ref_patterns.jh`);
  a `ref T` value can be passed where a `T` is borrowed; a `ref Vec(T)`
  value can be looped over and indexed; a generic function whose type
  parameter is a borrow (`mem.replace` in `Map(K, ref V).insert`) returns
  it as a value instead of a place; and a value that is not a view (a
  number, a raw pointer) no longer carries the loans of the container it
  was read from.
- Left as they are, and documented in
  [Coming from Rust](../language/from-rust.md): a `match` arm cannot hand
  out a borrowed part as its value, and `None` alone in an `if` arm needs
  the type written.

And differences from Rust that are by design, now documented in
[Coming from Rust](../language/from-rust.md): `let (var a, b)`, and
`match` using up a whole owned variable on every path.

## `i128` and `u128`

Sema folds constants in `i128` (a `u64` and a negative number both fit) and
MIR keeps integer constants that way, so jihoo gained `i128` and `u128`
before step 4. A 128-bit constant is held as its bit pattern and folded at
that width (`fold_128` in `consts.rs`); freestanding programs get LLVM's
128-bit helpers from `std/rt.freestanding.jh`, tested against libgcc's on
both targets. Literals stay at most 64 bits for now. Adding `i128`
also found that a shift ignored the type its context expected:
`let b: u8 = 1 << 3` was an error (`tests/run/int128.jh`).

## Known issues

- Built at `-O0`, stage 1 needs more than 16 MiB of stack to reach the
  parser's depth limit (500 levels of nesting), since every temporary has
  its own stack slot; built at `-O1` or more it needs about 4 MiB. The Rust
  compiler runs on a thread with a large stack for the same reason; stage
  1 will need the same once it has threads, or a smaller depth limit.
