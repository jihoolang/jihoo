# Self-hosting

The compiler is written in jihoo, in `compiler/`, and jihoo compiles
itself: the compiler built by itself writes the same LLVM IR as the one
that built it, for every program in the repository. It was first written
in Rust and ported pass by pass; once the port was self-hosted, the Rust
compiler bootstrapped it for one release (0.1.1) and was then removed. This
page is how it got there and how it stays there.

## Stages

- **Stage 0**, the seed, is the compiler of the latest release, downloaded
  from [GitHub releases](https://github.com/jihoolang/jihoo/releases)
  (`jihoo-seed` in `flake.nix`, which pins its hash).
- **Stage 1** is `compiler/main.jh` compiled by the seed.
- **Stage 2** is `compiler/main.jh` compiled by stage 1.

Stage 1 is the current compiler built by an older one; stage 2 is the
current compiler built by itself. jihoo is self-hosted when the two agree:
for `compiler/main.jh`, stages 1 and 2 write the same IR, a fixed point.

## Bootstrap and packaging

`nix build` makes the compiler in three steps: the seed builds
`compiler/main.jh` at `-O2` (stage 1), stage 1 builds it again (stage 2),
and stage 2 is installed as `jihoo` once stages 1 and 2 write the same IR
for `compiler/main.jh`. `nix flake check` runs
[the tests](testing.md) with the installed compiler; their `selfhost`
suite has it build itself once more and compares the IR the two write for
every `.jh` file. By hand, in the dev shell, where `jihoo` is the seed:

```sh
jihoo build -O2 compiler/main.jh -o out/jihoo1          # stage 1
out/jihoo1 build -O2 compiler/main.jh -o out/jihoo2     # stage 2
JIHOO_COMPILER=/home/jihoo/jihoo/out/jihoo2 jihoo run tests/runner.jh
```

## The seed and releases

Pushing a tag `vX.Y.Z` runs `.github/workflows/release.yml`: it builds
the compiler of that tag with Nix on x86_64 and aarch64, and attaches
`jihoo-vX.Y.Z-<arch>-linux.tar.gz` (`bin/jihoo` and `share/jihoo/lib`) to
the release. The binary uses the system's dynamic loader, so it runs
outside Nix too; the flake patches it back for Nix.

`compiler/`, and the parts of `lib/std` it imports, may use only what the
seed knows. To use a new language feature or library function in the
compiler:

1. Add it to the compiler, with tests and documentation, without using it
   in `compiler/` yet.
2. Tag a release and let the workflow attach the binaries.
3. Move the seed in `flake.nix` to that release: its version and the
   hashes of both archives (`nix hash convert --hash-algo sha256 --to sri`
   of the `.sha256` files).
4. Use the feature in `compiler/`.

A released archive is never replaced, since the flake pins its hash.

## History

### Pass by pass, compared all the way

The port went one pass at a time, in the order the compiler runs them. Each
pass got a command that prints what it makes, in both compilers, in the
same format (`emit-tokens`, `emit-ast`, `emit-program`, `emit-mir` with and
without `JIHOO_NO_ELAB`, `emit-llvm`); `crates/jihoo/tests/selfhost.rs` built stage 1 and ran both
compilers on every `.jh` file of the repository, comparing output, errors
and exit status byte for byte, and ran the examples built by each.
Error messages were part of the comparison. Inputs meant to exercise one
pass live in `tests/selfhost/<pass>/`, and stay as inputs of the
`selfhost` suite. A `// load-args: ...` line in a file gives the commands
that load a program more options (`-I dir`, `--target aarch64`).

| step | jihoo | Rust | compared by | state |
|------|-------|------|-------------|-------|
| 1 | `diag.jh`, `lex.jh` | `diag.rs`, `lex.rs` | `emit-tokens` | done |
| 2 | `ast.jh`, `parse.jh` | `ast.rs`, `parse.rs` | `emit-ast` (`astdump.rs`, `astdump.jh`) | done |
| 3 | `load.jh`, `target.jh`, `os.jh` | `load.rs`, `target.rs` | `emit-program` (every module, its file and imports, then its tree) | done |
| 4 | `types.jh`, `mir.jh`, `sema.jh`, `body.jh`, `pat.jh`, `builtins.jh` | `types.rs`, `mir.rs`, `sema/` | `emit-mir` before elaboration (`JIHOO_NO_ELAB=1`), and the errors of `tests/fail` | done |
| 5 | `elab.jh`, `check.jh` | `elab.rs`, `check.rs` | `emit-mir`, `tests/fail` | done |
| 6 | `llvm.jh`, `main.jh` (the driver) | `llvm.rs`, `main.rs` | `emit-llvm` for both targets; `run` of `tests/run` and `examples` | done |
| 7 | stage 2 | | stage 2's `emit-llvm` against stage 1's, on everything | done |

Sema (step 4) is half of the compiler, about 6,000 of its 12,000 lines:
`sema/mod.rs` and `consts.rs` became `sema.jh`, `body.rs` `body.jh`,
`pat.rs` `pat.jh` and `builtins.rs` `builtins.jh`. Every program loads the
prelude, which uses nearly the whole language, so `emit-mir` on ordinary
programs could only agree once almost all of sema was ported. Until then
the comparison ran on small programs in `tests/selfhost/sema/` compiled
with `--no-prelude` (an option for this only, in both compilers), grown
feature by feature; they stay, as tests of single features and of sema's
errors. Now `emit-mir` agrees on every file in the repository, the
standard library and `compiler/` included.

Elaboration and the borrow kernel (step 5) followed: `emit-mir` is now
compared twice, before elaboration (`JIHOO_NO_ELAB=1`, which shows a
difference in sema alone) and after it, with borrows checked, so the
errors of `tests/fail` agree too. Inputs for drop flags and moved values
are in `tests/selfhost/elab/`.

The code generator (step 6) is compared by `emit-llvm`, on the host target
and on aarch64, and the driver by building and running the test programs
with each compiler. Both drivers now load LLVM 21's shared library through
the C API to verify, optimize and emit objects. Native linking uses a C
driver through `std.process`, and freestanding linking uses lld directly.
The previous clang pipeline is available with `JIHOO_BACKEND=clang` for
comparisons. Stage 1 builds stage 2 (step 7).

The Rust `Sema` keeps references into the syntax tree (`&'a ast::FnDecl`).
In jihoo a `ref T` read out of a table (`self.fns[f].decl`) carries the
borrow of the table, since there are no lifetimes to say that it points
elsewhere; changing `self` while holding it is then an error. The port
keeps raw pointers into the tree instead (`*ast.FnDecl`), read through
`sema.at`: the tree outlives sema and never changes, which is what Rust's
`'a` says.

### How the port is written

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
  `Hash`. jihoo has `derive` now, but `compiler/` may use it only once a
  release that has it is the seed.
- The code generator's many `format!` lines become `fmt.f`, which fills
  `{}` in a template from a slice of `str`s. Its `Gen` owns the program
  (Rust's borrows it), and takes a function's body out while writing it,
  since writing reads the rest of the program and adds types. The label
  of the block being written is kept as blocks start, where Rust finds it
  in the text written so far.

### The end of the Rust compiler

Once the compiler in jihoo built itself, it became the one installed and
the one the language changed in, and the Rust compiler was frozen: it
changed only so that it still built `compiler/`, which used only the
language it knew. Version 0.1.1 was the first release whose binaries are
the compiler in jihoo; it became the seed, and the Rust compiler, its
tests (now `tests/runner.jh`) and Cargo were removed.

### What porting has found

Writing a large program in jihoo is also a test of jihoo. Problems found so
far, each fixed in the Rust compiler with a test:

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
- Also left as it is and documented there: a method called on a `ref T`
  value (`self.types.variants(t).unwrap()`) is looked up on the borrow
  first, so `.clone()` copies the borrow and the result still borrows
  `self`; named first, the value clones the `T`
  (`tests/fail/clone_of_ref_value.jh`). Porting the rest of sema found no
  compiler bugs; it used `|` patterns that bind names (not supported) and
  `==` on a payload-free enum (needs `Eq`), both documented already.
- The Rust code generator wrote its declarations of external functions in
  `HashMap` order, so its IR differed from run to run; they are now in the
  order first needed, in both compilers.
- A module named `llvm` could not be compiled: its functions' symbols
  began with `llvm.`, which LLVM keeps for intrinsics (the code generator
  in jihoo is `llvm.jh`). Such symbols now get a `_` in front
  (`tests/run/module_llvm.jh`).
- The compiler in jihoo needs a large stack for deeply nested code, as
  the Rust one does: at the parser's depth limit, 498 nested calls take
  sema 16 MiB of stack built at `-O1` or `-O2` and 48 MiB at `-O0` (every
  temporary has its own stack slot), more than the 8 MiB a main thread
  usually gets. Like the Rust compiler it runs on a thread with a 256 MiB
  stack (`os.with_stack`, over libc's `pthread_create`; jihoo has no
  threads of its own yet). `tests/run/deep_nesting.jh` is code as deep as
  the parser accepts, and `tests/fail/nested_too_deeply.jh` one level more.
- Writing the code generator also met two limits, left as they are:
  string literals cannot span lines (long texts use `\n`), and `Map` has
  no `clone`.

And differences from Rust that are by design, now documented in
[Coming from Rust](../language/from-rust.md): `let (var a, b)`, and
`match` using up a whole owned variable on every path.

### `i128` and `u128`

Sema folds constants in `i128` (a `u64` and a negative number both fit) and
MIR keeps integer constants that way, so jihoo gained `i128` and `u128`
before step 4. A 128-bit constant is held as its bit pattern and folded at
that width (`fold_128` in `consts.rs`); freestanding programs get LLVM's
128-bit helpers from `std/rt.freestanding.jh`, tested against libgcc's on
both targets. Literals stay at most 64 bits for now. Adding `i128`
also found that a shift ignored the type its context expected:
`let b: u8 = 1 << 3` was an error (`tests/run/int128.jh`).

## Known issues

- A function returning `ref` whose last expression borrows one of its
  locals (`fn first() -> ref i64 { let p = P { x: 1 }; p.x }`) gets
  "`p` is used here after it was moved away" from elaboration: the
  block's scope ends before the result is written. With `return p.x` the
  borrow kernel says "`p` goes away here while it is still borrowed"
  (`tests/fail/borrow_return_local_ref.jh`). The first
  message should be the second.

