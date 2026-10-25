# Testing

```sh
cargo test                                  # everything
cargo test --test programs                  # the programs in tests/
JIHOO_TEST=maps cargo test --test programs  # those whose path has `maps`
JIHOO_TEST_OPT=-O0 cargo test --test programs
JIHOO_COMPILER=out/jihoo2 cargo test --test programs  # with another compiler
cargo clippy --all-targets -- -D warnings
nix flake check                             # what CI runs
```

## Programs

`crates/jihoo/tests/programs.rs` compiles every file in `tests/run/` with
the built `jihoo`, runs it and compares its output, and compiles every file
in `tests/fail/` and checks the error:

- in `tests/run`, `//> text` lines are the expected standard output in
  order, `// exit: N` the exit status (default 0; a trap is 132), and
  `// args: a b` the program's arguments;
- in `tests/fail`, each `// error: text` must appear in the error message.

`JIHOO_COMPILER` names the compiler to test instead of the Rust one built
with the tests, such as the compiler in jihoo
([stage 1 or 2](self-hosting.md#bootstrap-and-packaging)); `nix flake
check` runs these tests with the installed one.

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
under `qemu-aarch64` (`nix-shell -p qemu`).
