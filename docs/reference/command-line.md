# Command line

```text
jihoo run <file.jh> [link inputs] [-- args]   compile and run a program
jihoo build <file.jh> [-o out] [link inputs]  compile a program
jihoo emit-mir <file.jh>                      print the compiler's MIR
jihoo emit-llvm <file.jh> [-o out]            print LLVM IR
jihoo emit-tokens <file.jh>                   print the tokens of one file
```

`emit-tokens` prints one token per line (its byte range, whether a newline
came before it, the token); it exists to compare the compiler with the one
written in jihoo ([Self-hosting](../internals/self-hosting.md)).

| option | |
|--------|---|
| `-O0` … `-O3` | LLVM optimization (default `-O2`) |
| `--release` | integer overflow wraps instead of trapping |
| `--target x86_64\|aarch64` | the machine to compile for (Linux) |
| `-I <dir>` | also look for modules in `<dir>` |
| `-o <file>` | the output |
| `--keep-ll` | keep the LLVM IR next to the output |

Link inputs are C sources, object files and `-l`/`-L` flags, passed to the
C compiler when linking a native program.

## Environment

| variable | |
|----------|---|
| `JIHOO_CC` | the C compiler that turns LLVM IR into programs (default `clang`) |
| `JIHOO_PATH` | more directories to find modules in, separated by `:` |

The compiler writes LLVM IR as text and runs `clang` on it; freestanding
programs are linked with `ld.lld` (`-fuse-ld=lld`).
