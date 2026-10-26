# Command line

```text
jihoo run <file.jh> [link inputs] [-- args]   compile and run a program
jihoo build <file.jh> [-o out] [link inputs]  compile a program
jihoo emit-mir <file.jh>                      print the compiler's MIR
jihoo emit-llvm <file.jh> [-o out]            print LLVM IR
jihoo emit-obj <file.jh> [-o out.o]           emit an object with LLVM
jihoo emit-tokens <file.jh>                   print the tokens of one file
jihoo emit-ast <file.jh>                      print the syntax tree of one file
jihoo emit-program <file.jh>                  print every module a program loads
```

`emit-tokens` prints one token per line (its byte range, whether a newline
came before it, the token), and `emit-ast` the syntax tree as
S-expressions with byte ranges, and `emit-program` every module the
program loads (its name, file and imports, then its tree); they exist to compare the compiler with the one
written in jihoo ([Self-hosting](../internals/self-hosting.md)).

A program with errors gets all of them in one run, in source order (the
first 20 are shown), each with notes: where a moved value went, where a
conflicting borrow started, and which generic instance, used where, an
error is in. Type errors come first. Move and borrow errors are reported
once the program has none.

| option | |
|--------|---|
| `-O0` … `-O3` | LLVM optimization (default `-O2`) |
| `--release` | integer overflow wraps instead of trapping |
| `--target x86_64\|aarch64` | the machine to compile for (Linux) |
| `-I <dir>` | also look for modules in `<dir>` |
| `-o <file>` | the output |
| `--keep-ll` | keep the LLVM IR next to the output |
| `--lib` | emit a library without an entry point, using `emit-obj` or `emit-llvm` |

Link inputs are C sources, object files and `-l`/`-L` flags, passed to the
C compiler when linking a native program.

## Environment

| variable | |
|----------|---|
| `JIHOO_LLVM` | path to LLVM 21's shared library; otherwise search `libLLVM-21.so`, `libLLVM.so.21.1`, `libLLVM.so` |
| `JIHOO_CC` | native linker driver and compiler for C source inputs (default `cc` on the host, `clang` for cross compilation) |
| `JIHOO_LD` | freestanding linker (default `ld.lld`) |
| `JIHOO_BACKEND` | `llvm` (default), or `clang` for comparison with the previous backend |
| `JIHOO_PATH` | more directories to find modules in, separated by `:` |

The compiler builds LLVM IR in memory, parses and verifies it through LLVM
21's C API, runs `default<O0>` through `default<O3>`, and emits an object
with a target machine. Loop and SLP vectorization are enabled at `-O2`
and `-O3`. It uses portable `x86-64`/`generic` CPUs and PIC code.

Native objects are linked by `JIHOO_CC`, including libc startup code, libm
and libdl. Freestanding objects are linked directly with `JIHOO_LD`,
statically, with unused function sections removed. `emit-obj` needs only
libLLVM and can cross-compile without a linker or target libc. Native
cross linking additionally needs a suitable linker driver and target
libraries; a GCC cross driver supplied in `JIHOO_CC` selects its own target.

`emit-llvm` still writes the original IR and needs no LLVM shared library.
`emit-obj --lib` accepts a module without `main`, exposes its `export fn`
symbols and emits no startup wrapper. Link the object from C, put it in
an archive with `ar`, or build a shared library with `cc -shared`.
`--keep-ll` preserves that IR alongside an executable. `JIHOO_BACKEND=clang`
uses the previous IR-file/clang pipeline (`JIHOO_CC` defaults to `clang`
in that mode); the compiler does not silently fall back when LLVM is missing.
