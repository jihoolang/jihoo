# Command line

```text
jihoo fmt <file.jh> [--check] [--width N]    format source or check its layout
jihoo check <file.jh> [--lib]                check without generating code
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
| `--lib` | omit the entry point, using `check`, `emit-obj` or `emit-llvm` |
| `--error-format=text\|json` | source diagnostic format (default `text`) |
| `--comptime-report <path>` | write interpreter resource measurements as a separate JSON file |

Link inputs are C sources, object files and `-l`/`-L` flags, passed to the
C compiler when linking a native program.

## Source formatting

```sh
jihoo fmt src/main.jh                       # formatted source on stdout
jihoo fmt src/main.jh --check               # verify layout without printing it
jihoo fmt src/main.jh --width 80            # a different soft width
```

`fmt` parses one file and prints its formatted source. It uses four spaces
per delimiter level, normalizes spaces between tokens, removes leading and
trailing blank lines and retains at most one empty line between source
elements. Nonempty and empty files end with one LF. Comments retain their
exact bytes, including whitespace inside comment bodies; literals keep
their original spelling and escapes.

Existing line breaks between tokens remain in place because newlines can
end statements or separate list elements. Lists that exceed a soft width
of 100 byte columns expand with a break after the opening delimiter, after
each separator and before the closing delimiter. This covers arguments,
parameters, arrays, tuples, struct fields and variant lists identified by
the parser. Outer lists expand first; nested lists are reconsidered at their
new indentation. Commas and semicolons retain their original spelling.

`--width N` accepts decimal integers from 20 through 1000. It counts UTF-8
bytes, like diagnostic columns. It is a soft target: long literals, comments
and expressions without a supported list boundary may exceed it. Short
lists remain compact. Function and statement blocks are not expanded just
because they contain a comma, such as a `for` index. Inline comments keep
their bytes and remain before the token they originally preceded; a new
break may follow an inline block comment. Multiline block comment bodies
are not reindented. Reformatting with the same width produces the same bytes.

Before returning any source, the formatter re-lexes it, requires the same
token kinds and spellings, and checks that no existing newline flag was
removed. It then reparses the result and compares the complete syntax trees
with source positions omitted. A changed tree is rejected. It formats
modules without loading imports, type checking or running compile-time
expressions, and needs neither LLVM nor a linker. Syntax errors use normal
source diagnostics, including `--error-format=json` when selected.

`--check` uses the selected width, writes nothing and exits with status 0 when the file is formatted.
When layout differs, it exits with status 1 and prints `FILE: needs formatting`
to standard error as text. Invalid syntax also exits with status 1; invalid
options exit with status 2. `fmt` rejects `-o`, `--keep-ll`, link inputs and
program arguments. It reads the source file without modifying it; no files
or build artifacts are created.

## Checking without code generation

```sh
jihoo check app.jh
jihoo check -I src src/main.jh --target aarch64
jihoo check --lib src/parser.jh
```

`check` loads the root module and its imports, checks types, evaluates
compile-time expressions, elaborates moves and drops, and checks borrowing.
As with a build, non-generic functions are checked even when unused;
generic bodies are checked for the instances the program requests.
By default the root module must have a `main`; `--lib` removes that requirement.

A successful check exits with status 0 and writes nothing by default. Source errors
exit with status 1 and use the same diagnostics as compilation. Invalid
command options exit with status 2. `check` rejects `-o`, `--keep-ll`, link
inputs and program arguments because it produces no output file and does
not run the program.

Checking does not emit LLVM IR, load libLLVM, or invoke a C compiler or
linker. External function declarations need no linked implementation for
checking. Compile-time obligations still execute and may fail or reach the
interpreter's limits. Checking does not establish that backend code
generation or linking will succeed. `JIHOO_NO_ELAB`, the debug switch for
unelaborated MIR dumps, never disables move or borrow checking in this mode.

## Compile-time resource reports

```sh
jihoo check app.jh --comptime-report resources.json
jihoo build app.jh --comptime-report resources.json -o app
```

`--comptime-report` writes a versioned JSON document after semantic checking,
including when an interpreter invocation failed. It records the target,
arithmetic mode, evaluator limits and an `evaluations` array. Each invocation
has its obligation's source span, success status, execution/validation steps,
cumulative simulated allocation bytes, allocation count, maximum active MIR
calls and per-function costs. Function costs are exclusive: their steps,
allocation bytes and allocation counts add up to the invocation's totals.
Calls to the provided allocator are counted separately from their callers.
Repeated evaluation of the same expression appears as separate invocations.

Allocation bytes include retained local storage and heap allocations, even
after their lifetimes end. They measure the evaluator's cumulative allocation
budget, not compiler process memory. The report excludes parsing, lowering,
borrow checking, optimization and linking costs. Measure compiler time and
process memory separately when comparing complete compilations.

The option works with `check`, `build`, `run`, `emit-mir`, `emit-llvm` and
`emit-obj`. It does not change interpreter limits or generated code. Reports
use a separate file, so successful checks remain silent and JSON source
diagnostics remain one document on stderr. A source-loading or syntax error
before semantic checking does not produce a report. Existing report files
are replaced; a loaded source file cannot be used as the report destination.

## Structured source diagnostics

```sh
jihoo check app.jh --error-format=json
jihoo check --lib src/parser.jh --error-format=json
```

`--error-format=json` writes one JSON document to standard error when a
source error is reported. Loading, lexing, parsing, type checking,
compile-time evaluation, move checking and borrow checking use the same
diagnostic data as the default text format. It works with all compiler
commands. `--error-format=text` explicitly selects the default; if repeated,
the last format option before `--` wins.

For example, a module without `main` produces a document with this shape:

```json
{
  "version": 1,
  "diagnostics": [
    {
      "severity": "error",
      "message": "the program has no `main` function",
      "span": {
        "file": "input.jh",
        "start": { "byte": 0, "line": 1, "column": 1 },
        "end": { "byte": 0, "line": 1, "column": 1 }
      },
      "notes": []
    }
  ],
  "error_count": 1,
  "truncated": false
}
```

- `version` identifies this document schema. Each diagnostic has a message,
  primary span and ordered `notes`. Each note has `message` and `span`;
  notes include move origins, conflicting borrows and generic-instance context.
- A span contains the source path as loaded and its start and exclusive end.
  `byte` is a zero-based byte offset; `line` and `column` are one-based, with
  columns measured in bytes, matching text diagnostics. Editors using UTF-16
  positions must convert from the source text. Ranges are clamped to the
  available source; zero-width ranges are valid. A missing source or an
  unlocated note has `span: null`.
- Strings are escaped as JSON, with invalid UTF-8 replaced by U+FFFD. The
  numeric offsets still refer to the original source bytes.
- Errors retain text diagnostic order and the limit of 20 displayed errors.
  `error_count` includes omitted errors; `truncated` says whether any were
  omitted. Related notes are not counted as separate errors.

Success remains silent in `check` mode, and source errors still exit with
status 1. Command-line usage errors, backend/linker errors and a running
program's own standard error remain text; this option formats source
diagnostics only. Standard output retains the selected command's normal
output, such as emitted IR or program output.

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
