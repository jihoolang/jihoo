# Command line

```text
jihoo fmt <paths> [--check|--write] [--width N]  format source or check its layout
jihoo check <file.jh> [--lib]                check without generating code
jihoo lsp [-I dir] [--target t]               serve the Language Server Protocol on stdio
jihoo run <file.jh> [link inputs] [-- args]   compile and run a program
jihoo build <file.jh> [-o out] [link inputs]  compile a program
jihoo test <file.jh> [link inputs] [-- names]  run the file's #[test] functions
jihoo emit-mir <file.jh>                      print the compiler's MIR
jihoo emit-obligations <file.jh>              print MIR as the verification model
jihoo verify <file.jh> [--all]                list the checks verification cannot remove
jihoo emit-llvm <file.jh> [-o out]            print LLVM IR
jihoo emit-obj <file.jh> [-o out.o]           emit an object with LLVM
jihoo emit-tokens <file.jh>                   print the tokens of one file
jihoo emit-ast <file.jh>                      print the syntax tree of one file
jihoo emit-program <file.jh>                  print every module a program loads
jihoo --version                               print the compiler's version
```

`jihoo --version` (or `-V`) prints `jihoo` and the release the compiler
belongs to, such as `jihoo 0.2.0`; `jihoo --help` prints the usage.

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
| `--verify` | remove the checks [verification](#verification) proves (`build`, `run`, `test`, `emit-llvm`, `emit-obj`) |
| `--target x86_64\|aarch64` | the machine to compile for (Linux, or UEFI for a `#![uefi]` program) |
| `-I <dir>` | also look for modules in `<dir>` |
| `-o <file>` | the output |
| `--keep-ll` | keep the LLVM IR next to the output |
| `--lib` | omit the entry point, using `check`, `emit-obj` or `emit-llvm` |
| `-mno-red-zone` | never keep data below the stack pointer ([kernels](../language/profiles.md#kernel-code-generation)) |
| `-mgeneral-regs-only` | use no floating-point or vector registers, and reject floats ([kernels](../language/profiles.md#kernel-code-generation)) |
| `--error-format=text\|json` | diagnostic format for every failure (default `text`) |
| `--comptime-report <path>` | write interpreter resource measurements as a separate JSON file |
| `--time-passes` | report the time and memory of each phase on standard error |

Link inputs are C sources, object files and `-l`/`-L` flags, passed to the
C compiler when linking a native program.

## Source formatting

```sh
jihoo fmt src/main.jh                       # formatted source on stdout
jihoo fmt src/main.jh --check               # verify layout without printing it
jihoo fmt src/main.jh --width 80            # a different soft width
jihoo fmt src tests --check                 # every .jh file under src and tests
jihoo fmt src --write                       # rewrite the files that need it
```

`fmt` parses one file and prints its formatted source. Given several files
or a directory, it requires `--check` or `--write`. A directory contributes
its `.jh` files and those of the directories in it, in sorted order; entries
whose names start with `.` are skipped, and a directory reached again through
a symbolic link is visited once. Files named on the command line are
formatted whatever their extension. It indents four
spaces per line that leaves a delimiter open: several delimiters opened on
one line, as in `f(match x {` or `Ok(S {`, add one level together, and a
line that starts with closing delimiters returns to the indentation of the
line that opened them. A continuation line inside a delimiter whose first
element is on the delimiter's line is indented by that delimiter alone.
It normalizes spaces between tokens, removes leading and trailing blank
lines and retains at most one empty line between source elements.
Nonempty and empty files end with one LF. Comments retain their exact
bytes, including whitespace inside comment bodies; literals keep their
original spelling and escapes.

Existing line breaks between tokens remain in place because newlines can
end statements or separate list elements. Lists that exceed a soft width
of 100 byte columns expand with a break after the opening delimiter, after
each separator and before the closing delimiter. This covers arguments,
parameters, arrays, tuples, struct fields and variant lists identified by
the parser. Outer lists expand first; nested lists are reconsidered at their
new indentation, and only the lines holding a list's own delimiters and
separators make it overflow, with any `?`, closing delimiters and calls
without arguments that follow it, as in `f(a, b).as_str())`. Parameter
lists also expand for a long return type after them. A list whose only
element is a call or struct literal, as in `Err(err(span, message))`, lets
that element expand instead (`Err(err(` ... `))`), and a single element
that would not fit on a line of its own either is left in place. Long
expressions without a list, such as string concatenations and conditions,
keep their own line breaks: break them after an operator such as `+` or
`&&`, and the continuation is indented. Commas and semicolons retain their
original spelling.

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

`--check` uses the selected width, writes nothing and exits with status 0 when every file is formatted.
When layout differs, it exits with status 1 and prints `FILE: needs formatting`
to standard error for each such file, or a `format` diagnostic with
`--error-format=json`. `--write` replaces the files whose layout differs
and leaves the others untouched. With either option, every file is
processed before failures are reported, in file order: files that need
formatting, syntax errors, and files that cannot be read or written, all
in one JSON document when it is selected. Invalid syntax also exits with status 1; invalid
options exit with status 2. `fmt` rejects `-o`, `--keep-ll`, link inputs and
program arguments. Without `--write` it reads the source files without
modifying them; it never creates files or build artifacts.

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

## Tests

```sh
jihoo test parser.jh                  # every #[test] function of parser.jh
jihoo test parser.jh -- number string # those whose names contain `number` or `string`
```

```jihoo
fn add(a: i64, b: i64) -> i64 {
    a + b
}

#[test]
fn adds() {
    assert(add(2, 3) == 5, "2 + 3 is 5")
}
```

`#[test]` marks a free function that takes no parameters and returns
nothing. `jihoo test` builds the file with a harness in place of `main`
(the file needs none, and its `main` does not run) and runs each test
function in a process of its own: the file's, then those of the modules
it imports, directly or not, outside the standard library. Those are
named with their module, as in `util.text.trims`, and may be private:
each module calls its own. A test passes when it
returns. It fails when it panics (`assert` included), traps or exits with
another status, and only that test fails: the others still run. Output:

```text
running 2 tests
test adds ... ok
test fails ... FAILED

failures:

---- fails ----
panic: 2 + 2 is not 5
signal 6

test result: FAILED. 1 passed; 1 failed; 0 filtered out
```

Each test's standard output and standard error are kept and printed only
when it fails, followed by its exit status or signal. `jihoo test` exits
with status 0 when every test chosen passed and 1 otherwise. Arguments
after `--` choose the tests whose names contain one of them.

The standard library's tests run when one of its files is the one given:
`jihoo test lib/std/string.jh`. A file of the library given to any command
is that module (`std.string`), with the access to the library's private
items it has when imported. Tests run in
native and freestanding programs; UEFI programs cannot run here. Elsewhere,
`#[test]` functions are ordinary functions, checked by `check` and `build`.
With `-o`, the test program is kept; given the name of a test as its one
argument, it runs it and exits with status 0, or with 2 for a name it does
not know.

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

## Phase timings

```sh
jihoo build compiler/main.jh --time-passes -o out/jihoo
```

```text
phase              elapsed       cpu       peak
load                0.074s    0.073s   47.1 MiB
sema                0.256s    0.254s  170.4 MiB
elaboration         0.112s    0.112s  172.9 MiB
effects             0.168s    0.168s  185.0 MiB
borrows             0.618s    0.617s  258.0 MiB
IR generation       0.193s    0.192s  258.0 MiB
LLVM parse          0.462s    0.460s  258.0 MiB
LLVM optimize      11.765s   11.693s  274.6 MiB
LLVM emit           1.962s    9.492s  373.5 MiB
link                0.216s    0.214s  373.5 MiB
total              15.831s   23.280s  373.5 MiB
```

`--time-passes` measures each phase inside the compiler and writes a table
on standard error when compilation ends: `load` (reading and parsing every
module), `sema` (names, types, generic instances, compile-time evaluation
and lowering to MIR), `elaboration` (moves and drops), `effects` (what each
function's borrows may store or return), `borrows` (the borrow checks), `IR
generation` (`llvm.jh`), then LLVM's `parse`, `optimize` and `emit` (object
emission, in several threads for a large module), and `link`. `check` stops
after `borrows`, `emit-llvm` after `IR generation` and `emit-mir` after
`MIR text`; with `JIHOO_BACKEND=clang`, `clang` replaces the LLVM phases
and the link. Writing a `--comptime-report` is a phase of its own.

`elapsed` is wall-clock time; `cpu` is the user and system time of every
thread of the compiler and of the programs it waited for (the linker), so it
exceeds `elapsed` where a phase runs in parallel. `peak` is the compiler's
peak resident memory once the phase ended. `total` covers the compiler from
loading on. Times are truncated to milliseconds.

Nothing else changes: standard output, the files written, exit statuses and
diagnostics are the same with or without the option. When compilation fails,
the phases that ran come first and the diagnostics, text or JSON, follow
unchanged; `run` reports before the program starts, so the program's own
output comes after the table. The option works with `check`, `build`, `run`,
`emit-mir`, `emit-llvm` and `emit-obj`.

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
      "kind": "source",
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

- `version` identifies this document schema. Each diagnostic has a `kind`,
  a message, primary span and ordered `notes`. Each note has `message` and `span`;
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

Every unsuccessful invocation writes one document of this schema, and
`kind` says what failed:

| kind | exit status | |
|------|-------------|---|
| `source` | 1 | an error in the program's source, with its span and notes |
| `usage` | 2 | an invalid command line, such as an unknown option or command; the usage text is left out |
| `io` | 1 | a file that cannot be read or written, or a program `run` cannot start |
| `backend` | 1 | LLVM, object emission or the linker failed; the message keeps the tool's output |
| `format` | 1 | `fmt --check` found a file that needs formatting; the zero-width span is at the first byte that differs |

A failure other than `source` has one diagnostic with no notes, and its span
is `null` unless stated above. The option applies wherever it appears before
`--`, including after the option that failed. Success remains silent in
`check` mode. A running program's own standard error and exit status are not
the compiler's and remain unchanged. Standard output retains the selected
command's normal output, such as emitted IR or program output.

## Language server

```sh
jihoo lsp
jihoo lsp -I src --target aarch64
```

`lsp` speaks the [Language Server Protocol](https://microsoft.github.io/language-server-protocol/)
on standard input and output, for editors that start it as a server. It
takes no files; `-I` and `--target` apply to every document. It provides:

- **Diagnostics.** Each open document is checked as `check --lib` would
  check it, with the editor's unsaved text used for every open document in
  place of the file on disk, so a document checks against the open versions
  of the modules it imports. Checks run when a document is opened, changed
  or saved, once the server has no further messages waiting, so a burst of
  edits is checked once. An error is published at its own range when it is
  in the checked document; otherwise at the first note located there, such
  as the use of a generic instance, with the error's own location in
  `relatedInformation`; otherwise in the file it belongs to. Notes become
  `relatedInformation`, and notes without a location are appended to the
  message.
- **Go to definition**, from the syntax trees the loader builds: a local
  binding in scope (a parameter, `let`/`var`, a `for`, `match` or closure
  binding), then items of the module and of its imports, the prelude and
  the modules it makes visible, then variants, fields and methods by name.
  `module.name` looks in that module, `Type.name` among that type's
  variants, fields and methods, and `value.name` among every field and
  method of that name, since the receiver's type is not resolved; such a
  request may return several locations.
- **Formatting** of a whole document with `fmt`'s default width, as one edit.
  A document with syntax errors is left unchanged.

Positions use UTF-8 byte offsets when the client lists `utf-8` among its
`positionEncodings`, and the protocol's default UTF-16 code units otherwise.
Documents are synchronized in full. Other requests return the protocol's
`MethodNotFound` error. A check runs on the server's single thread, so a
document that takes long to check (the compiler itself takes seconds) delays
replies until it finishes. The server exits with status 0 after `shutdown`
and `exit`, and 1 when its input ends or `exit` comes first.

## Verification

```sh
jihoo verify app.jh                  # the checks that stay, and why
jihoo verify app.jh --all            # every check, proved or kept
jihoo build --verify app.jh          # without the proved checks
```

[Verification](../internals/verification.md) proves that checks the
compiler inserts cannot fail: bounds checks (`assert` in MIR) and, in debug
builds, the overflow checks of `+ - *`. A call to a function that never
returns (`panic`, `abort`) and `trap()` are checks too: that the path
cannot be taken. A call to a small function that may panic is a check at
the call, named by the panic's message: that the callee does not reach its
panic from there, as a call `v[i]` to `Vec.index` in a loop over `v`
does not. It also proves [contracts](../language/contracts.md). `verify`
prints one line per check that stays, at the check's position, with what
it is, the function, and where the values it depends on come from (the
reasons of the [model](#verification-model), plus `argument`, `loop` and
`call`):

```text
app.jh:9:9: kept integer overflow in sum (loop, load)
app.jh:12:5: kept index out of bounds in first (argument, call)
app.jh:14:5: unproved `requires` of bump in unchecked
app.jh:56:13: unproved `ensures` in wrong
42 of 57 checks proved in 31 functions (0 not followed everywhere)
```

A contract clause that is not proved is listed too: an `ensures`, a
written `invariant`, or a call whose callee's `requires` it does not meet.
A proof counts only when everything it rests on is proved: a function's
`requires` when every call to it meets it (a function that is exported,
the entry, a destructor or used as a value is never assumed to be called
that way), a callee's `ensures`, and the invariants of loops, inferred or
written. `--machine` prints the verdicts of the root file's functions in
the line format jihoo-proofs' differential test reads. `--verify` on a
build runs the same verification and compiles without the proved checks:
an `assert` becomes a jump, a checked `+ - *` wraps, a call that never
returns becomes `unreachable` (so its branch goes away), and a call that
proved its callee's panics away calls a copy of the callee without them.
The program does the same, without their cost. `JIHOO_VERIFY_TRACE=1`
prints the time each function took on standard error.

## Verification model

`emit-obligations` prints each function's MIR as the integer model that
[verification](../internals/verification.md) proves things about, one
S-expression per function: its name and symbol, its argument count, a kind
per variable (`(int lo hi)` with the type's range, `bool` or `other`), its
[contract](../language/contracts.md), and its blocks, numbered as `emit-mir`
numbers them, of `(set variable value)` statements and one terminator.

The variables are the locals, then extra ones: a `str` or slice local's
length (`lengths`, pairs of local and variable), the integer an `inout`
integer parameter points to (`derefs`), when the pointer is used only to
read, write or lend it, integer fields (`fields`, each
`(VAR LOCAL [*] FIELD...)`: the fields below the local, through it when
`*` says it is a borrow), and the value on entry of each parameter's
variables (`entries`, pairs of variable and entry variable).

A field is a variable when the model sees everything that changes it: its
local's address is never taken (`&raw`), every mutable borrow of the local
or its parts is passed to one call, and no part of its type is
`#[interior]`. An assignment to it, or to a place that contains it, gives
it a value (`set`); so does an assignment to the borrow it is reached
through. A call that is lent such a place, is given a mutable borrow it
reaches, or writes its result there, gives it a new one. Nothing else can
change it: the borrow kernel lets no other borrow change what a borrow
reaches while it lives, a shared borrow promises that nothing changes,
and unsafe code that writes through a raw pointer to a place held under a
borrow, or to a local whose address it was not given, breaks the same
promise that `noalias` on borrowed parameters already relies on.

```text
(function clamp main.clamp.1
  (args 3)
  (locals (int -9223372036854775808 9223372036854775807) ... bool bool ...)
  (lengths)
  (derefs)
  (entries (1 7) (2 8) (3 9))
  (requires (le (lin 0 (2 1)) (lin 0 (3 1))) (at 55 63))
  (ensures (le (lin 0 (8 1)) (lin 0 (0 1))) (at 76 88))
  (ensures (le (lin 0 (0 1)) (lin 0 (9 1))) (at 92 104))
  (block 0
    (set 4 (cmp lt (local 1) (local 2)))
    (switch 4 2 1))
  ...
```

Each clause is `(requires (op A B) (at lo hi))`, `(ensures ...)` or
`(invariant BLOCK (op A B) (at lo hi))`, where `BLOCK` is the loop's head
and `op` one of `lt le gt ge eq ne`. A side is `(lin c (v k)...)`, the
constant `c` plus `k` times each variable `v`, computed exactly: `result`
is variable 0, and a parameter in `ensures` or `old(x)` is its entry
variable. A side over a variable the model does not have is
`(opaque escaped)`. A call is
`(call DST NEXT (fn SYMBOL) (args A...) [(never)] [(changes V...)] [(fields (P V FIELD...)...)] (at lo hi))`,
without `fn` through a pointer or closure. An argument is an operand,
`(view n)` for a slice or `str` with length variable `n`, or `(lent v)` for
a variable lent to an `inout` parameter, which the call may change.
`(never)` marks a callee that never returns: the call is a check that it
is not reached. `changes` lists the other variables the call gives new
values: fields inside what it is lent or where its result goes, and a
slice result's length. `fields` maps the callee's fields named by its
contract, or read by a small function whose panics calls may prove away,
to the caller's variables: field `FIELD...` of parameter `P` (through it
if it is a borrow; `P` 0 is the result) is variable `V` here. `trap()` is
`(trap (at lo hi))`.

The model follows integer and bool locals, `+ - *` that check for overflow,
comparisons, `!`, `&&`, integer casts, `switch` on a bool, `assert`, calls
and returns. Everything else is `(opaque why)`, a value known only to be in
its type's range, with the reason it is not followed: `load` (through a
pointer or borrow), `field`, `variant`, `element`, `aggregate` (a local that
is not an integer), `escaped` (a local whose address is taken, `&x` for an
`inout` parameter or `&raw`, since it may change through that pointer,
except a borrow only passed to one call, as `bump(&x)` passes it),
`wrap` (wrapping arithmetic, all of it with `--release`), `div`, `rem`,
`shift`, `bits`, `neg`, `bool`, `pointer`, `tag`, `constant` and `length`. A `switch`
the model does not follow is `(any blocks...)`. Each check ends with
`(at lo hi)`, the byte range where compile-time evaluation reports it
failing: an `assert`, and a `set` whose `+ - *` checks for overflow. The format is research and
may change; [jihoo-proofs](https://github.com/jihoolang/jihoo-proofs/tree/main/obligations)
reads it.

## Environment

| variable | |
|----------|---|
| `JIHOO_LLVM` | path to LLVM 21's shared library; otherwise search `libLLVM-21.so`, `libLLVM.so.21.1`, `libLLVM.so` |
| `JIHOO_CC` | native linker driver and compiler for C source inputs (default `cc` on the host, `clang` for cross compilation) |
| `JIHOO_LD` | freestanding and UEFI linker (default `ld.lld`; UEFI images use its COFF linker, `-flavor link`) |
| `JIHOO_BACKEND` | `llvm` (default), or `clang` for comparison with the previous backend |
| `JIHOO_CODEGEN_UNITS` | the number of code generation units for `build` and `run`, instead of one per 20,000 LLVM instructions (at most 8) |
| `JIHOO_PATH` | more directories to find modules in, separated by `:` |

The compiler builds LLVM IR in memory, parses and verifies it through LLVM
21's C API, runs `default<O0>` through `default<O3>`, and emits an object
with a target machine. Loop and SLP vectorization are enabled at `-O2`
and `-O3`. It uses portable `x86-64`/`generic` CPUs and PIC code.

`build` and `run` optimize the whole module at once, so inlining sees every
function, and then emit a large module as several objects on separate
threads: consecutive functions of about 20,000 instructions each, at most
eight units, linked in their original order. The units are formed by
halving, each half on a thread with its own LLVM context, so that a few
copies of the module are in memory at once rather than one per unit. The number depends only on
the module, so every host writes the same objects; a program small enough
for one unit is emitted exactly as by `emit-obj`. In split modules, local
functions and variables become hidden symbols, which the linker makes
local again in the executable; unnamed constants are copied into each unit
that uses them. `emit-obj` always writes a single object.

Native objects are linked by `JIHOO_CC`, including libc startup code, libm
and libdl. Freestanding objects are linked directly with `JIHOO_LD`,
statically, with unused function sections removed. UEFI programs are COFF
objects that `JIHOO_LD -flavor link` links into an EFI application
(`/subsystem:efi_application /entry:efi_main`); `build` names the image
`<file>.efi` unless `-o` says otherwise, and `JIHOO_BACKEND=clang` does not
build them. `emit-obj` needs only
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
