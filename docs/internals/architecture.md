# Architecture

```text
source.jh ─► lex ─► parse ─► load ─► sema ─► MIR ─► elab ─► check ─► llvm ─► .ll ─► clang ─► program
```

The compiler is one Rust crate, `crates/jihoo`. It writes LLVM IR as text
and runs `clang`, which optimizes it and links the program (with libc, or
statically with `ld.lld` for freestanding programs). The Rust build does not
link LLVM.

The same compiler is written in jihoo in `compiler/`, a `.jh` file for
each file below, and that one is installed and is the reference; the Rust
crate bootstraps it ([Self-hosting](self-hosting.md)). This page names the
Rust files.

| file | what |
|------|------|
| `lex.rs`, `parse.rs`, `ast.rs` | tokens and the syntax tree; newlines end statements |
| `load.rs` | finds and parses every imported module, picking per-target and per-profile files |
| `types.rs` | interned types and their memory layout |
| `sema/` | names, types, generic instances, and lowering to MIR |
| `mir.rs` | the intermediate representation |
| `elab.rs` | initialization: use after move, drop elaboration and drop flags |
| `check.rs` | the borrow kernel: exclusivity and the lifetimes of views |
| `llvm.rs` | MIR to LLVM IR text |
| `main.rs` | the `jihoo` command |

## Sema

Sema checks and lowers in one pass per function instance. A generic
function is checked per instance, with its compile-time arguments known, as
in Zig: an instance is a declaration and its arguments, and calls make
instances, which a queue lowers one by one. Every non-generic function of
the program is lowered too, so it is checked even if nothing calls it.

Names are looked up in local variables, then compile-time parameters, then
the module, then the prelude's modules, then builtins. Methods are looked up
in the type's impls, then in impls of traits; impl heads are matched against
types to bind their parameters.

Sema decides how each value is used: a place in a value position moves (or
copies, if plain); a place passed to a borrowed parameter is borrowed; an
`inout` argument is borrowed mutably. It inserts a `Drop` for every owned
local at the end of its scope, and at `return` and `break`.

## MIR

A function is a control-flow graph over *places*: a local followed by
fields, variant payloads, array indices and dereferences. Statements assign
rvalues to places, mark locals live and dead, drop places, and forget
locals whose parts were taken. Terminators jump, switch, call, assert and
return. Every move, copy, borrow and drop is explicit, which is what the two
checking passes read.

`jihoo emit-mir file.jh` prints it.

## Elaboration

`elab.rs` follows which locals hold a value at every point. Using a local
that may have been moved is an error; a drop of a moved local is removed;
a local moved on some paths only gets a flag, and its drop checks it.

## The borrow kernel

`check.rs` does not trust sema. It finds every borrow in the MIR (a loan of
a place, held by a local), follows loans through views (copies, aggregates,
calls that return views, `inout` arguments that are views), and computes
which locals are used later. A loan lasts while some local holding it is
used later. Then it checks every access against the loans that last there:

- a place borrowed mutably may not be used through anything else;
- a place borrowed may not be changed, moved or dropped;
- a returned view may only borrow what the parameters point to.

The idea comes from proof checkers such as Horn: a large untrusted part
(sema) produces something a small part checks in full, so a bug in the
large part becomes a compile error and not a dangling pointer.

## Code generation

`llvm.rs` is simple on purpose:

- every local is an `alloca`; `mem2reg` and SROA make registers of them;
- fields are byte offsets, computed once in `types.rs`, which also lays out
  enums (a tag, then each variant's fields);
- aggregates are copied with `memcpy`, passed by pointer and returned
  through `sret`;
- borrowed parameters are pointers with `noalias` and `dereferenceable`
  (`readonly` for shared borrows), which the borrow rules make true;
- overflow checks use LLVM's `*.with.overflow` intrinsics, panics are cold
  and `noreturn`;
- destructors are glue functions per type: the `Drop` impl, then the parts.

The C `main` stores `argc` and `argv` and calls the program's `main`; a
freestanding program gets a `_start` in module-level assembly, and
definitions of `memcpy`, `memmove`, `memset` and `memcmp`.

## Written to be ported

The compiler will be rewritten in jihoo, so the Rust follows rules that
port line by line: data refers to other data by index (`TyId`, `Local`,
`BlockId`, `FnId`), references are only parameters (except the syntax tree,
which sema reads through one shared reference), and the code uses enums,
`match`, `Vec`, `HashMap` and `String`, all of which the jihoo standard
library has.
