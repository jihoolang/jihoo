# Architecture

```text
source.jh ─► lex ─► parse ─► load ─► sema ─► MIR ─► elab ─► check ─► llvm ─► LLVM C API ─► .o ─► linker ─► program
```

The compiler writes LLVM IR as text in memory. `backend` loads LLVM 21's
shared library, verifies and optimizes the module with the new pass manager,
then emits an object through the target machine C API. Native linking uses
a C driver for libc startup files; freestanding linking calls `ld.lld`
directly. The compiler needs no LLVM headers or C++ shim to build.
`JIHOO_BACKEND=clang` retains the previous pipeline for comparisons.

The compiler is written in jihoo, in `compiler/`, and a released build of
it bootstraps the next ([Self-hosting](self-hosting.md)).

| file | what |
|------|------|
| `lex.jh`, `parse.jh`, `ast.jh` | tokens and the syntax tree; newlines end statements |
| `load.jh` | finds and parses every imported module, picking per-target and per-profile files |
| `types.jh` | interned types and their memory layout |
| `sema.jh`, `body.jh`, `pat.jh`, `builtins.jh` | names, types, generic instances, and lowering to MIR |
| `mir.jh` | the intermediate representation |
| `elab.jh` | initialization: use after move, drop elaboration and drop flags |
| `check.jh` | the borrow kernel: exclusivity and the lifetimes of views |
| `llvm.jh` | MIR to LLVM IR text |
| `backend.jh` | LLVM 21 C API: verification, optimization and object emission |
| `main.jh` | the `jihoo` command |

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

The jihoo lowerer also tracks statically known closure functions by MIR
place, including immutable aliases and captures inside lifted functions.
Specialization selects a function while passing its ordinary environment
value; borrow checking still sees the environment and its captures. A
callback with known inputs and an unknown generic result is first checked
with those input types, then its full signature participates in generic
argument inference. The same inference applies to comptime callbacks.

## MIR

A function is a control-flow graph over *places*: a local followed by
fields, variant payloads, array indices and dereferences. Statements assign
rvalues to places, mark locals live and dead, drop places, and forget
locals whose parts were taken. Terminators jump, switch, call, assert and
return. Every move, copy, borrow and drop is explicit, which is what the two
checking passes read.

`jihoo emit-mir file.jh` prints it.

## Compile-time interpreter

`compiler/interp.jh` executes MIR for `const` initializers, `comptime`
expressions, array lengths and compile-time arguments. Simple arithmetic
still uses sema's constant folder. Other expressions use the normal lowerer
with a compile-time environment and no runtime locals. Reachable function
instances are lowered on demand, without draining the enclosing function's
pending queue.

Before execution, snapshots of the expression and reachable functions pass
elaboration and the borrow kernel. The runtime compilation pipeline retains
its original bodies. The interpreter follows basic blocks and call frames,
with bounded execution, recursion and allocation. Its memory is separate
from the compiler's address space: pointers encode allocation identities
and offsets, with checks for lifetime, bounds, initialization and pointer
bytes. Layout and enum payload offsets come from the target's `Types`.
Scalar results become MIR constants, strings become static strings, and
aggregates without addresses become `Const.Bytes`.

## Elaboration

`elab.jh` follows which locals hold a value at every point. Using a local
that may have been moved is an error; a drop of a moved local is removed;
a local moved on some paths only gets a flag, and its drop checks it.

## The borrow kernel

`check.jh` does not trust sema. It finds every borrow in the MIR (a loan of
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

`llvm.jh` is simple on purpose:

- every local is an `alloca`; `mem2reg` and SROA make registers of them;
- fields are byte offsets, computed once in `types.jh`, which also lays out
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

The compiler was first written in Rust and ported to jihoo line by line,
and it keeps the rules that made that possible: data refers to other data
by index (`TyId`, `Local`, `BlockId`, `FnId`), references are only
parameters (except the syntax tree, which sema reads through raw pointers),
and the code uses enums, `match`, `Vec`, `Map` and `String`.
