# Design: jihoo 0.1

Status: implemented, as the `v0.1` branch; what is left is on the
[roadmap](roadmap.md). This page is the plan for the rewrite, which broke
compatibility with everything before it, and the reasons for it. The
language before the rewrite is called *v0* below.

## Goals

1. **As fast as C.** No GC, no reference counting, no hidden copies, no
   runtime. What a program does is what it costs.
2. **Safer and simpler than Rust.** Memory safety and freedom from data races
   without lifetimes, lifetime annotations or a borrow checker anyone has to
   think about.
3. **A compiler that can be written in jihoo.** The next project is to write
   the compiler in jihoo, so the language must be good at that kind of
   program (trees, tables, strings, files, processes), and the compiler must
   be small and written in a style that ports line by line.

## What v0 taught

v0 had three profiles with three memory models: a VM with a GC (`hosted`),
native code where an inferred ownership pass inserted copies and reference
counts, and freestanding code with raw pointers only. That was too much
language for one implementation:

- **Every feature was built up to three times** (VM, native, freestanding) and
  had to agree, which the differential tests and the fuzzer enforced. Most of
  the compiler (the VM, the ownership pass and its checker, the list and
  string instructions in the backend) existed to make the three agree.
- **Copies were implicit.** Value semantics with inferred moves is easy to
  write, but a small change could turn a move into a copy of a whole tree.
  `nocopy`, `--cost` and the rule system existed to find and remove those
  copies after the fact. 13 of the last 25 roadmap items were about copies.
- **No mutation through parameters.** A function that changes a value takes
  it and returns it (`inp = skip_space(inp)`), and the compiler had to prove
  that this did not copy.
- **The backend knew about lists, strings, closures, channels and files.**
  Containers were built into the compiler, in C++, so they could not be
  improved in jihoo, and a compiler written in jihoo would also have to
  carry them.

## The language in one page

```jihoo
struct Point {
    x: i64
    y: i64
}

impl Point {
    fn norm2(self) -> i64 {
        self.x * self.x + self.y * self.y
    }
    fn shift(inout self, d: i64) {
        self.x += d
    }
}

enum Expr {
    Num(i64)
    Add(Box(Expr), Box(Expr))
}

fn eval(e: Expr) -> i64 {
    match e {
        Num(n) => n
        Add(a, b) => eval(a) + eval(b)
    }
}

fn main() {
    var p = Point { x: 3, y: 4 }
    p.shift(1)
    var xs = Vec(i64).new()
    xs.push(p.norm2())
    for x in xs {
        println(x)
    }
}
```

### Values and ownership

Every value has one owner: a variable, a field, an element. There are no
references to store, so there are no lifetimes.

- **Moves.** Assigning, passing to a `sink` parameter or returning a value
  that owns memory moves it; the old variable cannot be used until it is
  assigned again. The compiler checks this.
- **Copies are explicit.** Types without owned memory or a destructor (all
  numbers, pointers, and structs, enums and arrays made only of such types)
  are *plain* and copy implicitly, as in C. Others are copied by
  `x.clone()`, which their `Clone` impl defines.
- **Destruction is deterministic.** When the owner of a value goes away, its
  `Drop` impl runs, then the drops of its parts. The compiler generates this
  glue. Values moved on conditionally get drop flags.
- **`let` and `var`.** `let` names cannot be assigned again; `var` names
  can. `let x = <place>` *borrows* the place for the rest of the block (no
  copy, no move); `let x = <value>` owns a new value; `var x = <place>`
  moves (or copies a plain value).

### Parameter conventions

What a function does with an argument is part of its signature, as in Hylo
or Swift:

| parameter | meaning | at the call | passed as |
|-----------|---------|-------------|-----------|
| `x: T` | borrowed: read only for the call | `f(x)` | a pointer, or the value if plain and small |
| `inout x: T` | borrowed mutably: no one else sees `x` during the call | `f(&x)` | a `noalias` pointer |
| `sink x: T` | owned: the function takes it | `f(x)` (moves) | a pointer to the moved value |

A method's `self` takes the same conventions, and `x.f()` passes `&x`
automatically when `self` is `inout`.

References exist, but only as parameters, local borrows (`let x = place`,
`inout x = &place`), projections (below) and *views*. None can be stored in
an ordinary struct or outlive what it borrows, so a borrow always ends at a
place the compiler sees.

### Views

`str`, slices, closures and borrows are views: values that point into
something owned elsewhere. A type that contains a view, or is instantiated
with one (`Vec(str)`, `Option(ref T)`), is a view too, and a library type
holding borrows through raw pointers says `#[view]` (the `Vec` iterator).
Views can be kept in locals, returned and stored in other views; the
compiler follows what each one borrows (copies, aggregates, calls that
return views, `inout` arguments that are views), keeps the borrowed values
alive and unchanged while a view of them is used, and lets a function return
only views of what its parameters point to. This is what Rust's lifetimes
do, without annotations: every borrow is scoped to a function body, so the
checker sees all of it.

### Exclusivity

One rule replaces the borrow checker: **while something is borrowed mutably,
nothing else may use it; while something is borrowed, no one may change it.**
Because borrows are scoped to a call or a block, the compiler checks this
locally, per function, comparing the places involved:

```jihoo
swap(&a, &a)          // error: `a` is borrowed mutably twice
f(&xs, xs[0])         // error: `xs` is read while borrowed mutably
for x in xs {
    xs.push(x)        // error: `xs` is changed while the loop borrows it
}
```

The payoff is speed as well as safety: an `inout` parameter cannot alias
anything, so the compiler tells LLVM (`noalias`), which C compilers can only
do where a programmer writes `restrict`.

### Projections

A function may return a borrow of part of its first parameter:

```jihoo
impl(T: type) Vec(T) {
    fn get(self, i: i64) -> ref T { ... }
    fn get_mut(inout self, i: i64) -> inout T { ... }
}
```

The result is a place, not a value: it is used right away (`xs.get_mut(0) +=
1`) or bound to a local borrow, and the first argument counts as borrowed
for as long. Indexing (`xs[i]`) and dereferencing a box (`b.x` for `b:
Box(P)`) are projections of the `Index` and `Deref` traits, which is how
`Vec`, `String`, `HashMap` and `Box` are library types and still read like
built-ins.

### Closures

A closure (`fn(x) { ... }`) borrows what it uses. Its type, `fn(A) -> R`, is
a view: it is passed down and kept in locals, but never stored in an
ordinary struct, so its borrows end where the compiler can see. Calling one costs an indirect call; a
`comptime f: fn(A) -> R` parameter instead compiles one copy of the function
per closure, where the closure is inlined.

Function pointers (`fnptr(A) -> R`) are plain values: named functions and
closures that capture nothing.

### Unsafe code

Raw pointers (`*T`), `extern fn` calls, `asm` and `syscall` are allowed only
inside `unsafe { }`. The standard library builds `Vec`, `String`, `Box` and
`HashMap` this way, and safe code uses them.

### Errors

`Option(T)` and `Result(T, E)` are ordinary enums in the prelude; `e?`
returns early with the `None` or `Err`. A bug stops the program: `panic(msg)`,
a failed bounds check or an integer overflow (when checked) print a message
and trap. There is no unwinding.

### Generics and compile time

As in v0 and Zig, a generic parameter is a compile-time parameter
(`comptime T: type`), and each set of compile-time arguments compiles to its
own instance; type arguments are inferred where they can be. Bounds are
traits (`comptime T: Ord + Hash`), dispatched statically. Generic types are
functions of types: `Vec(i64)`, `Map(String, i64)`.

`const`, `comptime` expressions and compile-time arguments are folded by
sema today (arithmetic, constants, `size_of`). The plan is an interpreter of
the compiler's IR, with the target's memory layout, so that compile-time
code may allocate, use pointers and build containers; only system calls and
C would be refused.

### Integers

`i8`…`i64`, `u8`…`u64`, `f32`, `f64`, `bool`. Sizes and indices are `i64`.
`+ - *` trap on overflow in debug builds and wrap in release builds;
`+% -% *%` always wrap. Division by zero traps. Bounds checks are always on.

## The implementation

```text
source.jh ─► lex/parse ─► AST ─► sema (resolve, check, monomorphize) ─► MIR
                                                                        │
                       ┌─────────────────────────────────────────────── ┤
                       ▼                      ▼                         ▼
                 elab, check            interpreter              LLVM IR text ─► clang ─► program
                 (moves, borrows)       (comptime, planned)
```

- **One crate, one language.** The compiler is a single Rust crate,
  `crates/jihoo` (since ported to jihoo, [Self-hosting](self-hosting.md)). There is no VM profile and no C++ backend: the compiler
  writes LLVM IR as text and `clang` turns it into an object file and links
  it. Freestanding programs are ordinary programs whose standard library
  talks to the kernel with `syscall` instead of calling libc.
- **MIR** is a control-flow graph over *places* (a local, then fields,
  indices and dereferences), close to Rust's MIR: every move, copy, borrow
  and drop is an explicit statement. Sema produces it; three consumers read
  it.
- **The checker is the kernel.** Initialization, moves, exclusivity and the
  scope of borrows are checked on MIR by a small pass that trusts nothing
  sema decided, the way Horn's kernel trusts nothing its engine produced. A
  sema bug becomes a compile error, never a dangling pointer.
- **Codegen is simple on purpose.** Every local is an `alloca`, every field a
  byte offset, every aggregate move a `memcpy`; LLVM's `mem2reg` and `SROA`
  turn that into registers. Aggregates are passed by pointer (with
  `noalias` and `readonly` where the conventions allow it) and returned
  through `sret`. Layout is computed once, by the compiler, and the
  interpreter uses the same one.

### Written to be ported

The Rust code follows rules that make a line-by-line port to jihoo possible:

- References only as function parameters, never in structs: data lives in
  vectors and refers to other data by index (`TypeId`, `LocalId`,
  `BlockId`), which is also what jihoo programs do.
- Enums and `match`, `Vec`, `HashMap` and `String`; no trait objects, no
  iterator chains that need lifetimes, no macros beyond `derive`.
- The standard library the compiler needs (`Vec`, `String`, `HashMap`,
  files, processes, formatting) is the first thing the jihoo standard
  library provides.

## Removed

The hosted profile and the VM's GC, `ref`, `cell`, `chan`, `go`, `select`
(threads and channels become library code), the ownership inference pass,
`nocopy`, `--cost`, rewrite rules, contracts, macros and `quote`, and JIR as
a text contract between two languages. Some of these may come back on the
new foundation (contracts and macros are the likeliest); none is needed to
write the compiler.

## Plan

1. Core: lexer, parser, sema for numbers, structs, enums, `match`,
   functions, loops, pointers and arrays; MIR; LLVM text; the driver. Done.
2. Ownership: moves, `Drop`, drop flags, `inout`, local borrows, the
   checker; `Box`, `Vec`, `String` in the library. Done.
3. Traits and methods, projections, indexing and `deref`, closures, slices
   and `str`, `for` over iterators, `?`. Done; `derive` is left.
4. The interpreter: `const`, `comptime`, value parameters. Left.
5. The library: `Map`, files, arguments, atomics; freestanding programs.
   Done, and processes; formatting and threads are left.
6. Documentation, the website, examples; remove v0. Done.

## Measurements

Each program run three times, best time, on x86_64; jihoo with
`--release -O2` (bounds checks on), C with `clang -O2`:

| program | jihoo | C |
|---------|-------|---|
| `fib(40)`, recursive | 0.31 s | 0.30 s |
| sieve of Eratosthenes to 50 million | 0.47 s | 0.47 s |
| 1000 × 1000 matrix product | 0.33 s | 0.32 s |
| n-body, 5 bodies, 5 million steps | 0.30 s | 0.31 s |
