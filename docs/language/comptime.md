# Compile-time evaluation

`const` initializers, explicit `comptime` expressions, array lengths and
integer or boolean compile-time arguments can call ordinary jihoo functions.
The compiler checks and lowers the expression to MIR, runs it in a separate
interpreter, and puts the resulting constant into the program. LLVM and the
runtime do not need to execute that expression.

```jihoo
fn factorial(n: i64) -> i64 {
    var result = 1
    for i in 1..n + 1 {
        result *= i
    }
    result
}

const LIMIT = factorial(4)

fn main() {
    let answer = comptime factorial(6)    // 720, calculated while compiling
    let table: [i64; LIMIT] = [0; LIMIT]  // 24 elements
    println(answer)
    println(table.len)
}
```

The function needs no annotation. It can also be called with runtime values
in ordinary code. `comptime` applies to the following unary expression;
use a block or parentheses for a larger calculation:

```jihoo
let answer = comptime {
    var n = 6
    n += 1
    n * 6
}
let total = comptime (factorial(3) + factorial(4))
```

## What the interpreter runs

Function calls, recursion, generic instances, methods, closures and function
pointer calls use the same MIR as runtime code. Locals, assignments,
`inout` arguments, conditionals, `match`, `while`, `loop`, `for`, `break`,
`continue` and function returns work during evaluation. Boolean operators
short circuit. Arrays, tuples, structs and enums use the selected target's
layout; slices and borrows can be used inside the calculation.

Results can be integers (including `i128` and `u128`), floats, booleans,
strings, slices, unit, or aggregates containing only values without
addresses or destructors. Aggregate results become static bytes; string
results become static string literals. For example:

```jihoo
fn squares() -> [i64; 4] {
    var values = [0; 4]
    for i in 0..4 {
        values[i] = i * i
    }
    values
}

const TABLE = squares()
```

## The heap

`Vec`, `String`, `Map`, `Box` and anything else built on the standard
allocator work during evaluation, in both [profiles](profiles.md). The
interpreter gives each allocation its own memory, so a use after it is freed
or a double free is a compile error, not undefined behavior. Destructors
run where they would at run time, user `Drop` impls included.

A result that owns heap memory cannot keep it: the program's copy is static
data, which nothing may change or free. So a `String` result becomes a
`str` constant, and a `Vec(T)` result a `[T]` constant over static bytes,
when `T` itself has no addresses or destructors:

```jihoo
fn describe(comptime T: type) -> String {
    var s = String.from("fields:")
    inline for i in 0..field_count(T) {
        s.push(' ')
        s.push_str(field_name(T, i))
    }
    s
}

fn primes(n: i64) -> Vec(i64) { ... }

const FIELDS: str = describe(Point)   // "fields: x y"
const PRIMES = primes(10)             // a [i64] of 10 elements

fn main() {
    let greeting = comptime String.from("hi")   // a str
    for p in PRIMES { println(p) }
}
```

Other owning results, such as a `Map`, a `Box` or a `Vec(String)`, are
errors: reduce them to such a value inside the calculation. What the
calculation leaks is discarded with the interpreter's memory.

## Checking literal arguments

A function can have a literal argument checked where it is called:

```jihoo
#[literal_check(pattern, check_pattern)]
pub fn format(comptime T: type, pattern: str, values: T) -> String { ... }

// What is wrong with `pattern` for values of type `T`, or "".
pub fn check_pattern(comptime T: type, pattern: str) -> String { ... }
```

When the argument for `pattern` is a string literal, the compiler calls
the checking function, from the same module, with the call's compile-time
arguments and the literal, and runs it in the interpreter. A message it
returns is a compile error at the literal. Other arguments, known only when
the program runs, are not checked. [`std.fmt`](../reference/standard-library.md#formatting)
checks its patterns this way.

The checks run after the rest of the program is lowered, once per checking
instance and literal, and the functions only they need are left out of the
program: a call that passes its check compiles to the same code as without
one.

## What it sees

A compile-time expression sees module constants and its enclosing function's
compile-time parameters. It cannot read that function's runtime locals,
even when their initializers happen to be literals. Declare reusable values
as module `const` items or calculate them inside a `comptime` block.

## Checks and limits

The interpreter executes snapshots after initialization analysis and borrow
checking. These checks still apply when `JIHOO_NO_ELAB` is used to inspect
the surrounding program's unelaborated MIR. Division by zero, checked
integer overflow, failed bounds checks, traps, invalid memory accesses and
cyclic evaluation produce compile errors. `+%`, `-%` and `*%` wrap; function
arithmetic follows the build's overflow mode, including `--release`.

Each interpreter invocation permits 1,000,000 execution and validation
steps, 128 active calls, and 64 MiB of cumulative simulated allocation.
Nested evaluation dependencies are also bounded. These limits stop
nonterminating calculations without hanging the compiler.

Interpreter failures include the current resource consumption, the source
obligation and up to eight compile-time call notes. Use
[`--comptime-report PATH`](../reference/command-line.md#compile-time-resource-reports)
to measure successful and failed invocations, including exclusive per-function
steps and allocation costs. This leaves both the limits and program output
unchanged. Allocations are cumulative simulated storage, not peak compiler
process memory.

Current limitations:

- External functions, system calls, inline assembly, atomics, program
  arguments and statics are unavailable during evaluation. This includes
  file and network I/O. The standard allocator is the exception: the
  interpreter provides it (see [the heap](#the-heap)).
- Pointer, borrow, closure and function pointer results cannot leave the
  interpreter. Nonzero pointers cannot be converted to integers or read
  through a scalar byte reinterpretation. A returned string or slice must
  refer to live memory, which the compiler copies; its elements must not
  contain addresses.
- Float arithmetic and numeric casts work; the math and atomic intrinsics
  are not implemented in the interpreter. `mem_copy` and `mem_fill` work
  on interpreter memory.

This feature is implemented in the compiler written in jihoo
(`compiler/interp.jh`). The frozen Rust bootstrap compiler builds that
compiler but does not provide the new evaluator itself. Build stage 1 or
use the installed compiler to compile programs using this feature.
