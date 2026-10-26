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
strings, unit, or aggregates containing only values without addresses or
destructors. Aggregate results become static bytes; string results become
static string literals. For example:

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

Current limitations:

- External functions, system calls, inline assembly, atomics, program
  arguments and statics are unavailable during evaluation. This includes
  file and network I/O and the standard library's allocator.
- Values with destructors cannot be dropped by the interpreter yet;
  `Vec`, `String` and `Box` allocation is therefore unavailable. Fixed
  arrays and string literals work.
- Pointer, borrow, slice, closure and function pointer results cannot leave
  the interpreter. Nonzero pointers cannot be converted to integers or
  read through a scalar byte reinterpretation. A returned string must
  refer to live constant bytes, which the compiler copies.
- Float arithmetic and numeric casts work; the math and atomic intrinsics
  are not implemented in the interpreter. `mem_copy` and `mem_fill` work
  on interpreter memory.

This feature is implemented in the compiler written in jihoo
(`compiler/interp.jh`). The frozen Rust bootstrap compiler builds that
compiler but does not provide the new evaluator itself. Build stage 1 or
use the installed compiler to compile programs using this feature.
