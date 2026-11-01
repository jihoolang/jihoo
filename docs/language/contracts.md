# Contracts

A function can say what it needs from its callers and what it promises
them, and a loop what holds each time it starts over:

```jihoo
fn clamp(x: i64, lo: i64, hi: i64) -> i64
    requires lo <= hi
    ensures lo <= result && result <= hi
{
    if x < lo { return lo }
    if x > hi { return hi }
    x
}

fn bump(inout n: i64)
    requires n < 100
    ensures n == old(n) + 1
{
    n += 1
}

fn sum(xs: [i64]) -> i64 {
    var s = 0
    var i = 0
    while i < xs.len
        invariant 0 <= i && i <= xs.len
    {
        s += xs[i]
        i += 1
    }
    s
}
```

Contracts are for [verification](../internals/verification.md): they are
proved while compiling, never checked while the program runs, and a check
the proof covers (the bounds check of `xs[i]` above) is removed. **For now
the compiler only reads them**: it checks that each clause is well formed and
gives the clauses to the verifier through
[`emit-obligations`](../reference/command-line.md#verification-model), and
[jihoo-proofs](https://github.com/jihoolang/jihoo-proofs/tree/main/obligations)
proves them. A build is the same with or without them.

## Clauses

`requires` and `ensures` go between a function's signature and its body,
`invariant` between a loop's head and its body, as many as needed. The
words are special only there: elsewhere `requires`, `result` and `old` are
ordinary names.

- **`requires`** is the caller's duty. Each call must meet it, so a
  function with `requires` cannot be used as a value (a `fnptr` or a
  closure), whose calls would not.
- **`ensures`** is the function's duty, at every `return`. `result` is the
  value returned. A parameter is its value on entry, even a `sink`
  parameter the body assigns, except an `inout` parameter, which is its
  value on return; `old(x)` is an `inout` parameter's value on entry.
- **`invariant`** holds each time the loop reaches its head (before
  `while` tests its condition, before a range `for` takes its next value,
  at the top of a `loop`): on entry and after every iteration. It names
  the variables declared before the loop, and `old(x)`.

A function without a body (`extern fn`) cannot have a contract: nothing
could prove it.

## What a clause says

A clause compares integers, or joins comparisons with `&&`:

```text
clause = term cmp term { "&&" term cmp term }
cmp    = "<" | "<=" | ">" | ">=" | "==" | "!="
term   = integer | name | "result" | "old" "(" name ")" | name ".len"
       | term ( "+" | "-" ) term | term "*" term | "-" term | "(" term ")"
```

- The names are integer parameters and variables, and `.len` of a slice or
  `str`.
- One side of `*` must be a constant: the verifier's arithmetic is linear.
- **The arithmetic is exact.** `x + 1 <= hi` in a clause cannot overflow,
  and integers of different types compare by value: `i <= xs.len` holds
  for `i: u64`.
- Calls, fields, `||` and `!` are not part of clauses yet.

## How a call is proved

Proofs are modular: a call proves the callee's `requires` with the
arguments for its parameters, then assumes its `ensures`. A local lent to
an `inout` parameter (`bump(&y)`) has a new value after the call, about
which the callee's `ensures` says what it says, and nothing more:

```jihoo
fn after_bump(n: i64) -> i64
    requires 0 <= n && n <= 10
    ensures result == n + 1
{
    var x = n
    bump(&x)
    x
}
```

A recursive call assumes the `ensures` being proved, so a proof says what
holds *if* the function returns.

See [Grammar](../reference/grammar.md#files) for where clauses go.
