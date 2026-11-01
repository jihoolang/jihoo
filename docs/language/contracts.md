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
the proof covers (the bounds check of `xs[i]` above) is removed.
[`jihoo verify`](../reference/command-line.md#verification) proves them
and lists those that are not proved, and `--verify` removes the proved
checks from a build. **For now an unproved contract is not an error**,
and a build without `--verify` is the same with or without contracts.

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
term   = integer | place | place ".len" "(" ")" | "old" "(" place ")"
       | "old" "(" place ".len" "(" ")" ")"
       | term ( "+" | "-" ) term | term "*" term | "-" term | "(" term ")"
place  = ( name | "result" ) { "." field }
```

- The names are integer parameters and variables, their integer fields
  (`self.len`, `p.pos.line`, through a borrowed parameter too), and `.len`
  of a slice or `str`, including one in a field. A field is named only
  where the code could name it: `Vec`'s `len` field is private to `std`.
- `x.len()` is what the `len` method of `x`'s type says it returns, with
  an `ensures result == ...` over `self`: `v.len()` for a `Vec` is
  `v.len`, and `s.len()` for a `String` is its bytes' length.
- One side of `*` must be a constant: the verifier's arithmetic is linear.
- **The arithmetic is exact.** `x + 1 <= hi` in a clause cannot overflow,
  and integers of different types compare by value: `i <= xs.len` holds
  for `i: u64`.
- Other calls, `||` and `!` are not part of clauses yet.

## How a call is proved

Proofs are modular: a call proves the callee's `requires` with the
arguments for its parameters, then assumes its `ensures`. A local lent to
an `inout` parameter (`bump(&y)`) has a new value after the call, about
which the callee's `ensures` says what it says, and nothing more; so do the
fields of a value lent that way (`v.push(x)` lends `v`), and the fields of
a result:

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

```jihoo
struct Counter {
    n: i64
}

impl Counter {
    fn bump(inout self)
        requires self.n < 100
        ensures self.n == old(self.n) + 1
    {
        self.n += 1
    }
}

fn twice(inout c: Counter)
    requires 0 <= c.n && c.n < 50
    ensures c.n == old(c.n) + 2
{
    c.bump()
    c.bump()
}
```

A recursive call assumes the `ensures` being proved, so a proof says what
holds *if* the function returns.

## Panics a call rules out

`requires` is the caller's duty, so a function that checks its arguments
itself and panics, as `Vec.index` does, states none: most of its calls
could not prove one. Instead, a call to a small function that may panic
is a check at the call: the callee's paths to its panic, over its
parameters, must be impossible with what the caller knows. In

```jihoo
fn sum(v: Vec(i64)) -> i64 {
    var s = 0
    var i = 0
    while i < v.len() {
        s += v[i]
        i += 1
    }
    s
}
```

`v.len()`'s `ensures` relates its result to `v`'s length (`std` states
its contracts once the compiler that builds it, the seed, reads fields in
clauses), and `v[i]` cannot reach `Vec.index`'s panic: with `--verify` the call goes to a copy
of `Vec.index` without the check, and a call that cannot rule it out keeps
it. A panic that the function rules out itself, as after
`if x == x + 1 { panic(...) }`, is removed from it.

See [Grammar](../reference/grammar.md#files) for where clauses go.
