# Errors

## Expected failures: `Option` and `Result`

Failures a program handles are values: `Option(T)` (`Some(x)` or `None`)
and `Result(T, E)` (`Ok(x)` or `Err(e)`), ordinary enums from the prelude.

```jihoo
fn parse(s: str) -> Result(i64, String) {
    match s.parse_int() {
        Some(n) => Ok(n)
        None => Err("not a number: " + s)
    }
}
```

`e?` gives the value inside an `Ok` or `Some`, and returns the `Err` or
`None` from the function otherwise. The function must return the same kind,
with the same error type.

```jihoo
fn sum(a: str, b: str) -> Result(i64, String) {
    Ok(parse(a)? + parse(b)?)
}
```

`unwrap`, `expect(msg)`, `unwrap_or(x)`, `is_some`, `is_ok`, `ok` and the
like are methods ([Standard library](../reference/standard-library.md)).

## Bugs: stopping the program

A bug stops the program right away, with a message on standard error:

- `panic(msg)`, and `assert(cond, msg)` when `cond` is false;
- an index out of bounds (always checked);
- a division by zero;
- an integer overflow, in debug builds;
- `unwrap` of `None` or `Err`.

There is no unwinding and no catching: the process ends (by a trap, so a
debugger stops right there). Functions that never return have the result
type `never`.

## Panic handlers

A program can replace the way it reports these with a function of its own,
marked `#[panic_handler]`:

```jihoo
import std.sys

#[panic_handler]
fn on_panic(msg: str) -> never {
    println("stopped: " + msg)
    sys.exit(70)
}
```

Every failure listed above then calls it with its message (`index out of
bounds`, `integer overflow`, `unwrap of None`, the text given to `panic`),
instead of writing `panic: ` and the message to standard error and
trapping. The handler is a free function written `fn(msg: str) -> never`:
not generic, `extern`, `export` or `unsafe`, and a program (with all of its
modules) has at most one. It must not return, and a panic inside it calls it
again. Since nothing unwinds, it is where a program reports a bug its own
way and stops, for example through the system calls of an operating system
that is not Linux ([embedding](profiles.md#embedding-in-another-system)).
