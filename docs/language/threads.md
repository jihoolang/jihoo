# Threads

`std.thread` runs work on several threads. Parallel calls wait for their
workers, and scope bodies join their workers before releasing local values,
so the work can borrow what the caller owns. No value needs copying,
`'static`, a reference count or a lock to reach another thread:

```jihoo
import std.thread

fn main() {
    let words = load_words()              // a Vec(String)
    let lengths = thread.map(words.as_slice(), fn(w) { w.len() })
    let (a, b) = thread.join(fn() { count(words, "a") }, fn() { count(words, "b") })
}
```

| function | |
|----------|---|
| `join(a, b)` | runs `a` on a new thread and `b` on this one; returns `(a(), b())` |
| `each(lo, hi, f)` | calls `f(i)` for each `i` in `lo..hi`, spread over the processors |
| `map(xs, f)` | `f` of each element of the slice `xs`, as a `Vec`, in order |
| `each_mut(&v, f)` | calls `f` on each element of the `Vec` `v`, which `f` may change |
| `scope(f)` | lends a scope to `f`; joins all its threads before returning `f`'s owned result |
| `cpu_count()` | the number of processors online |

`each`, `map` and `each_mut` halve their range until there is a part per
processor, and run the halves with `join`.

## Scoped threads

`scope` lets a body start several threads, keep working, and collect their
results. `s.spawn(fn() { ... })` starts a thread immediately and returns a
`ScopedJoinHandle(T)`. Its `join()` waits and consumes the handle, returning
the closure's result:

```jihoo
var left = Vec(i64).new()
var right = Vec(i64).new()
let answer = thread.scope(fn(s) {
    let a = s.spawn(fn() { left.push(20); String.from("ready") })
    s.spawn(fn() { right.push(22) })
    println(a.join())
    42
})
println(left[0] + right[0])   // 42: both workers have finished
```

The scope joins **every** worker, including those whose handles are ignored,
dropped or passed to `forget`. It drops unused results exactly once, before
the body's local values go away. This also happens on `return` and `?`.
As with other threads, a panic stops the program.

Each spawn moves a fresh tuple of captured borrows into its own heap job.
This keeps the closure's environment alive independently of the statement
that starts it. A loop can start any number of jobs borrowing values that
outlive the loop:

```jihoo
let hits = sync.Atomic(i64).new(0)
thread.scope(fn(s) {
    for _ in 0..8 {
        s.spawn(fn() { hits.add(1) });
    }
})
println(hits.load())   // 8
```

The semicolon discards the last handle: without it, a body's last expression
is its return value, and a handle cannot leave the scope. The body can
return an owned result such as an integer, `String` or `Vec(i64)`; a result
that is a view currently retains the scope's borrow and cannot leave it.

Each worker may change what it alone captures. Its captured borrows remain
active until the scope body's end, even after `join()` or `forget(handle)`.
Other workers and the body cannot read or change a mutably captured value
in that time. A local in a shorter inner block, or a loop variable, cannot
be borrowed by a worker that lasts until the body's end. Use an inner
`thread.scope` when work must finish before leaving such a block.

Write the worker closure at the spawn call. An existing borrowed closure,
or a capture containing one, is rejected: it could also be called on this
thread while the worker changes its captures. Owning `dyn fn` values and
ordinary functions can be called from a worker.

A worker also cannot capture a mutable or interior value that itself holds
borrows, such as a mutable `Vec(str)` or a `Channel(str)`: it could store a
borrow of a scope local where it would survive the scope. Use owned elements
(`Vec(String)`, `Channel(String)`) in containers that workers change. Shared
read-only views, such as `str` and slices of owned values, can be captured.

Helpers can accept `inout s: thread.Scope` and call `s.spawn(...)`. The
compiler joins the jobs that helper started before releasing its locals;
the caller's earlier jobs and handles remain in the outer scope. To use a
scope stored in a struct or captured by another callback, pass it to such
a helper first. Only a direct `inout Scope` parameter, or its local
reborrows, may be used to spawn. Scopes can also be nested normally.

## Why there are no data races

A data race needs two threads to use the same memory while one of them
changes it. Two rules prevent it:

- **`join`'s two closures are two arguments of one call.** The borrow
  rules already keep the arguments of a call from changing what the other
  uses ([borrowing](borrowing.md)). Each closure may change what it alone
  captures:

  ```jihoo
  var left = Vec(i64).new()
  var right = Vec(i64).new()
  thread.join(fn() { left.push(1) }, fn() { right.push(2) })   // fine
  thread.join(fn() { left.push(1) }, fn() { left.push(2) })
  // error: `left` is used here while it is borrowed mutably
  ```

- **A closure that `each`, `map` or `each_mut` call on several threads at
  once cannot change what it captures.** These functions take it as a
  `comptime` parameter and check it with `captures_mut(f)` (see below). A
  closure borrows every `var` it uses mutably, even one it only reads, so
  borrow with `let` first:

  ```jihoo
  var grid = make_grid()
  thread.each(0, n, fn(i) { use(grid, i) })
  // error: the closure cannot capture a `var` or a closure; borrow with `let` first
  let g = grid                    // a borrow of `grid`, for the rest of the block
  thread.each(0, n, fn(i) { use(g, i) })
  ```

  It also may not capture another closure, which might change what that
  closure captures.

Outside `unsafe`, safe jihoo has no shared mutable state: no globals, no
reference counts, and no cells except the `#[interior]` types of
`std.sync`, which are built to be changed by several threads. So what a
closure can only read cannot change on another thread. Values move between
threads as the results of `join` and `map`, and through
[channels](#channels).

A panic on any thread stops the whole program, as it does on one thread.

## Sharing changes: `Atomic` and `Mutex`

`std.sync` has two types that threads change together. They change behind
shared borrows (they are `#[interior]`, see
[unsafe code](unsafe.md#changing-behind-a-shared-borrow)),
so a closure that runs on several threads may capture them with `let`:

```jihoo
import std.sync

let hits = sync.Atomic(i64).new(0)
let seen = sync.Mutex(Vec(i64)).new(Vec(i64).new())
thread.each(0, n, fn(i) {
    hits.add(1)
    if i % 7 == 0 {
        seen.lock(fn(v) { v.push(i) })
    }
})
println(hits.load())
let all = seen.into_inner()
```

`Atomic(T)` holds an integer: `load`, `store`, `add`, `sub`, `swap` and
`compare_swap`, all sequentially consistent. `Mutex(T)` holds any value.
`m.lock(f)` waits until no other thread holds it, then calls `f` with the
value lent mutably, and returns what `f` returns. Since the value is lent
only for the call, nothing can keep a part of it after the lock is
released, and there is no guard to forget. Locking the same mutex again
inside `f` waits forever. Waiting uses Linux futexes, so it costs nothing
while no one else holds the lock.

## Channels

`sync.Channel(T)` is a queue that threads pass values through. Like
`Mutex`, it is shared with `let`, so any number of threads may send and
receive at once:

```jihoo
let ch = sync.Channel(i64).new()
let (sum, _) = thread.join(fn() {
    var total = 0
    for v in ch.iter() {      // until the channel is closed and empty
        total += v
    }
    total
}, fn() {
    thread.each(0, 1000, fn(i) { ch.send(i) })
    ch.close()
})
```

| method | |
|--------|---|
| `Channel(T).new()` | a channel without a limit: `send` never waits |
| `Channel(T).bounded(n)` | at most `n` values wait in it; `send` waits while it is full |
| `send(v)` | puts `v` at the end; on a closed channel, stops the program |
| `recv()` | the value at the front, waiting for one; `None` once closed and empty |
| `try_recv()` | the value at the front, or `None` without waiting |
| `close()` | no more values will be sent; receivers get the rest, then `None` |
| `iter()` | `for v in ch.iter()` receives until `recv` gives `None` |
| `len()`, `is_closed()` | as they are now |

Each value goes to one receiver, in the order sent. A value sent moves
into the channel; what is never received is dropped with it. Since the
channel itself is borrowed, it must outlive the threads that use it, which
every channel in a `join` or `each` does.

## Once-cells

`sync.Once(T)` holds a value that the first thread to ask for it sets.
`get_or_init(f)` calls `f` if no thread has, while threads asking at the
same time wait for it, and returns the value borrowed. `get()` gives it if
it is set, and `into_inner()` takes it back:

```jihoo
let table = sync.Once(Vec(i64)).new()
thread.each(0, n, fn(i) {
    let t = table.get_or_init(fn() { build_table() })   // built once
    use(t, i)
})
```

Asking the same `Once` inside its own `f` waits forever.

## Profiles

Native programs use POSIX threads from libc.
[Freestanding programs](profiles.md) start threads with the `clone` system call, each on
a stack of its own (8 MiB of address space, used as touched, with a guard
page), and wait for them with a futex that the kernel clears when the
thread ends. The freestanding allocator takes a lock, so every thread can
allocate. `cpu_count()` counts the processors the process may run on.

## Checks that libraries write

`captures_mut(f)` and `compile_error(msg)` let a library check its
compile-time arguments, as `std.thread` does:

| builtin | |
|---------|---|
| `captures_mut(f)` | for a `comptime` closure parameter `f`: whether it captures a variable mutably, or captures a closure |
| `compile_error("...")` | an error at this point of this instance; with [`inline if`](reflection.md#inline-for-and-inline-if), a check |

```jihoo
pub fn each(lo: i64, hi: i64, comptime f: fn(i64)) {
    inline if captures_mut(f) {
        compile_error("the closure cannot capture a `var` or a closure")
    }
    ...
}
```

The error points at `compile_error`. Its notes show each generic instance
on the way to it and where that instance was used, ending in the caller's
code.
