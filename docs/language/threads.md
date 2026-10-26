# Threads

`std.thread` runs work on several threads. Every thread it starts ends
before the function that started it returns, so the work can borrow what
the caller owns. No value needs copying, `'static`, a reference count or a
lock to reach another thread:

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
| `cpu_count()` | the number of processors online |

`each`, `map` and `each_mut` halve their range until there is a part per
processor, and run the halves with `join`.

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

Safe jihoo has no shared mutable state: no globals outside `unsafe`, no
reference counts and no cells. So what a closure can only read cannot
change on another thread. Values move between threads only as the results
of `join` and `map`.

A panic on any thread stops the whole program, as it does on one thread.

## Profiles

Native programs use POSIX threads from libc. In
[freestanding programs](profiles.md) the same functions run each part on
the calling thread, one after another, because the freestanding allocator
cannot be used from several threads yet. The rules above make the results
the same: running the parts in order is one of the schedules the native
version may choose.

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

## Not yet

- Threads that outlive a call (a `scope` you spawn into), channels and
  mutexes.
- Atomic values that safe code can share. They need a way to mark
  memory that changes behind a shared borrow, because the compiler tells
  LLVM that shared borrows are read-only.
- Threads in freestanding programs.
