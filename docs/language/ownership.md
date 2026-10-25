# Values and ownership

Every value has exactly one owner: a variable, a field, an element of a
collection. When the owner goes away, so does the value, and anything it
owns is freed. There is no garbage collector and no reference counting.

## Plain values copy, the others move

A type is *plain* when it owns nothing and has no destructor: numbers,
`bool`, pointers, and structs, tuples, enums and arrays made only of plain
types. Plain values copy, as in C.

Other values move. Assigning one, passing it to a `sink` parameter or
returning it hands it over, and the old variable cannot be used until it is
given a new value:

```jihoo
let a = String.from("text")
let b = a              // moves: `a` is empty now
println(a)             // error: `a` is used here after it was moved away
```

Copies of values that own memory are written out with `.clone()`, so a copy
is never a surprise:

```jihoo
let c = b.clone()
```

`move x` moves explicitly where a borrow would otherwise be taken
(`match move x { ... }`).

## Destruction

When a variable goes out of scope, its value's destructor runs: the
`Drop` impl of its type if it has one, then the destructors of its parts.
Values are destroyed in the reverse of the order they were made.

```jihoo
struct File {
    fd: i32
}

impl Drop for File {
    fn drop(inout self) {
        sys.close(self.fd)
    }
}
```

A value moved away on some paths and not others is destroyed only where it
is still there; the compiler keeps a flag for it. `forget(x)` gives up a
value without running its destructor, and `drop(x)` destroys it early.

## `let` and `var`

`var` declares a variable that can change. `let` declares one that cannot,
and what it means depends on the value:

- `let x = <new value>` owns it (a call's result, a literal, a struct
  literal).
- `let x = <place>`, where the place is a variable, field or element that is
  not plain, *borrows* it for as long as `x` is used: nothing is copied or
  moved, and the place cannot change meanwhile.
- `var x = <place>` moves the value out of the place (or copies it, if
  plain).

```jihoo
let name = person.name         // a borrow of the field
var mine = person.name.clone() // a copy, which can change
```

## Moving out of places

A whole variable can be moved; a field, an element, or anything reached
through a borrow cannot be moved out, because its owner would be left
broken. (A part of a new value can: in `pair().1` nothing else owns the
pair, so its other parts are dropped there, unless its type has a `Drop`
impl.) Take it with `mem.replace` or `mem.take`, which leave something in
its place, or `.clone()` it:

```jihoo
import std.mem

let old = mem.replace(&v[0], String.new())
```

Destructuring a value that the code owns moves its parts out:

```jihoo
match parse(text) {                 // a new value: owned
    Ok(tree) => use(tree)           // `tree` moves out
    Err(msg) => println(msg)
}
```

So does a `match` on a whole variable that owns its value, when the arms
bind its parts: the variable is used up by the `match`, whichever arm runs.
On a field or an element, `match` borrows the parts instead.

## Integer overflow, bounds and other bugs

Bugs stop the program at once with a message on standard error: an index
out of bounds, a division by zero, an integer overflow (in debug builds),
`unwrap` of `None`, `panic(...)`. There is no unwinding; destructors do not
run.
