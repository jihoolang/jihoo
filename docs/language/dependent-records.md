# Parameterized dependent records

In a `#![dependent_core]` module, a struct can have erased `u64` parameters.
This keeps an owned value's index in its type:

```jihoo
#![dependent_core]

struct Sized(n: u64) { data: buffer(n) }

fn make(n: u64, value: i64) -> Sized(n) {
    Sized { data: alloc(n, value) }
}

fn first(n: erased(u64), s: ref Sized(n), p: erased(Lt(0, n))) -> i64 {
    let Sized { data } = s
    index(data, 0, p)
}

fn main() -> i64 {
    let s = make(3, 17)
    first(3, s, decide_lt(0, 3))
}
```

This returns 17. `first` borrows the record and its buffer. The caller still
owns `s`, which is freed when the scope ends. The struct parameter introduces
no runtime field. A separate runtime argument such as `make`'s `n` is still
needed to allocate a buffer dynamically.

Construction gets all parameters from the expected type: a return type, an
annotated binding such as `let s: Sized(n) = Sized { ... }`, or a field's type.
Without an expected type, the constructor is rejected; parameters are not
inferred from the fields. Struct literals use `Sized { ... }`, not an explicit
index application. Imported records use `module.Sized(n)` in types and
`module.Sized { ... }` in literals and patterns.

Fields may refer to parameters and earlier fields. For example, a record with
parameters `n: u64, m: u64` can declare, in order, `len: u64`,
`data: buffer(len)`, `fixed: buffer(n)`, and `same: erased(Eq(len, m))`.
Construction checks each field at its substituted type, even when the literal
lists fields in a different order. Matching binds only fields; it does not
bind the erased parameters again. Evidence fields remain erased.

A plain `let` can destructure a record: `let Sized { data } = value`. The
initializer is evaluated once, and the rest of the block sees the fields in
declaration order, with their dependent types and evidence. Renaming uses
`data: bytes`; `_` discards one field and `..` omits the remaining fields.
Duplicate binding names are rejected. A contextual constructor can have an
explicit annotation, for example
`let Sized { data }: Sized(n) = Sized { data: alloc(n, 0) }`. The annotation
and initializer are checked even if all fields are discarded.

This is a single-case elimination, like the corresponding `match`. An owned
record is consumed; destructuring a `ref` parameter borrows its owned fields.
Owned fields extracted this way can be passed to `inout` operations, just as
owned match-arm fields can. Omitted owned fields are cleaned up by the existing
case ownership rules. Nested records can be unpacked in one pattern, or with successive lets:

```jihoo
struct Outer(n: u64) { inner: Sized(n), extra: buffer(n) }

fn release(n: erased(u64), value: Outer(n)) -> i64 {
    let Outer { inner: Sized { data }, extra: _ } = value
    free(data, 0)
}
```

A nested record pattern is checked at the field's actual type. Erased indices,
evidence and borrowed fields retain the same meaning as successive record
lets. Every named binding in the complete pattern must be distinct; `_` may
appear more than once. Each record's fields enter scope in declaration order,
then its nested patterns are unpacked in the order written. The initializer
runs once, even when every nested field is discarded. Omitted owned fields
are freed, and private fields remain inaccessible at every level.

Match arms also accept nested irrefutable record patterns, including inside
enum payloads: `Delivery.Present(Envelope { inner: Sized { data }, .. })`.
The outer match must still cover each variant exactly once. Record subpatterns
are unpacked only inside the selected arm; their field types and evidence come
from that arm's constructor telescope. In a record match, sibling subpatterns
are unpacked in declaration order, even if fields were written out of order.
All named bindings in one arm must be distinct, including bindings at different
nesting levels. This also rejects duplicate names in flat match arms.
Borrowing, private fields, dropped fields and inout reconstruction behave as
with explicit nested matches. Nested enum variants, literals and other refutable
subpatterns remain unsupported; use a separate match for those cases.

This form supports struct patterns with names, wildcards and nested struct
patterns. `var` destructuring, refutable enum patterns and `let ... else` are
not supported in this subset. Bind an inout call's result to a name before
unpacking it. Borrowed fields cannot escape their borrow or be consumed as
owners, and field-dependent results retain the existing match restrictions.

The existing ownership and visibility rules apply: owned matches consume the
record, borrowed matches lend its owned fields, and `inout` functions can
reconstruct a record at the same indexed type. A field omitted with `..` is
handled by the existing ownership rules. Private fields cannot be constructed
or named in a pattern outside their defining module. A field cannot reuse a
parameter's name.

Parameters are uniformly erased `u64` values, not type parameters or arbitrary
index refinements. Invariants and declaration attributes remain unsupported.
The compiler elaborates these declarations into the existing core family and
constructor representation; this feature adds no kernel rule or new formal
soundness claim.
