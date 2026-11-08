# Bulk vector extension

`dependent.vec_bulk.extend(&v, n, source)` appends a borrowed `buffer(n)` to an existing
vector and returns erased evidence:

`Eq(vec.len(v), vec.len(old(v)) + n)`

Import `dependent.vec_bulk` for this opt-in operation over the existing
`dependent.vec.Vec` representation. Keeping bulk operations separate avoids
adding their elaboration cost to unrelated vector consumers.

This is a typed mutation postcondition. It describes the vector after the call
relative to its previous state, allowing a caller to derive bounds for later
reads without rediscovering the length.

## Composing mutation evidence

```jihoo
#![dependent_core]
import dependent.vec
import dependent.vec_bulk
import dependent.nat

fn main() -> i64 {
    var v = vec.with_capacity(4)
    let empty = vec.clear(&v)
    let source = alloc(3, 17)
    let grown = vec_bulk.extend(&v, 3, source)
    let three = transport(fn(k) { Eq(vec.len(v), k + 3) }, empty, grown)
    vec.get(v, 2,
        nat.rewrite_upper(2, 3, vec.len(v), nat.eq_sym(vec.len(v), 3, three), decide_lt(2, 3)))
}
```

This returns `17`. The earlier equality from `clear` refers to the old state;
transporting the extension's postcondition through it proves the new length is
three. An old bound or equality cannot simply be reused as if it described the
new vector, even though extension happens to preserve previous indices.

The [complete example](../../examples/core_vec_extend.jh) materializes a checked
list as the first source buffer, performs two bulk extensions, composes their
postconditions and reads the final element using the resulting evidence.
It connects imported structural list materialization to mutation; direct list
extension is not part of this API.

## Capacity and ownership

The source remains borrowed. Its elements are copied in order after the vector's
existing prefix; later vector mutation does not change the source. The vector
owns its destination buffer independently and remains valid after the source is
released. Passing a borrowed vector as `&v` is rejected.

- If the combined length fits the existing capacity, extension writes directly
  into that buffer. It does not copy the prefix or allocate another buffer.
- Otherwise, it allocates exactly the combined length, copies the old prefix
  once, appends the source and frees the old buffer. The new capacity equals the
  new length.
- An empty extension preserves elements, length and capacity. The current
  lowering may still replace the vector record.

The loop carries one destination owner, and every source read and destination
write has checked bounds evidence. The caller supplies the source's runtime
length `n`, which must agree with its `buffer(n)` type. No type parameter or
unchecked copying primitive is introduced.

## Costs and limits

With enough capacity the copying work is linear in the source length. Growth
adds a linear copy of the old prefix. Repeated small extensions without reserved
capacity may repeatedly copy that prefix; this API makes no amortized growth
promise. Reserve a suitable capacity up front when the total is known, or use
individual `push` operations for their existing geometric growth policy.

At O0, the current implementation replaces the vector record on each extension:
one small allocation even when buffer capacity suffices, plus one buffer
allocation on growth. Tests state these actual costs; reusing capacity is not a
claim that the entire operation allocates nothing. The buffer allocator initializes
new storage before copying, and optimizer behavior may remove allocations.

Runtime combined-length, capacity and allocation arithmetic keeps its normal
checks and may trap. The postcondition is not a proof of successful allocation
or trap-freedom. Source programs remain subject to the core's fixed term arena;
the grouped regression checks independent consumers separately, while the
composed two-extension example fits the defaults.

[The regression suite](../../tests/core_vec_extend.py) checks exact MIR equality
with and without additional postcondition reasoning. Both object targets and
native O0/O2 models cover empty/prefix/suffix cases, exact capacity, spare capacity,
growth, preserved order, independent source storage, released sources, signed
extremes, composed reads, capacity/length results and allocation cleanup. Wrong
source lengths, stale evidence and malformed unused imported implementations
are rejected with exact source diagnostics, positive object controls and no
invalid output artifacts.

These are checked length and access proofs plus finite runtime models. Prefix
and appended-element contents are not yet expressed as pointwise theorems, and
this is not ordinary `ensures` syntax or a mechanized compiler-soundness proof.
