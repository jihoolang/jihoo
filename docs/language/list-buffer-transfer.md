# Materializing lists in buffers

The list libraries can copy a proved-length list into contiguous storage in a
single structural copy pass. Repeated `nth` reads would traverse a growing list
prefix for every element, making this operation quadratic. The structural writer
instead passes one owned destination buffer through the recursion and advances
its offset once per element.

The source stays borrowed, and the result owns independent storage. Copying does
not consume list nodes or share their storage with the result. Later source
cleanup still traverses its nodes to free them.

## Exact-length input

`sized_list.to_buffer(n, xs)` borrows `xs: ref Sized(n)` and returns `buffer(n)`.
The runtime `n` supplies the allocation size; the private exact-length proof
supplies the writer's capacity evidence. No runtime length-discovery pass is
needed.

```jihoo
#![dependent_core]
import dependent.sized_list

fn main() -> i64 {
    let xs = sized_list.repeat(3, 17)
    let values: buffer(3) = sized_list.to_buffer(3, xs)
    index(values, 2, decide_lt(2, 3))
}
```

This returns `17`. Modifying the destination later does not change `xs`, and the
buffer can be returned from a function that frees its local list on exit.

## Runtime-selected input

`collect.to_vec(n, xs)` borrows `xs: ref Bounded(n)` and returns the existing
`dependent.vec.Vec` type. Its stored runtime count determines both the vector's
length and capacity. Only the kept values are copied; no intermediate buffer or
extra list is created. `n` is erased. The vector owns its buffer after the
collection is released.

`collect.to_vec_length(n, xs)` proves
`Eq(vec.len(collect.to_vec(n, xs)), collect.len(n, xs))`. The proof is checked
through the private record fields and is erased; invoking it does not allocate
a vector or perform the copy. It states a property of the conversion expression,
not an unrestricted rule equating arbitrary vector variables with the source.

The [complete example](../../examples/core_list_buffer.jh) selects values at
runtime, materializes the result, releases the collection and sums the vector
with the ordinary proof-bounded vector reads. The resulting vector can use the
existing mutation and growth operations.

## Writing an existing destination

`list.write_into(cap, xs, start, dest, fits)` borrows `xs: ref List`, consumes
`dest: buffer(cap)` and returns the same buffer owner after writing the source
values from `start` onward. It requires:

`fits: erased(Lt(start + list.length(xs), cap + 1))`

This expresses that the complete write fits. The destination elements before
and after the written range remain unchanged. Empty lists perform no writes,
including when `start == cap`. `cap` and `fits` are erased; `start` is a runtime
value. Passing a borrowed destination or reusing the consumed owner is rejected.
The writer allocates no storage itself.

The extended structural induction accepts an offset, a destination owner and
remaining-capacity evidence. In a Cons case, the evidence proves the current
store is in bounds and also proves the recursive call fits after advancing the
offset. Tail lengths appear only in erased evidence: the runtime writer neither
recomputes them nor calls `nth`.

`list.to_buffer(n, xs, exact)` allocates a fresh buffer and invokes this writer,
requiring `exact: erased(Eq(list.length(xs), n))`. Unlike `Sized`, an ordinary
list does not already supply its length as a runtime value; callers may need to
observe it first. Existing exact-length evidence lets a caller avoid that pass.

## Costs and validation

Copying to a buffer adds one allocation and visits each source node once during
the copy. The primitive allocator first initializes the destination, so this
is not a promise of one memory-write pass. Converting a bounded collection to a
vector adds the buffer and vector-record allocations. Both results have normal
ownership cleanup. Runtime arithmetic and allocation retain their checks and
possible traps. Structural recursion is not a guarantee of bounded stack use.

[The tests](../../tests/core_list_buffer.py) compare exact library/reference MIR,
require a single structural writer helper for `Sized` conversion with no extra
length traversal, and check complete erasure of the conversion-length theorem.
Both object targets and native O0/O2 models cover empty/small/larger lists,
partial destination writes and preserved surrounding values, signed extremes,
source independence and release, stored vector length/capacity and allocation
cleanup. Wrong capacity/offset/length evidence, repeated destination owners and
malformed unused imported definitions are rejected using exact source diagnostics,
positive object controls and no invalid output artifacts.

The library proves write bounds and result lengths. Element order and unchanged
surrounding values are regression-tested, not yet expressed as pointwise content
theorems. Elements remain i64, and no general compiler-soundness claim follows.
