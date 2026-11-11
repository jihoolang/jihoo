# Runtime field interpretation

The next missing connection after the recursive ownership interface was that
`Tree` edges were only mathematical metadata. Nothing required an executable
heap lookup to return those children. `RecursiveFieldRuntime` supplies that
relation for a finite binary abstract pointer heap.

A state contains the existing `HeapLeases.State` and a separate cell store.
Each cell stores two nullable child references. `Represents` relates these
stored references to the root references of the witness subtrees.
`Interprets` adds root-reference agreement and the existing unique, live,
unborrowed ownership inventory. A child reference is not its flattened
inventory: a right child rooted at 2 can own both objects 2 and 3.

`take` reads the actual cell and rejects a missing cell or a dead parent. It
returns the stored references, clears the parent cell and releases the parent
in the old heap. It does not dynamically check leases. `split_safe` derives
legal release from ownership and proves that both returned children retain
their interpretation, together with their joint ownership and ambient frame.
`take_result` identifies every successful observation. `allocate_safe` installs
actual field references and derives the new parent representation; allocator
freshness protects existing interpreted subtrees.

`consume_left_total` first constructs the split and then invokes the existing
`OwnedCoreApplications.Typing` totality theorem on the left footprint. The
right subtree remains interpreted after that consumer runs. This preserves a
real field-store relation in addition to the old capability counts; successful
execution and output interpretation are conclusions rather than premises.

## Checks

Run `bash proofs/check-recursive-fields.sh` with pinned Lean and Python, or
`nix build .#checks.x86_64-linux.recursive-field-proofs`. The existing independent
Nix check runs on both CI architectures. See [the interface overview](RECURSIVE_FIELDS.md) for the current audit count.
It uses warnings as errors and allows only standard logical axioms. The shared Core audit and #168 files are unchanged.

The new fixture contains parent 0, left leaf 1, and right subtree 2 -> 3. It
proves initial ownership and store interpretation, checks actual returned
pointers, rejects wrong stored pointers, missing cells, dead parents and
borrowed-parent interpretation, and instantiates Core consumer totality while
retaining the nonempty right subtree.

## Boundary and next connection

This is an abstract runtime representation layer. The cells are not native
bytes, offsets, tags or allocator blocks. Null denotes the empty abstract tree;
no claim is made that a particular source nullary constructor uses null.
The old Core semantics operate on the projected heap and leave this added cell
component unchanged. A consumer of the left footprint still treats allocations
as the existing Buffer1 resources; it is not a source-level recursive-data case
body with typed recursive variables.

The production `Case` rule frees one boxed parent and passes its owned fields
to its selected case. This interface captures that resource-transfer shape,
but `ScopedLend.Graph.Node` still has no data constructors or `Case` node. To
prove the actual rule, the next work needs constructor signatures/tags and a
source graph view, a runtime value/lexical interpretation for recursive values,
and a typing rule whose premises derive this field interpretation. A type and
layout distinction must prevent arbitrary Buffer operations from treating
recursive objects as buffers. Dependent case motives and binders, general
recursive families, `Elim`, `Drop`, `Back`, and native compiler correspondence
remain outside this module. #168's symbolic Buffer compaction is unchanged.
The common Core typing and 0.6 release blockers remain open.

The stored root uniquely determines any admitted finite tree witness
(`Represents.unique`); an alternate truncated witness is rejected. Additional
regressions check allocation followed by actual lookup/removal. This uniqueness
result does not implement a decoder or prove that every raw store admits a tree.

The Core consumer still receives `l.owners` separately from the interpretation
witness. There is no operational rule converting the returned field pointer into
a recursive lexical value/environment. The cell store is explicitly frozen
during that old Core execution; field loads/stores are not added to its rules.
Allocation preservation covers owned subtrees and their frame, not arbitrary
unowned cells or a global store-integrity invariant.

There is also an execution-order gap: the production Case lowering reads fields
and frees the parent at the end of the block, with same-size node reuse when
applicable (`docs/internals/core-spec.md`, data Case runtime rule). This model
releases the parent immediately in `take`, before running the consumer. No
reordering, release-timing, or node-reuse correspondence theorem is claimed.

The subsequent [lexical interface](RECURSIVE_LEXICAL_FIELDS.md) adds actual
child-root binding and a separate pending-shell release model. It does not
extend this eager consumer into a source Case body or prove trace equivalence.
