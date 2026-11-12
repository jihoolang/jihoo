# CommonData and boxed Tree state correspondence

Base: main 92d9f42f (#190). `CommonDataReference.lean` adds a state/resource
bridge to the existing CommonData state and executable ReferenceHeap operations.
It imports the independently reviewed ReferenceHeapFrame laws (parallel commit
6e3e52e), without changing that module, ReferenceHeap, or scalar compatibility
proofs. Shell release uses its success characterization and external set frame
law. Both frame regression checks and all frame audit entries are registered
in the aggregate build/audit, so both architectures exercise them.

## Representation and initial invariants

`Image` records independent source and target identities at each nonempty node.
`source_pairs` identifies the source projection with the existing Tree owners.
`pairs` is the explicit node correspondence; `nils` separately lists the extra
boxed empty objects. `resource_count` gives exact multiplicity accounting and
`nil_count` proves one more target Nil than source nodes. Target `ids.Nodup`
excludes sharing between any nodes or Nils, including repeated empty children.
Source `OwnsTree` excludes duplicate source nodes and supplies live, unborrowed
ownership. No equality of object IDs or allocation traces is asserted.

`Related s H image` requires existing `Represents s.cells image.source`, existing
`OwnsTree s.buffers.heap image.source`, exact live target objects via `Layout`,
and target separation. Thus initial fields/layout/ownership are explicit
invariants, not inferred from arbitrary reference values. `Layout.bound`,
`tag_total` and `children_total` apply recursively to every finite Image: a Nil
has tag 0, a Node has tag 1 and two initialized provenance references, and each
child has its own recursively valid layout. Loads are proved successful; no load
result or successful execution is a premise.

## Executable lifecycle correspondence

* `empty_total`: source empty leaves its state unchanged while target `makeNil`
  allocates eight bytes and stores tag 0. It yields a new Related empty and
  preserves all old target objects. `Related.push` and `BufferRelated.push`
  preserve retained relations while the source state stutters.
* `allocate_total`: source `CommonData.allocate` and target `makeNode` (allocate
  24 bytes, store tag and two references) succeed and establish Related for the
  parent. Source validity, joint child/frame ownership and joint target child
  separation are required. Source frame ownership and every old target object
  survive. `Related.allocate` and `BufferRelated.allocate` retain other resources.
* `case_open_total`: actual source `RecursiveLexicalFields.enter` and target
  `openNode` succeed. Source lookup is an explicit environment-selection premise;
  field results are derived from Represents and Layout. The two children remain
  Related, and neither state changes. The parent shell remains pending.
* `finish_total`: a live, unborrowed source pending owner and a chosen
  live target shell can be released, preserving any retained finite tree,
  source owner frame and every other target object. `finish_children` derives
  both the actual node pairing and separation from a Related node and preserves
  both children. The source action
  is actual `CommonData.finish`; target action is executable `ReferenceHeap.release`.
* `empty_case_total`: source empty Case stutters; target tag read and extra Nil
  release succeed. `Related.retireNil` and `BufferRelated.retireNil` retain disjoint
  resources. A consumed target Nil is no longer part of a live empty relation.
* `BufferRelated` describes a retained live uniform-fill buffer with independent
  IDs and exact length/cells. Its finish/allocate/Nil-retirement laws preserve
  this relation. This does not execute a Buffer body or prove a general Buffer
  compiler simulation.

Allocation requires `Budget H n`: fewer than 512 allocated object slots and
existing total cell count plus n at most 4096 (n=1 for Nil, n=3 for Node).
Dead objects continue to count; there is no reuse. These are the actual allocator
bounds. Source freshness uses existing `HeapLeases.Valid`. Arbitrarily large
finite trees cannot necessarily be constructed under this bounded allocator.
The results are local lifecycle steps from explicit valid initial relations,
not a total serializer from every source state into a bounded target heap.

## Limits and validation

No full CFG, complete lexical-environment/trace simulation, native pointer-bitcast
refinement, pending allocation reuse, arbitrary intervening body simulation, or
general recursive Drop theorem is claimed. The source frame and target external
frame can include retained buffers; the theorem does not assign an automatic
mapping to every unrelated object in the entire CommonData heap. Frames must be
separate from the released target shell. The parent may be released after any
intervening work only when the stated current-state invariants still hold.

`CommonDataReferenceChecks.lean` exercises source node 7 / target node 3,
two additional Nils, actual source Case opening, retained Buffer source 4 /
target 0, child relations after finish, double-free/dead loads, invalid child
layout, alias rejection, and object/cell budget exhaustion. Examples use kernel
`decide` or ordinary proofs, not native_decide. All public named theorems are
registered in the shared axiom audit. Run `cd proofs && ./check.sh`.
