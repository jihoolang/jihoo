# Executable boxed Tree Drop

Base: main `c9373a36` (#191). Inspected `compiler/core_lower.jh:1092–1185`
and `CommonDataDestroy.lean`. Production `drop_glue` reads the tag and saves
owned fields, releases the parent, then recursively drops owned fields in field
order (buffers, if any, precede recursive owned fields). The binary Tree fragment
has no buffer fields. `CommonData.Destroy` likewise releases parent, left, right.
Case's delayed pending-shell release and reuse are a different operation.

`CommonDataReference.drop H root fuel` is executable. It reads the actual tag
and child references from `ReferenceHeap`, frees boxed Nil or Node, and returns
an optional final heap and preorder release-ID list. Image, source Tree, and
ownership proofs are not execution inputs. Fuel bounds recursive depth, including
Nil, and is decremented independently on both recursive calls. Failure returns
`none`; this pure Option interpreter does not expose a partially modified heap
or claim transactional native behavior.

`drop_total` derives success from finite `Layout`, duplicate-free image IDs and
`Image.depth ≤ fuel`. It constructs child success by induction and frames the
right child over left destruction. Layout supplies live initialized tags and
actual base-pointer children. No allocations occur, so no allocation-capacity
budget is needed. `destroy_correspondence` adds source `Valid` and live,
lease-free ownership of the source tree plus an arbitrary frame, and constructs
the existing `CommonData.Destroy` derivation and legal `HeapLeases.Steps`.
`every_source_run` transfers to any observed source Destroy derivation.

The exact traces are `i.source.owners.map free` and `i.ids`. Both are preorder,
but source node IDs correspond through `i.pairs`, not numeric identity. Source
empty stutters; each target Nil is freed. `source_pairs` identifies the ordered
source nodes, while `resource_count` gives exact target multiplicity as mapped
nodes plus Nils. `nil_count` gives N+1 extra Nils for N source nodes. Target IDs
are duplicate-free, hence every corresponding object is released exactly once.
Raw trace equality, including deletion of Nil without remapping identities, is
not asserted.

`Frees.effect` specifies every target object: inside the image its live bit is
false with the identical cells; outside it the complete optional object is
unchanged, including absent and already-dead objects. Thus it is newly destroyed
objects that are confined to the image, not a claim that all external objects
are live. Source `released_dead`, `source_live_frame`, `source_unchanged`,
`Destroy.cells_frame`, and `Destroy.lengths` provide the corresponding source
facts. `retained_tree` and `retained_buffer` preserve independently owned retained
Tree/Buffer relations under explicit source/target footprint separation; no
retained-resource postcondition or successful child execution is assumed.

The executable checks cover empty, nonempty and nested trees, exact release
order, sufficient/insufficient fuel, retained buffer contents, repeated free,
invalid tags, uninitialized tags, null/interior/absent roots, dangling children,
shared children and cycles. Malformed graphs have no unconditional success
claim. In production the final constructor is the switch default; unknown tags
may therefore enter its branch. The abstract interpreter deliberately rejects
unknown tags. Correspondence is restricted to well-formed Related inputs, not
malformed native execution.

This is an abstract ReferenceHeap/source-resource theorem, not MIR CFG execution,
native pointer-cast/layout refinement, pending reuse, or whole-compiler correctness.
No compiler source is changed.

Run `bash proofs/check-common-data-reference-drop.sh` with the pinned Lean on PATH.
It builds checks with warnings as errors and audits ten theorem dependencies,
allowing only Lean's propext, Quot.sound and Classical.choice. The existing Common
Core backward CI workflow invokes this check; the aggregate Jihoo imports the
regressions as well.
