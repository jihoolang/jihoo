# Common resource contexts at callable Drop boundaries

`Jihoo/CommonDataTargetContext.lean` connects the existing common lexical
context to direct target locals and the boxed reference heap. It reuses
`RecursiveLexicalFields.Agrees`, common `removeHead`, symbolic closing,
`CommonDataReference.Related`/`BufferRelated`, and `TreeDropCall.invoke`.

`Resource` is one Data image or a source/target Buffer pair. `Context` keeps:

- source validity, source lexical agreement, and target lexical bindings;
- actual Data/Buffer layout and liveness for every inventory resource;
- joint source ownership, including pending parents and an external frame;
- joint target separation, including every boxed Nil and pending shell;
- pending-parent shell contents and liveness, without demanding live children.

Lexical entries name inventory slots, not owned objects. Multiple lexical aliases
can name the same inventory slot without duplicating ownership. `removeHead`
retires every alias of the consumed slot and reindexes surviving slots. It does
not remove lexical positions or clear locals. Dead and ghost entries impose no
target-local condition. Two source-empty trees still require two distinct boxed
Nil objects. Source and target IDs need not agree numerically.

`Context.data_lookup` and `buffer_lookup` derive the actual source value,
non-dereferencing target operand, layout, and liveness from the same resource.
`CommonContext` additionally fixes the common judgment's ordered Data prefix,
Buffer suffix, and Buffer sizes. `sources_inventory` identifies its source
inventory with the existing `CommonData.caps`.

## Drop theorem

`typed_drop_prefix` takes a valid `CommonContext` and the common Drop typing
derivation. Its conclusion contains the continuation's source typing, a
constructed source `Destroy`, actual target call/recursive-free/return steps,
the `CommonContext` at the resumed continuation, and the exact target heap
effect. No successful body execution, `BodyIH`, or arbitrary `Post` is assumed.
`symbolic_drop_prefix` obtains the same result through the existing symbolic
closing and source-rule elaboration. Neither theorem executes the continuation.

The target program must install the relocated Drop, and the caller must actually
be at its call block with an existing continuation and a writable unit local.
The separate stack limit must cover the finite image depth. `Fresh` excludes the
unit destination from every *surviving* active lexical local, including scalar
and natural locals. `Site` alone does not establish that exclusion.
`resume_operand` proves that all other direct operands retain their values.
Dereferencing a consumed pointer is intentionally outside that statement.

`Context.after_drop` derives preservation for retained Data, Buffers, pending
shells, source ownership, and exact external target objects. Unrelated target
objects can be dead or absent. `data_accounting` reuses the existing mapped
source-node and extra-Nil accounting; source and target free traces are different.

## Extension laws and limits

`Bindings.bind`, `map`, `argument`, and `captured` are binder and static partition
interfaces. The latter two use the existing common prefix-partition maps and
preserve lexical positions. They transport target bindings; they do not prove
complete application context splitting/recombination or body lowering.

`Context.open_case` derives the actual source `enter` and target `openNode`
results, revokes all parent aliases, binds child slots in lexical order, and
moves the parent shell into pending ownership. Child pointer locals are an
explicit preloaded interface for future field-load lowering. This theorem does
not execute the corresponding target load instructions or a branch body.

This is a resource invariant, not complete value correspondence: scalar source
and target values are independently well shaped, while their equality is not
asserted. Existing scalar locals are preserved by Drop. Native addresses, casts,
allocator refinement, arbitrary pointer graphs, general body lowering, and whole
native compiler correctness remain outside the result. Generic block linking is
an independent module and is not needed for the existing `invoke` boundary.

## Validation

`CommonDataTargetContextChecks.lean` constructs a common context with two Data
aliases, a retained boxed Nil, a retained Buffer, scalar/natural locals, and an
absent external frame. The typed continuation drops the retained Nil and frees
the Buffer. The boundary theorem supplies its context without running that body.
Checks cover stale aliases, rejected duplicate Nil and Data/Buffer overlap,
scalar/natural destination collisions, ghost and child bindings, pending parent
preservation after a child Nil becomes dead, dead/absent external objects, and a
live zero-length Buffer.

Run `bash proofs/check-common-data-target-context.sh` for the dedicated build and
axiom audit. All declarations also participate in the aggregate build/audit;
the dedicated check runs on both architectures in the Test workflow.
