# ReferenceHeap frame API

Base: main `92d9f42fc47106d047b071e49fc0e7022452efdb` (#190), fetched on
2026-11-12. Branch: `codex/reference-heap-frame`, isolated worktree
`jihoo-reference-frame`. Only new files are added. `ReferenceHeap.lean`, CommonData
Tree definitions, `Jihoo.lean`, shared `Audit.lean`, and `check.sh` are unchanged.

Import `Jihoo.ReferenceHeapFrame`; APIs are in `Jihoo.ReferenceHeap.Frame`.
This is a proof about the existing abstract reference heap, not the native allocator.

## Contracts and API

- `Agree F H K` means exact lookup equality at every object ID in `F`, including
  missing objects, liveness, slot count, initialization, values and provenance.
  It does not imply equal heap sizes or follow stored pointers transitively.
  `Supported F P` is an explicit obligation that this agreement suffices to
  preserve a higher-level assertion `P`. Use `agree_trans` for operation sequences.
- `store_success_iff`: success iff the container exists, is alive, the index is
  strictly within bounds, `validCell v = true`, and the result is the stated
  object/slot update. Initialization is not required for a write. Scalars must
  satisfy `n < BoundedMir.scalarBound`. References may be null, dangling, interior,
  self-referential, or aliases: storing them does not dereference them.
- `release_success_iff`: success iff the object exists, is alive, the offset is
  zero, and the result sets its liveness to false. A live zero-slot object can be
  released although it cannot be read. Release preserves stored cells and does
  not recursively release children.
- `load_success_iff`: existence, liveness, strict bounds, and initialized
  `some (some v)` are all explicit. Typed load additionally checks the Cell
  constructor. Initialized null is distinct from an uninitialized slot.
- `store_agree` / `release_agree` preserve every object with a different **ID**.
  From this, `address_eq`, `valid_iff`, `initialized_iff`, `liveBase_iff`, `load_eq`,
  `loadRef_eq`, `loadScalar_eq`, and `own_iff` preserve external observations,
  including failures. No liveness/bounds premise is needed on the external
  observation because the equality also preserves invalid states.
- `store_frame` / `release_frame` preserve arbitrary supported assertions when
  `∀ k, F k → k ≠ j`. This is a sufficient object-level separation condition,
  not a claim that it is necessary for every assertion or every write.
- `store_object`, `store_load_self`, `store_liveBase` describe the modified
  object. `store_load_other_slot` preserves any other index of that same object,
  including failure cases. This finer observation rule does not create separate
  exclusive owners for the slots. `release_object`, `release_load_none` and
  `release_not_live` describe invalidation of the entire released object.
- `read_frame` proves a successful executable reference read returns the identical
  heap; `read_supported` preserves **any** heap assertion without separation.
  The plain scalar/untyped load functions are pure observations, not transitions.

## Logical ownership and mixed external frames

`Own H j cells` claims an exact **live** object. It is a logical assertion;
ReferenceHeap does not enforce ownership permissions at runtime. `Claim` names
an object ID, a local `Kind.buffer`/`Kind.data` label, and its exact cells.

`OwnMixed cs H` requires pairwise-distinct IDs via `Nodup`, a `Shape` proof for
all claims, and `Own` for each one. Buffer shape allows uninitialized cells or
bounded scalar cells. Data shape allows uninitialized cells or any valid Cell,
including reference values. These are storage-level claims; they do not define
source Buffer lengths, constructor tags, Tree layouts, recursive ownership,
acyclicity, or a CommonData representation relation.

`mixed_supported` proves this assertion depends only on `Footprint cs`.
`store_mixed` / `release_mixed` preserve it for successful operations under the
explicit condition `∀ c ∈ cs, c.id ≠ j`. `own_store_mixed` additionally supplies
successful execution and the updated local ownership from `Own`, bounds and
value validity. `own_release_mixed` supplies execution, dead-object contents,
loss of local liveness, and the preserved external ownership.

Distinct object owners do not require disjoint pointer values. An external Data
object may hold a pointer to the modified/released object: its own cells remain
unchanged, but that pointer's target may die. To preserve a reachable-child
invariant, include the observed children in the footprint and prove `Supported`;
do not infer reachability closure from the label `data`. Similarly, two different
references to different indices of one object are not separate object owners.

## Validation and counterexamples

Run with the pinned Lean 4.34.1 toolchain on PATH:

```sh
cd proofs
python3 check-reference-frame.py
```

The standalone runner builds just the dependency closure (6 jobs), checks both
new modules with warnings as errors, checks exact audit coverage, and rejects
axioms outside `propext`, `Classical.choice`, `Quot.sound`. It audits all 37 API
theorems, 21 check theorems, and the 4 existing scalar compatibility theorems
(load/write/allocation/release): 62 declarations. It does not modify the shared
audit or import aggregator. New APIs will require explicit integration there if
the repository wants them included in the default full-project check.

The 18 kernel-decided boundary witnesses cover aliases, mutation of owned
contents, external pointer survival with target death, dangling/self pointers,
uninitialized versus initialized-null slots, initialization by store, one-past,
absent/null/dead containers, interior release, zero-slot release, oversized
scalars, and wrong typed reads. Three further proofs establish concrete mixed
ownership and general mixed store/release clients. No `sorry`, added axioms, or
`native_decide` is used. The concrete ownership example has a scalar buffer, a
Data object containing null, and a pointer alias into the buffer.

## Unproved scope

No CommonData Tree representation or source/target lowering theorem is supplied.
No whole-program Buffer/CFG simulation, recursive Drop, alias analysis, native
pointer encoding/LLVM provenance refinement, alignment, allocation failure
simulation, allocator reuse, delayed free, concurrency, or complete native
allocator correctness follows from these results. Allocation frame rules remain
the existing push-based `ReferenceHeap.external_frame`; this module focuses on
load/store/release and does not extend allocation semantics.
