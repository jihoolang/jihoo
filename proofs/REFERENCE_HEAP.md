# Reference storage candidate

Base: main d91629c65f80dc6aef2917bdc09895aa5bc7f50a (#189).

`ReferenceHeap.lean` is a separate, executable memory model with independent
operation rules. It leaves BoundedMir and the existing SizedMir proofs unchanged.
It is preparatory work for CommonData-to-MIR, not a proof of that lowering.

## Source contract checked

At this base, `compiler/core_lower.jh:209–226` allocates a boxed constructor's tag
and retained runtime fields. Consequently the fixed binary Tree has an 8-byte
boxed Nil (tag 0), and a 24-byte Node (tag 1 plus two children). Nil is not null.
`core_lower.jh:680–746` implements slots, allocation, release and put/get; pointers
are cast to i64 for storage and cast back after an i64 load.
`compiler/llvm.jh:1867–1873` emits inttoptr and ptrtoint for these casts.
`core_lower.jh:787–917` delays parent release and may reuse a pending allocation
of the same size. `core_lower.jh:1089–1190` generates recursive Drop functions
returning unit. None of these complete compiler paths is verified here.

The old BoundedMir `Option Nat` cell, i64-only dereference/store and absent null
constant cannot directly carry child pointer provenance. Missing provenance
storage/casts is the key Tree limitation; a null constant is not necessary for
successful boxed Tree representations. Existing address casts only expose a
nonnull abstract address token, not a reversible pointer storage encoding.

## Candidate semantics and checked claims

* `Ref.null` and `Ref.object id index` are distinct; object zero is nonnull.
  `Option.none` is uninitialized, distinct from a stored null reference.
* A Cell/Word is a scalar Nat or a reference with provenance. pointerToWord and
  wordToPointer roundtrip without reducing object identity to a scalar number.
  Scalar-to-pointer forging is outside this fragment, not a statement about
  arbitrary LLVM inttoptr. There is no concrete address/bit-pattern encoding.
* Every memory access checks container existence, liveness and strict bounds.
  Loads require initialization and the requested payload kind. Scalar stores
  enforce the old scalarBound. Reference loads/stores transport dangling values;
  child liveness, bounds and ownership must be supplied separately before use.
  Free requires a live base pointer and preserves cells; it does not recursively
  drop children. Identities are append-only, with no reuse of released IDs.
* `execute_iff` and `step_deterministic` connect executable reference read/write,
  null test, allocation and free with independent operation rules. This is a
  memory-operation machine, not an extension of the BoundedMir CFG interpreter.
* Scalar load/allocation/release commute with exact heap embedding.
  `scalar_write_compatible` uses actual BoundedMir.write, under pointer local
  type/value premises, and includes container, bounds, liveness and scalar
  payload failure cases. It is not full CFG/program simulation.
* `node_cycle` proves allocate(24), tag store, both child stores, both child
  loads, and parent release for arbitrary external heaps/children under exact
  allocator capacity and cell-budget premises. `external_frame` preserves all
  old objects and their liveness/cells at each stage. Children may alias or be
  null/dangling; source ownership/tree well-formedness is not inferred.
* Boxed Nil/Node tag reads, null/initialization separation, rejected type reads,
  out-of-bounds/dead/absent containers, invalid free, scalar overflow, allocation
  size rejection and dangling-reference transport have Lean regression checks.

## Remaining proof obligations

CFG locals/types, raw-word casts and pointer arithmetic integration; a CommonData
heap relation including ownership; supported source lowering and its resource
bounds; delayed free/reuse; calls, recursive Drop and unit return; native address
width/alignment/provenance correspondence; allocation failure and target runtime.
The candidate memory operations neither establish native refinement nor the
entire existing scalar/Buffer program semantics under an extended interpreter.

Run `cd proofs && ./check.sh` with Lean v4.34.1. The shared audit includes every
named theorem in ReferenceHeap and rejects nonstandard axioms/sorryAx.

Validation on this change: full `lake build` succeeded (328 jobs); `./check.sh`
succeeded with warnings treated as errors, 3,171 audited declarations and all
existing generated-fixture comparisons. The 14 new executable boundary examples
use kernel `decide`. Independent review found no blocker in the candidate model;
the scope restrictions above remain necessary.
