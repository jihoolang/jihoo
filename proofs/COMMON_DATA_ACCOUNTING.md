# Common allocation-identity conservation

The 0.6 roadmap calls for runtime resource guarantees from specified typing
rules. After resource-partitioned Data application, the common theorem supplied
safe execution, result ownership and frame representation preservation, but not
conservation of every input and intermediate allocation. This change strengthens
the existing judgment's general theorem instead of adding a new typing fragment.

For every allocation identity `x`, `Account input output events` states:

```text
count x (released events) + count x output
  = count x input + count x (allocations events)
```

The input is `footprint (caps trees owners)`. The external frame is excluded
from both sides. Scalar results return an empty footprint; Data results return
the **whole** finite tree footprint, including all descendants, not just its root.
`AccountedPost` uses the same tree witness for actual stored-field representation,
final ownership and accounting. `ResultFootprint.unique` derives witness
independence from actual final field references via `Represents.unique`.

## General rule coverage

`Typing.total_accounted` strengthens the previous totality proof for every
constructor of the same `CommonData.Typing` judgment. `Typing.total` remains a
compatibility projection. No new syntax, runtime rule or accounting premise is
added to typing.

- Embedded scalar Core and Buffer let reuse sized accounting over the actual
  projected execution events, including fresh owned-result readers.
- Literal and empty return no allocations; a Data variable returns its entire
  input tree; construction adds exactly its one fresh parent identity.
- Whole-inventory and partitioned Data applications cancel the intermediate
  result footprint. Retained captures enter the body exactly once. Reordering
  Data/Buffer inventories is justified by count-preserving permutation.
- Drop uses the already constructed exact recursive free trace.
- Empty Case uses the empty footprint. Node Case excludes the pending parent
  from branch accounting, keeps it in the branch frame, and accounts for it
  exactly once at the final release. Returned-tree representation survives that
  release using the existing separation proof.

`Typing.every_run_accounted` transfers the constructed result to every execution
of the deterministic operational semantics. Runtime execution does not receive a
partition plan or an accounting witness. `AccountedPost.account_for` permits a
caller to use any valid final representation witness with the same result.

## Consequences and necessary assumptions

`Typing.other_released` proves that every initial or newly allocated tracked
identity absent from the result is actually freed exactly once and is dead in
the final heap. The count equation and safe-trace release distinctness both
participate; a mere producer-supplied trace is not assumed.

`Typing.survivors` proves that returned descendants and declared frame objects
are live and were not released. `Typing.live_domain` additionally requires
**initial live coverage** by the input inventory plus frame. Only then does the
final live identity set equal the returned footprint plus frame. This is not
equality of entire heap records: payloads, stale cells and allocation counters
can remain. `Typing.scalar_no_leaks` specializes this result to a scalar consumer
with complete initial coverage and no external frame.

A regression deliberately starts a literal execution with an untracked live
object. It remains live, demonstrating why coverage cannot be omitted.
Allocation accounting also cannot distinguish one empty logical Data capability
from two: both footprints are empty. Logical capability exactly-once use and
lease-token accounting are separate properties.

## Evidence and boundary

Regressions reuse existing runs for computed reconstruction followed by Drop,
returned descendants, nested pending Case shells, and partitioned return with
retained captures. They check exact fresh-object release and the final live set.
A manually wrapped version of the existing sized composition graph projects
exactly to that graph and reuses its parametric owned-result-reader derivation
and execution, proving common accounting and scalar no-leaks from the empty
heap. This wrapper is not claimed to be a new production export. The original
checked-source snapshot comparison remains in the standalone check.

All results remain within the existing fixed binary Data/uniform sized Buffer
closing-instance judgment, with finite tree interpretations, successful abstract
allocation and monotonically fresh identities. No production compiler code is
changed. Production checking is tested rather than proved; dependent Pi/closure
rules, general families/motives, recursion, Back, native field bytes/address reuse,
erasure/lowering refinement and whole-language quantity soundness remain open.
This closes allocation-ID accounting for this common fragment, not those gates.
