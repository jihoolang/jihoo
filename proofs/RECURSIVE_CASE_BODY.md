# Source-typed Buffer segments inside a recursive case

The lexical interface in #170 proved field entry and delayed shell release,
but `finish_safe` required ownership and field interpretation after the body
as premises. `RecursiveCaseBody` now derives those premises for a scalar
Buffer body typed by the existing `SizedCoreTyping.Typing` judgment. Successful
execution, final frame ownership and non-release of the frame are conclusions.

## Connection to the existing source judgment

`RecursiveBodyProjection` maps the mixed lexical environment to the existing
sized Core environment without deleting or reordering slots. Natural and scalar
values remain available. Only Buffer capabilities in the suffix become owner
slots; Data slots become dead entries with ghost runtime placeholders. Original
erased slots also become dead entries: they cannot fabricate a bound fact.
The existing body may introduce its own checked bounds through its original
rules. No recursive allocation is reinterpreted as a Buffer.

`project_agrees` derives the original `SizedBufferContext.Agrees` from the mixed
relation. `body_total` invokes `SizedCoreTyping.Typing.total_accounted` with
that agreement and the original length layout. Its actual safe steps, exact
accounting and `Eval.lease_frame` allow `OwnedApplicationFrame.recombine` to
restore ownership of the pending parent and retained Data footprint. The input
ownership is permuted by `owns_rotate`, not assumed in two unrelated orders.
`body_every_run` additionally proves that no retained allocation appears in
the body's release events. Allocation freshness prevents release/reallocation
from masquerading as preservation.

`BodyRun` executes the existing graph on the same projected heap. It explicitly
leaves the separate abstract field cell store unchanged. This is a definition
of this restricted mixed semantics, not a theorem about native byte stores.
The final lexical continuation uses the original mixed environment, not an
inverse of the projection: every Buffer alias is dead, Data aliases retain
their original roots, and the returned scalar is prepended.

## Composed segment

`SegmentTyping` checks an actual variable scrutinee node ID and an existing
source body node ID under the child-binding layout. `SegmentRun` reads the
scrutinee's stored child roots, executes that body, then releases the pending
parent. `segment_total` constructs this execution, safe heap steps, a valid
final state, the residual child inventory and its mixed lexical continuation.
`segment_every_run` transfers safety and residual ownership to every admitted
segment execution using source determinism.

This is an intermediate segment, **not a source Case typing rule**. The graph
view still has no Case node; the segment interface does not recognize one,
select a constructor tag, validate a constructor telescope, enforce branch
coverage/equal linear use, or check a dependent motive. The scrutinee must be
a variable denoting a nonempty binary tree whose capability heads the semantic
inventory. The body returns a scalar and consumes only the Buffer suffix.
Both child Data capabilities remain for a subsequent continuation; they are
not silently dropped by a completed scalar Case. General recursive body
operations and their linear consumption/return remain open.

The body cells are frozen, its result is scalar, and only the fixed
`[erased slots..., left, right]` field layout is supported. Native Case lowering
may reuse the pending shell or flush it at different block boundaries. No
native lowering, node-reuse, dependent Case, Back, or full common-Core soundness
claim follows from this segment theorem.

## Validation

The hand-built regression graph uses the existing Core constructor view; it
is not claimed to be a native-export snapshot. The nonempty fixture enters
parent 0 with children rooted at 1 and 2 (right footprint `[2,3]`), consumes
Buffers 4 and 5, allocates Buffer 6, lends/reads/closes/frees it, and frees parent
0 last. All child allocations remain owned. Two erased binders, outer natural
and scalar values, and separated Buffer aliases exercise lexical index
preservation. Negative tests reject Data-as-Buffer free and a shared
Data/Buffer identity; ghost slots supply no bounds. An empty Buffer suffix
also exercises composed totality.

Run `bash proofs/check-recursive-fields.sh` or
`nix build .#checks.x86_64-linux.recursive-field-proofs`. The standalone audit
includes the new modules and regressions; shared Core aggregators and compiler
sources remain unchanged. See [the interface overview](RECURSIVE_FIELDS.md)
for the current theorem count.
