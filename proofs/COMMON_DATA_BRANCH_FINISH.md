# B: conditional branch body and pending-shell finish

Base: frozen contract commit `4a701387` on `proof/common-composition-contract`.
This base contains copied, unmerged #201 prerequisites; it is not main.
Only this B module, its checks, its dedicated script and this note are added.

## Proven interface

`finish_context` accepts an arbitrary valid Boundary whose pending list is a
named head followed by a tail. Given an exact retired target heap and unchanged
locals, it derives the final CommonContext. No child pointer is read. The proof
preserves images, Buffer identities and sizes, lexical layout, both ambient
frames, retained data representations and ownership, and every remaining shell.

`finish_authority` derives the source free Step and final Post using
`CommonData.Post.finish`, and derives target release from Pending.Valid.
`finish_result` constructs the frozen FinishResult from those facts and an
explicit `FinishExecution`, rather than assuming FinishResult or final validity.
`body_finish` composes the actual bounded walks at the exact shared boundary,
adds ticks, appends the singleton free event, and preserves suspended callers.
`result_preserved` transports either the scalar local or actual inventory image
and its pointer local. `pending_not_result` excludes source-owner aliasing.

## Explicit remaining assumptions

* The input boundary is valid; its pending list has the specified head/tail.
* BodyResult is supplied: source Typing (including inventory count and sizes),
  actual source Eval, actual target Transfer, result Post including all pending
  owners, and result-local representation. No body evaluator/compiler is proved.
* FinishExecution supplies the bounded walk in ONE installed program, exact
  retired heap, equality of all locals, and equality of suspended caller stacks.
  Thus instruction placement/execution is still required at each integration
  site. The concrete check proves one nontrivial one-tick inhabitant, not a
  universal placement provider.
* The all-locals equality restriction is conservative. A general scratch-slot
  write-set variant is not provided. The concrete free writes unit into an
  already-unit destination and therefore satisfies this stronger restriction.

No source/target event correspondence, return ABI, entry provider, general
Supported lowering, allocation scheme or production compiler correctness is
claimed. Target ticks and final machine state are explicit indices. C must
supply BodyResult and FinishExecution in its single installed program, and A
must independently supply its entry provider.

## Checks and integration

Run `bash proofs/check-common-data-branch-finish.sh` with Lean 4.34.1 on PATH.
Checks include a real one-tick free with dangling child references, a retained
result pointer and live target box, a nonempty suspended stack, generic nested
pending/Buffer preservation, and rejection of a pending/result source alias.
Nested/Buffer and rejection tests are theorem specializations with explicit
validity inputs; they do not fabricate a body execution or a concrete complex
context. The ten named theorems are axiom-audited by the script.

After #201 lands, replay the shared contract onto resulting main and then this
B commit. Do not replay its copied prerequisite commits. Shared imports, CI and
audit registration require a separate integration change. No merge is made.

Validation: Lean 4.34.1 isolated dependency/module build passed (123 jobs);
dedicated checks passed (124 jobs), including warning-as-error elaboration and
ten axiom audits. Dependencies were only `propext`, `Quot.sound`, and (for
finish_authority/finish_result/body_finish) `Classical.choice`. No sorry/admit or
custom global axiom occurs in the added Lean modules. `git diff --check` passed.
The full shared check.sh was not run; shared build targets are unchanged.
