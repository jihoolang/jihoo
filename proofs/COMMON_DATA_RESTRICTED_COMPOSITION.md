# C: single-program Case placement

Base: shared contract commit `4a701387` on
`proof/common-composition-contract`. This includes copied, unmerged #201
prerequisites. This work does not merge them or identify that branch with main.

## Proved scope

`CommonDataRestrictedComposition.lean` gives a syntactic installation witness
`Placement p f`: one complete function-zero `Program` equals an explicit
prefix, a seven-block relocated Case fragment, and a suffix. The witness does
not assume any execution. `assemble_placement` constructs such witnesses for
every member of an arbitrary finite list assembled into a single final block
array. Prefixes and suffixes are arbitrary, and the list can contain repeated
fragments. Existential placement does not promise a unique occurrence.

`Placement.program` proves equality with the existing `linked` program, so
`Placement.walk`, `Placement.node_entry`, and `Placement.nil_entry` reuse the
existing interpreter theorems without replacing the running program. Node
and Nil still take exactly 11 and 5 copied-entry ticks, respectively.
`parentPlacement` and `childPlacement` construct both witnesses for the same
two-fragment program. `nested_jump` proves that either parent branch's
trampoline takes one tick to the child's copied entry, preserving heap,
locals, and suspended callers. The trampoline uses forward relative address
13, hence no subtraction or underflow assumptions.

`placed_induction` fixes p before strong induction. The explicit step receives
only supported child IDs strictly less than the current ID, with their own
layout witnesses in p. It is an eliminator, not a body theorem. The assembly
proof independently recurses on a strictly smaller list tail. Neither proof
assumes the desired outer Case semantics.

## Executable evidence

The dedicated checks execute a relocated parent Node followed by its left
Nil in the very same program: prefix length two, initial root slot six,
child root slot four, 17 (= 11+1+5) ticks, and exactly `[free 1]`. A symbolic-stack variant proves the same path for arbitrary suspended callers
under an explicit stack bound. A further proof exports genuine `ReferenceCalls.Steps`. The checks also instantiate
simultaneous placement of three fragments with nonempty prefix and suffix.
The generic entry and jump theorems allow arbitrary suspended callers,
subject to the explicit stack-depth bound.

Run `bash proofs/check-common-data-restricted-composition.sh` with Lean 4.34.1
on PATH. The script builds only this dependency closure and audits 14 named
theorems against the usual Lean logical axioms. No shared CI/import/audit
file is modified.

## Unresolved integration obligations

This is a placement result, not a compiler correctness result or a claim that
all `Supported` expressions have layouts. The concrete nested execution is
an operational prefix; it does not carry CommonContext or a source Eval.
In particular, nesting can overwrite the sibling still held in slot five.
The fixed ABI reserves slots 0–6, and the A provider's reservation premises
must be re-established separately at every entry. An actual general nested
compiler needs register renaming, save/restore, or a stricter typing/layout
subset. Placement alone does not solve this ownership/register issue.

The independent A `EntryProvider` and B `FinishResult` remain unresolved
here. No inhabitant is assumed. To obtain a full body theorem, integration
must supply valid boundaries and typing; source Eval constructors; literal,
Nil, variable, and constructor leaf certificates with all Safe/Budget and
freshness premises; live result representation; pending-shell ownership and
executable finish placement; and a continuation/return ABI. The generic
induction step remains an explicit argument until those are proved. This
work deliberately does not manufacture a circular body provider.

To use A without changing its contract, a CaseInput must use the prefix and
suffix from its Placement, the same fragment bodies/src, and the required
boundary/PC evidence. Then `Placement.program` identifies its `i.program`
with p. Existing Transfer, BodyResult, and FinishResult may be transported
along that equality, but all their resource premises must still be proved.

After #201 lands, replay the contract commit and this C commit onto the
resulting main as appropriate; do not replay the copied prerequisites.
Shared CI integration remains a separate change. No merge is performed.

## Validation result

Lean 4.34.1: dedicated check passed (124 build jobs, warnings treated as
errors), followed by a fresh invocation of the check module. All 14 audited
theorems depend only on `propext`, `Quot.sound`, and/or `Classical.choice`.
No proof holes or global axioms were introduced. `git diff --check` passed.
The full shared `check.sh` was not run; no shared targets were changed.
