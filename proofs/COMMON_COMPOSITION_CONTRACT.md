# Conditional common composition contract

Base: main b5ed6688855f46076523b0c6f6224222a1dcaa81 (#200).
Prerequisite: #201 proof tree from 890f89c8 (same initial tree as published
ded203d1), followed by da033fcf. These commits are copied onto this separate
branch. The ongoing codex/pr201-integrated worktree is read-only to this work.
No shared audit, root imports, workflow, or check.sh is changed.

The interface is `Jihoo.CommonCompositionContract`. Run
`bash proofs/check-common-composition-contract.sh` with Lean 4.34.1 on PATH.
This is a conditional contract, not compiler correctness or completed A/B/C.

## Frozen shared types

`Boundary` contains images, source/target Buffer IDs, Buffer sizes, pending
shells, both ambient frames, lexical context/environment/slots, source state,
and the complete target State. `Boundary.Valid` is exactly CommonContext.
`Transfer p limit ticks a b events` contains the executable bounded `walk`
equation, validity preservation, and equality of suspended caller stacks and
both ambient frames. It does not assert validity of an invalid input.
The actual input validity must be supplied at the outer call.

`Transfer.then` adds ticks and appends target events. It requires the same
program, limit, and exact middle boundary. `Transfer.steps` exports actual
ReferenceCalls.Steps. There are no implicit typeclass instances, global
axioms, assumed provider inhabitants, or erased proof obligations.

## A: relocated Case entry to CommonContext

Own a new `CommonDataCaseRelocatedContext.lean`; import the contract and prove
an explicit `EntryProvider` value. Do not change B/C or shared build files.
Inputs: CaseInput's exact pre/post arrays, body blocks, source index/local,
ghost slots, selected head capability, slot lookup, function-zero copied-entry
PC at pre.size+6, at least seven locals, valid input context, head-image
shape, stack bound, and reservation of every live lexical binding.
Node conservatively reserves [0,1,2,3,4,5] on the original context. Nil reserves
[0,1,6] on removeHead. Thus an active Node input in slot zero fails this first
copied-entry contract; a later direct-entry variant needs its own contract.
Outputs: exact sourceEnter equation and Transfer of 11 ticks/[] for Node,
5 ticks/[free j] for Nil. `nodeOut` and `nilOut` are fully defined, not selected
by the provider. Node binds right/left to slots 5/4, retires parent aliases,
and prepends the parent shell. Nil removes all aliases and releases its box.
Buffers, sizes, ambient frames and suspended callers remain unchanged.
Use #200 context lookup/open_case/reframe plus relocation copy/frame lemmas.
Tests should include nonzero relocation, arbitrary selected local, aliases,
retained Buffer/scalars/naturals, pending shells and suspended callers.

## B: branch body and pending-shell finish

Own `CommonDataBranchFinish.lean` and its checks. Develop the shell-finish
lemma independently from A by accepting a valid arbitrary boundary.
`BodyResult` carries source Typing with inventory count and sizes, actual
source Eval, Transfer, source result ownership including all pending shells,
and target result-local representation. A data result names an actual image
in the final inventory; scalar results name the i64 local. Source and target
event lists are separate intentionally; no trace correspondence is claimed.
`FinishResult` requires a particular pending head and tail, exact source
finish, exact target singleton free event, unchanged images/Buffers/sizes/
lexical layout, preservation of the result local, the Transfer and final Post.
Its ticks and final machine state are explicit indices, not guessed constants.
A concrete finish instruction sequence still needs a placement/write-set
contract and a proof that it executes in p; supplying FinishResult IS that
obligation, not a substitute for proving it. Derive source free validity from
CommonData.Post.finish and target release from the pending shell authority.
Test stale child pointers, live result, nested pending parents, framed buffers
and rejection of an aliased pending/result owner.

## C: restricted structural composition

Own `CommonDataRestrictedComposition.lean` and checks. Supported admits only
signed literals, Nil, data variables, Node of two variables, and binary
constant-motive Case with a variable scrutinee. Typing is separate and mandatory
in BodyResult; Supported does not grant resource authority. Case records both
nil < term and unwrapped node body < term explicitly. Recursive calls must use
these inequalities, not fuel or the outer Case hypothesis. The provided
`supported_induction` is Nat strong induction; P and its step are explicit
parameters. It is an induction utility, not a hidden semantics theorem.

C must define an installation/placement witness for ONE final program before
specializing P to its body theorem. Establish leaf certificates (constructor
ones adapt #201's 13/3-tick prefixes and preserve its Safe/Budget/freshness
premises). At Case, obtain A's entry, recurse only on the selected smaller
body, and apply B's finish only for Node. `node_pipeline` already checks the
11+n+m seam and event concatenation. Supply source emptyCase/nodeCase Eval
constructors to lift the branch Eval to the outer expression. Nil uses
Transfer.then with 5+n ticks and its boxed-free prefix.

Critical limitation: A's existing linked layout embeds exactly two body
blocks and fixes function zero. General nested fragments cannot simply replace
p with a newly linked program mid-proof. C must prove a common embedding/
placement law or narrow its layout witness to bodies that fit the installed
program. That law is NOT supplied here. Do not claim all Supported terms have
a lowering until this obligation is solved. No return ABI, production emitter,
allocation strategy, target/source event simulation, Buffer operations,
applications, data-let, Drop, general Core, or dependent motives are covered.

## Integration and review

The checks instantiate A/B wiring solely as explicit theorem arguments,
exercise a real zero-step interpreter seam twice, admit a concrete literal and
reject opaque syntax. Eight named theorems are axiom audited. This checks API
compatibility, not nontrivial inhabitants of EntryProvider or FinishResult.
After #201 lands, replay only the contract commit onto the resulting main;
do not replay the two copied prerequisite commits. Add shared CI imports only
in a separately authorized integration change. No merge is performed here.

Validation on this branch: Lean 4.34.1 clean dependency build passed (122
jobs), dedicated checks passed (123 jobs), all eight audited theorems use only
propext and/or Quot.sound, and git diff --check passed. No global proof holes
or axioms were introduced. The full shared check.sh was not run because this
change adds only separately invoked modules and does not alter shared targets.
