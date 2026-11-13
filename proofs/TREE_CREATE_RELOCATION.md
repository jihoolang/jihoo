# Relocatable Tree constructor prefixes

This is an in-function CFG fragment, not a complete compiler or native ABI.
`TreeCreateRelocation.entry` and `build` emit two blocks. `Placement` states that
they are installed at arbitrary distinct entry/work/continuation block indices
in an otherwise arbitrary caller function. Only entry/work exits must be absent;
the continuation body and exit remain unconstrained.

`Slots` selects arbitrary result, address scratch, word scratch, child destination,
and temporary indices. `Safe` requires the seven destinations to be pairwise
distinct, in bounds, and correctly typed. The two pointer temporaries must also
be distinct from both source indices. Child sources may otherwise coincide with
each other, swap the child destinations, or overlap result/address scratch.

A Node executes four real copies: save left, save right, install left, install
right. Both original operands are captured before either child destination or
constructor scratch can destroy them. Malloc then runs, followed by seven
initialization statements and goto: exactly **13 transitions**. Nil executes
malloc, one tag store and goto: exactly **3 transitions**. Prefix fuel is consumed
normally; `node_fuel`/`nil_fuel` prove short-fuel failure and add these counts to a
separately assumed successful continuation. No pointer-return ABI is asserted.

The executable prefix theorems assume installed blocks, valid local placement,
initial child values, and actual object/cell budgets. They derive allocation and
store success. `node_total` additionally requires the existing source validity,
representation, joint ownership, target layout and child separation premises.
Only under these stronger premises does construction produce a related owned
Tree. Raw pointer transport can succeed for equal, dangling, non-root or null
children; kernel checks explicitly cover these cases. The general `node_prefix`
theorem transports root pointers; null and nonzero offsets are concrete checks
only. Such success alone is not
an ownership or valid-Tree theorem.

`locals_preserved` covers every caller local outside the seven writable slots;
Nil changes only result. `stack_preserved` keeps the entire suspended caller stack.
`heap_preserved` keeps every old heap object. Retained Tree/buffer relations use
the existing allocation/frame lemmas. `node_result_pointer` and
`nil_result_pointer` expose the result at the selected local, without claiming a
return convention.

These fragments enter an existing frame with explicit operand hypotheses. The
old constructor body's `parameters=[]` does not bind child arguments through
`ReferenceCalls.enter`. A regression uses valid caller return placement and two
valid operands to check this parameter mismatch directly.

Run the dedicated checks from `proofs` with `./check-tree-create-relocation.sh`.
It pins the repository's Lean version, rejects warnings, and checks all 51 constructor and relocation
audit entries against Lean's standard logical-axiom allowlist. The swapped-child
fixture explicitly proves `Safe` and `Placement`, as well as checking execution.
The shared audit registers the same 51 entries. Both architecture Test jobs and
Common Core backward proofs run the dedicated check alongside the Case check.

## Integration and audit registration

PR #199 now incorporates main `f0eacaa3051c5f9caaed3a403846515ba8a55465`,
including the merged target-context (#197) and Case CFG/relocation (#198) proofs.
The integration preserves the exact union of imports, audit entries and CI steps.
All proof modules from both parents are unchanged.

The shared audit contains **3550 unique entries**: baseline 3393, target context
45, Case CFG/relocation 61, and Tree constructor/relocation 51 (25 + 26).
The 245 shared imports are also unique and form the exact union of both parents.
`check.sh` requires 3550 elaborated audit results and accepts only `propext`,
`Classical.choice`, and `Quot.sound`. Run the complete and dedicated checks on
this combined tree; registration counts alone are not proof-validation evidence.
Passing checks does not authorize merging the PR.
