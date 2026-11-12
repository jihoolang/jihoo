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
The shared audit registers the same 51 entries and totals 3444 on main
`1dda9513`. Both architecture Test jobs and Common Core backward proofs run the
dedicated check. #197/#198 branches and worktrees remain unchanged.

## Integration order and audit registration

This candidate is based directly on main `1dda9513`, plus the isolated constructor
commit `4cab93bd`; it has no dependency on #197 or #198. Keep #197 pending its
existing approval. Any merge order must preserve the union of imports, audit
entries and CI steps, then rerun the complete and dedicated checks on that exact
combined tree. Never resolve the audit count by choosing one side: baseline
3393 + this candidate 51 = 3444; with #197 (+45) = 3489; with #198 (+61) = 3505;
with both = 3550. Recompute unique `#print axioms` entries if either PR changes.
These counts are registration arithmetic, not claims of a validated combined
#197/#198 tree. Shared `Jihoo.lean`, `Audit.lean`, `check.sh`, and workflow append
conflicts need explicit union resolution. No merge is authorized by passing this
candidate alone.
