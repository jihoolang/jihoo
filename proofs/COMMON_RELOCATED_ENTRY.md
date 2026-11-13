# Relocated common Case entry

Based on shared contract commit `4a701387` on
`proof/common-composition-contract`. This includes the unmerged #201
prerequisites; it is not a main-branch result.

`Jihoo.CommonDataCaseRelocatedContext.entryProvider` inhabits the unchanged
`CommonCompositionContract.EntryProvider`. The separate `node` and `nil`
theorems prove the exact sourceEnter equations and Transfer certificates:
11 ticks / no target events for Node; 5 ticks / one boxed free for Nil.
The output boundaries are the contract's fully defined nodeOut/nilOut.

All assumptions are retained: exact installed linked program and body blocks,
function zero at copied-entry PC pre.size+6, selected head capability and
selected local, seven or more locals, valid common ownership context, exact
head image, stack bound, and reservations for every live binding. Node reserves
[0,1,2,3,4,5] on the original context. Nil reserves [0,1,6] after removeHead.
Node uses context lookup, copied execution, local framing and open_case. Nil
uses lookup, copied execution, separated destruction and local framing.
No interface mismatch or strengthening of the frozen provider is needed.

Tests instantiate nonzero placement, lexical index one, source local eleven,
parent aliases, a retained Nil/Buffer/scalar/natural, an out-of-range ghost
slot and a suspended caller. A subsequent relocated Nil entry retains the
pending parent and remaining resources. Active Node slot zero is explicitly
rejected by the conservative reservation. The generic theorem covers arbitrary
pending lists and ambient frames; these are preserved without new premises.

Run `bash proofs/check-common-data-case-relocated-context.sh` with Lean 4.34.1
and lake on PATH. The dedicated check builds the module and fixtures with
warnings as errors and audits eight named results for proof axioms.

Integration obligations remain: replay only the contract and new proof commits
after #201 lands, adapting to its final API if necessary. Add root imports/CI
only in a separately authorized integration. Nothing here proves branch-body
execution, pending-shell finish, nested common placement, source/target trace
correspondence, return ABI, production lowering or general compiler correctness.
The linked layout still embeds exactly two branch blocks in function zero;
B and C remain separate obligations. No merge is performed.

Validation: clean dependency/module build passed (123 jobs); dedicated fixture
build passed (128 jobs) with warnings as errors; all eight audited results use
only propext, Classical.choice and/or Quot.sound. No sorry, admit or new axiom
is present. git diff --check passed. The full shared check.sh was not run;
shared build targets, imports and audit files are unchanged.
