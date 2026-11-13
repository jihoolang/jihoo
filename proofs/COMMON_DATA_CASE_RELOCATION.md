# Independent Case CFG relocation and slot separation

Base: `2bfdcb15`; independent branch `work/case-cfg-relocation`.
Integrated on main `1dda9513` with the independent entry commit `2bfdcb15`
and relocation commit `fc13ba4c`. Shared imports and audits now register both
modules and their checks. Pending #197 context files are unchanged.

## Contract

`linked pre post nb cb src` places the original five blocks at `pre.size`.
Every destination in all five blocks (including supplied body blocks) is
translated by that offset. Body destinations must use fragment-relative
addresses. Prefix and suffix blocks already use absolute addresses.
`relocated_lookup` covers blocks 0–4 and `relocate_edges` covers every
terminator constructor and switch default.

The old default 5 now names an explicit `assert false` block. Arbitrary
appended code cannot make this failure instruction succeed (`failure_tick`).
`invalid_dispatch` reaches that block for tags other than 0/1. Failure is
observed one tick later than the old out-of-bounds switch: this is not a
same-fuel equivalence for invalid inputs. The counterexample
`append_changes_failure` shows why retaining the old out-of-bounds argument
would be unsound.

Direct entry requires the root in slot 0 and costs Nil 3 / Node 9 ticks.
An optional entry at offset 6 copies `src` to slot 0 and jumps to entry:
assignment 1 + goto 1, hence Nil 5 / Node 11 ticks. `nil_copied_entry` and
`node_copied_entry` prove the exact results under sufficient fuel, space
(at least seven value slots), and the independent stack limit.
`runPrefix_sound`, `BoundedPrefix.steps`, and `BoundedPrefix.execute`
connect these results to actual transitions and prefix-plus-tail fuel.
A tail's success must be independently established; no body is executed by
an entry theorem.

`Apart live writes` is an explicit allocator obligation. Node writes
{1,2,3,4,5}; Nil writes {1,6}. Copying additionally reserves slot 0.
`node_live`, `nil_live`, `copied_node_live`, `copied_nil_live` preserve every
retained slot under that obligation, including out-of-range lookups.
The final state equations preserve all suspended frames and the complete
stack, and reset the active instruction index at the relocated body.
Node leaves the heap unchanged. Nil retires only the root; the existing
`empty_case_total` theorem supplies preservation of other heap objects.
`binder_order` connects source newest bindings [right,left] to slots [5,4].
`node_entry` and `nil_entry` connect the source entry operation and related
heap layouts to copied, relocated target entry.

## Counterexamples and checks

The checks module uses kernel-evaluated examples for unsafe append,
explicit failure with nonempty prefix/suffix, swapped child slots, live
slot collisions (4, 6, and copy slot 0), copied entry with nonempty stack,
insufficient fuel, and insufficient stack limit. It prints theorem axioms.

## Integration boundary and follow-up

This is a fixed-slot ABI lemma, not an arbitrary local-slot renaming or
whole-program linking theorem. The linked function retains exactly seven
type slots, has no call-exit overrides, and occupies function index 0.
Extra value slots can be read/preserved by entry, but their type declarations
and surrounding arbitrary code are not certified here.

#197 context integration, branch-body safety, native cast and reuse remain
unproved. Follow-up integration must allocate/discharge `Apart`, supply the
source-to-slot connection in [5,4] order, preserve the pending parent shell
and revoke its source aliases, extend the actual locals/type table and exits,
and prove the body/finish continuation separately. Do not merge or change
#197 as part of this work.

## Independent review

A separate read-only reviewer found no mathematical counterexample in the
initial relocation/entry definitions, identified the fixed type table and
empty-exits limitation, and requested combined copied-slot preservation,
edge laws, and explicit negative checks. Those additions are included.
Lean validation is recorded in the completion report; the reviewer did not
claim to have run Lean independently.

## Validation result

Targeted Lean 4.34.1 compilation passed for both new modules. Dependencies
were reused read-only from the unchanged base worktree's compiled cache;
new output was stored only in this worktree. The checks module reported only
`propext`, `Classical.choice`, and `Quot.sound` (subsets vary by theorem),
with no `sorryAx`. No `sorry` or `admit` is present in either module.

For a normal checkout, from `proofs/`, run:

```sh
lake build Jihoo.CommonDataCaseRelocation Jihoo.CommonDataCaseRelocationChecks
```

Final independent read-only review covered all three new files and found
no blocking semantic issue. Its requested axiom checks for the new joint
entry and fuel soundness theorems are included and passed. This is targeted
Lean validation, not a full repository or native backend test run.
