# Enclosing source Case with explicit child consumption

Base: `38239d84f8a332b716770891cd067b9311b7b708`.
Branch: `codex/case-source-consumption`.

Only two new Lean modules and this note are added. Shared CI, existing proof
modules, and compiler code are unchanged. Nothing is published.

## Results

`CommonCaseSourceConsumption.graph n` extends the earlier five-node
left-drop/right-drop/literal shape with an actual binary source Case, scalar
motive, two branch lambdas, and a Tree-to-scalar entry signature.
`typed` proves source typing for one data capability and no buffer inventory.
`total` derives source evaluation and allocation accounting, without assuming
source evaluation, target execution, or a body result certificate.
`tree_released` and `frame_survives` apply to every observed scalar run.

Exact premises of the generic totality theorem:

- `n < 2^63`;
- agreement of `caps [tree] []`, lexical context `.data 0 :: ctx`, and `env`;
- buffer layout for empty owners and sizes;
- valid initial heap;
- ownership of the whole tree footprint appended to the ambient frame;
- stored fields representing the inventory.

The lexical tail is arbitrary only subject to agreement; this is not arbitrary
extra owned inventory. Ownership includes separation, so the ambient frame
cannot overlap the tree. The release and survival theorems additionally take an
observed scalar run and membership in the tree footprint or frame respectively.
No global axioms were introduced.

## Checked examples

- `checked_entry`: graph 7 passes restricted source/family validation and the
  Tree-to-scalar CheckedEntry judgment.
- `node_run`: direct source Case/drop/drop/literal derivation for the existing
  closed fixture, returning scalar 7 and freeing source shell 7.
- `nil_run`: direct Nil branch derivation (operationally valid for any n;
  source typing still requires the integer bound).
- `recursive_run` / `recursive_accounted`: real nonempty children release source
  identities 1,2,3 before parent 0, preserving frame [4,5,6].
- `closed_connection`: source typing, actual enclosing source evaluation to
  `done.source`, exact 24-tick target walk to `done.target`, and target scalar 7
  in local 1. Initial source state/environment are those of the target fixture.
- `node_run_unique`: every source run from that fixture has the derived result,
  trace, and final state.
- `unconsumed_literal_rejected`: even logical Nil children cannot be silently
  discarded from the two-capability Node body inventory.

## Validation

Lean 4.34.1 checked both new modules, producing local `.olean` files. The
existing `CommonCaseChildTransferChecks` module was also compiled locally.
Unchanged dependencies were reused from the base worktree's build cache; this
was a targeted check, not a clean whole-library rebuild. Reproduction with a
configured toolchain from `proofs/`:

```
lake build Jihoo.CommonCaseSourceConsumption Jihoo.CommonCaseSourceConsumptionChecks
```

All new exported theorem axiom audits contain only Lean's standard `propext`,
`Classical.choice`, and/or `Quot.sound`; no `sorryAx` or project axioms occur.
Both new Lean files contain no `sorry`, `admit`, or axiom declarations.

## Remaining gaps

This is a hand-written restricted source graph, not a production frontend
export or proof that the compiler emits the target fixture. The closed
connection pairs independently derived executions at matching state/result
endpoints; it is not a parametric simulation theorem. Source trace [.free 7]
and target trace [.free 1,.free 2,.free 3] differ intentionally because target
Nil children are boxed. The fixture has an administrative target ghost slot;
the source Case introduces none, so context identity is not claimed. Generic
source totality supports arbitrary finite trees, but generic exact target
execution, general branch lowering, and a trace-refinement relation remain
outside this increment.
