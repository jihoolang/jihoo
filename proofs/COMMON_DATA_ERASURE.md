# Common Data source execution and ghost slots

`Jihoo/CommonDataErasure.lean` connects the **existing**
`CommonDataSourceRules.Typing` and `CommonDataSourceExecution.Eval` judgments to
an independent, tree-shaped target syntax with compact runtime variable indices.
It does not extend `SymbolicMirLoweringTotality`.

## Statements and assumptions

- `Lower g slots term target` is a structural lowering certificate: source node
  shapes, source binder indices, slot-map positions, and recursively lowered
  subterms. No source or target execution occurs in its constructors.
- `Env slots source compacted` removes only actual `.ghost` values. Kept values
  are equal. Dead ownership aliases are retained: erasing them requires a
  different simulation. The mask is static, independent of runtime values.
- `Env.lookup` proves lookup preservation; `position_injective` proves distinct
  surviving lexical binders cannot alias because of compaction.
- `Env.bind` / `Env.enter` prove the Case binder correspondence. Both runtime
  fields survive, newest first: right then left. The mask gains two `true`
  entries. The existing source Case has **zero newly inserted ghost binders**;
  this result removes pre-existing lexical ghost holes, not dependent constructor
  telescopes. Drop introduces no binder and keeps the mask unchanged.
- `Lower.preserves` maps **every existing source run** to target execution with
  identical result, event trace, and final heap/store. Target `Eval` has no source
  graph, source environment, source evaluation or typing premises.
- `total_accounted` derives target execution existence and trace accounting from
  existing source typing, tree-count agreement, lexical capability agreement,
  Buffer layout, initial heap validity, ownership including an arbitrary frame,
  and field representation. It also requires structural `Lower` and `Env`
  certificates. It does **not** assume successful source or target execution:
  source existence follows from `CommonDataSourceExecution.total_accounted`.

## Exact supported fragment

Literal, empty binary Data, Data variable, binary construction from variables,
Data application (including source split/captured typing), recursive Drop,
explicit Buffer release, and arbitrarily nested constant-result binary Case.

Both source `allocate` and `bufferLet` rules are excluded. In particular, even
pure I64 application through `SizedCoreExecution` is outside this fragment. The
term “no Buffer allocation” alone would not describe the restriction accurately.
There is no theorem that **every** CommonData typed term has a `Lower`
certificate, no executable lowering function, and no backward simulation or
native-target refinement claim.

The shared Core/native scope remains the existing restricted monomorphic binary
family with constant scalar/Data motives. Target heap operations (`allocate`,
`Destroy`, `finish`, and Buffer release) use the existing abstract common model.
This is not a proof of production `core_lower.jh`, native memory layout, MIR
execution, arbitrary inductives/dependent motives, or general ghost erasure in
embedded Core computations.

## Regression and integration

`CommonDataErasureChecks.lean` derives a nested Case/Drop example from the existing
source-execution fixture, changing only its outer scrutinee to index 1. Input
`[ghost, tree, ghost]` becomes `[tree]`. It checks both non-circular typed target
existence and the exact existing nested release trace, plus Case slot shifts,
rejection of erasing Data, and axiom dependencies.

The independent review confirmed the structural/non-circular boundary and binder
order, and requested the explicit exclusion of scalar Core lets and genuine
false-mask regressions; both are reflected here.

No existing Typing/SourceRules, aggregate imports, audit manifests, or CI files
are changed. Follow-up integration should:

1. Rebase against the concurrent Buffer-producer typing changes and rerun the
   targeted module. This implementation does not pattern-match on Typing, so its
   non-circular totality corollary depends only on the existing public theorem.
2. Prove a compact Core environment/graph simulation before admitting either
   `SizedCoreExecution` island; do not add successful Core execution as a lowering
   premise. Cover arbitrary Buffer producers under the new rules.
3. Add canonical mask construction and structural lowering totality for a named
   source fragment, then connect to the common Core/native boundary.
4. Coordinate aggregate imports, recursive axiom audit and CI registration before
   claiming default-build coverage. Run explicitly with
   `cd proofs && lake build Jihoo.CommonDataErasureChecks` until then.
