# CommonData scalar and direct Buffer erasure

`Jihoo/CommonDataBufferErasure.lean` extends the structural fragment of #184
in a separate namespace and file. It reuses `CommonDataErasure.Slots`,
`position`, `Env`, lookup injectivity, and Case binder correspondence.
Shared typing is unchanged. Both new modules are registered in the aggregate
imports and the central and recursive axiom audits.

## Supported execution

In addition to #184's structural constructors, the new lowering admits:

- scalar `bufferLet` whose Core argument is an integer literal or scalar variable;
- direct Buffer allocation whose length is a natural literal and initializer is
  an integer literal or scalar variable;
- arbitrary nesting of these binders with Data application, Case, Drop, and Free.

`ScalarLower` and `Lower` contain only source shapes, slot positions and recursive
lowering certificates. They contain no successful execution or safety premises.
`ScalarEval` and target `Eval` have no source graph, source typing, or source run.
A scalar or Buffer binder prepends `true`; existing ghost holes shift with the
source environment. Only actual ghost values disappear; stale ownership aliases
are retained. Core lookup commutes with projection and slot compaction.

`ScalarLower.preserves`, `ScalarLower.run`, and `natural_value` invert the existing
Core execution for these atoms. `Lower.preserves` covers every source run admitted
by the structural certificate, preserving the result, complete projected trace,
and exact final `CommonData.State` (heap payload, Buffer length map and Data cells).
The projected allocation event stores the initializer value, not the length.

`total_accounted` derives target execution from existing source typing, structural
lowering, environment agreement, initial ownership and layout/field validity.
It assumes no source or target execution. It preserves arbitrary ownership frames,
heap steps, final validity and `AccountedPost`. This is execution totality for
certified lowering, not a proof that every typed source has a lowering certificate.

## Regression and verification scope

`CommonDataBufferErasureChecks.lean` uses all bounded natural lengths, arbitrary
scalar inputs, arbitrary valid initial states and owned frames. Its source
`[ghost, scalar, ghost]` compacts to `[scalar]`, then performs scalar binding,
allocation and release. It separately checks structural lowering, existing typing,
non-circular totality, source execution, exact target execution, and preservation.
Local named `#print axioms` checks cover the new lemmas and regressions.

## Integration boundary

The implementation starts from #184 (`3e02d2c`) and is integrated onto main
`d1acb2113b1d1132bd971e5d5b61f091526e1ce1` after #185.
The new Buffer-producer typing rules and all shared audit changes must be retained.
Existing source totality is reused; there is no new typing axiom.

General producer bodies (including producer/consumer framing), scalar Core
applications or effectful scalar arguments, variable or computed lengths, and
borrow/lend islands are outside this lowering relation. They need compact Core
syntax plus simulations for their own binders and runtime natural environments.
#185 provides producer typing and accounting but does not itself provide erasure.

Integration adds all 14 named checks to both audits (3,100 central and 447
recursive entries) and registers the regression module in the recursive build.
The existing Nix proof checks exercise both suites on x86_64-linux and
aarch64-linux CI. This does not claim native/MIR refinement, arbitrary inductives,
or lowering totality for all typed terms.

## Independent review

A separate reviewer inspected the core simulation and authored the parameterized
regressions. The review checked exact allocation payload projection, unchanged
Data cells, full Buffer state equality, binder ordering, actual ghost removal,
Core lend-shape contradiction cases, and the absence of execution premises in
lowering or totality. No semantic blocker was found. Forward simulation is proved;
backward simulation and accounting for every arbitrary target run are not claimed.

## Completed targeted validation

On main `d1acb211`, Lean 4.34.1 completed 114 jobs with `--wfail`:

```sh
lake build Jihoo.CommonDataBufferErasureChecks Jihoo.CommonDataErasureChecks Jihoo.CommonDataBufferProducerChecks --wfail
```

All 14 new named axiom reports contain only `propext`, `Classical.choice` and
`Quot.sound` (or no axioms). There were no warnings or errors. `git diff --check`
passed. Full aggregate/Nix and two-architecture CI were not run for this change.
