# Bidirectional executable common erasure

`Jihoo.CommonDataCoreBackward` extends the #188 executable compiler without
changing its target evaluator, source typing, or accepted lowering grammar.
`Lower.backward` reconstructs source execution from a lowering certificate,
a `Bridge`, and target execution alone. The returned value, entire common event
trace, and final state are identical. Scalar and Buffer islands use
`SizedErasure.Erases.backward`, retaining the complete sized state before the
existing event projection.

`Bridge.enter_backward` destructs target entry directly: lookup correspondence
recovers the source reference, and the same live heap entry and cell produce
the source child bindings. No forward simulation or successful source execution
is used to justify Case entry. `Lower.adequate` and `compileTarget_adequate`
combine backward simulation with existing forward preservation.

`compileTarget_every_run_accounted` applies symbolic source
`Typing.every_run_accounted` to the reconstructed run. It proves safe heap
steps, final validity and the existing per-identity Data/Buffer accounting for
every target run under the unchanged closing, layout, ownership and field
invariants. `compile_closed_adequate_accounted` combines #188 structural
completeness with these results: a single target compiles at every fuel above
a finite bound, has exact bidirectional adequacy, has a successful execution,
and every execution from the supplied initial state is safe and accounted.
Compilation fuel bounds structural traversal, not execution steps.

## Verification and scope

The dedicated checks construct a target node Case execution independently and
reflect it through a compiler result with an erased ghost slot. They also cover
the empty branch, scalar and owner Core islands, and the dynamic producer fixture. All new public theorem
axioms are checked by `CheckCommonCoreBackward.lean`, central `Audit.lean`,
and the recursive field audit. The shared `Jihoo` import includes these checks,
so both full CI architectures validate the new results.
Run `lake build --wfail Jihoo.CommonDataCoreBackwardChecks` and
`lake env lean -DwarningAsError=true CheckCommonCoreBackward.lean`.

The scope remains fixed binary Tree, constant common motives, and the existing
symbolic Core islands. This does not prove CommonData-to-MIR or native compiler
refinement, general dependent Data, or termination of arbitrary cyclic graphs.
No target determinism theorem is needed for backward simulation.

The separately reviewed `CommonDataCoreDeterminism` module is included unchanged.
It proves uniqueness of terminating target runs without source, lowering, or
typing assumptions. Its public theorem is included in the dedicated 16-entry
axiom audit. Run `bash proofs/check-common-core-backward.sh` from the repository
root; the dedicated GitHub workflow runs the same check.
