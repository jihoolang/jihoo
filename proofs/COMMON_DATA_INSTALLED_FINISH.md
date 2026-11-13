# Installed pending-shell finish

Base: `8ac8db21064bd1ec7cdb353d29c4e1c42340774a`.
The original contribution added only new modules. The integration now registers
these modules and checks in the root, aggregate audit and existing CI check chain.
The shared contracts remain unchanged.

`CommonDataInstalledFinish.installed_execution` constructs the existing
`CommonDataBranchFinish.FinishExecution` from an installed free instruction,
valid boundary, pending-head equality, stack bound and a unit scratch value.
It does not assume FinishExecution, a target walk, a release result, or final
validity. The walk is derived from the actual free rule and pending authority.

`Site` states every placement assumption: the current function is in the same
program, fetch is exactly a direct-copy free, no call/return override applies,
the direct destination is unit-typed and in bounds, the continuation block is
in bounds, and the operand local contains the pending shell's base pointer.
Children are never loaded. Execution takes one tick, keeps the function and
suspended stack, jumps to the supplied continuation at index zero, changes only
the destination local and shell heap object, and emits exactly one free event.
The continuation is reached, not executed or certified safe.

## Scratch and result contract

The original FinishExecution demands equality of all locals, so it needs the
old scratch to be unit. The regression proves this contract impossible when
scratch changes from i64 123 to unit.

`LiveFinishExecution` records equality only at active lexical bindings and the
explicit result slot. `installed_live_execution` constructs it with the existing
`Reserved ctx slots [dest]` convention and a separate `resultSlot != dest`
condition. Every active alias is covered, including scalar, nat, data and Buffer
bindings; dead and ghost slots may overlap scratch. Result preservation is
required even when the result is absent from the lexical map. No assumption
that all other array entries are covered by the lexical context is needed.

`live_finish_result` produces the unchanged frozen FinishResult interface;
`installed_body_finish` composes with an explicit BodyResult in the identical
program and exact boundary. Source evaluation, typing, ownership postcondition
and body execution remain BodyResult obligations. `live_result_preserved`
transports the body's scalar or data result representation explicitly.

Non-unit scratch is valid under this model's Boundary.Valid, which constrains
active bindings rather than every local's runtime type. It does not establish
whole-frame runtime type consistency: a future invariant requiring every
unit-declared slot to hold unit would rule out the i64 scratch example. Neither
result completeness nor general body lowering/native correctness is claimed.

## Regression coverage

`CommonDataInstalledFinishChecks` constructs a closed valid boundary from the
existing Case-entry/child-drop fixture: one shell child is dead, retained boxed
Nil is the live result, a two-element Buffer has payload 42, a suspended caller
is present, and the target reservation frame includes an absent external ID.
It constructs original unit-scratch FinishExecution, arbitrary-value scratch
LiveFinishExecution, final validity, and actual FinishResult inhabitants.
Independent reduction checks cover exact event, continuation/index, callers,
changed scratch, live result box, stale child pointer and Buffer payload.
Negative checks reject all-locals equality for non-unit scratch, a scratch/live
binding collision, a scratch/result collision and insufficient stack limit.
The generic context theorem also supports arbitrary remaining pending shells.

Run from `proofs` with Lean 4.34.1:

```
lake build Jihoo.CommonDataInstalledFinishChecks
lake build Jihoo.CommonDataBranchFinishChecks Jihoo.CommonCaseIntegration
```

The new checks print axioms for the certificate constructors, context/result
transport, body composition and concrete inhabitants. No proof placeholders or
new axioms are used. Root import/audit/CI wiring is supplied by this integration; run
`bash proofs/check-literal-finish.sh` for its dedicated audit.

Validation completed with the combined three-target command above: 134 build
jobs succeeded on the isolated base checkout. Printed dependencies are limited
to Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`
or project-specific axioms occur in the new certificate theorem dependencies.
