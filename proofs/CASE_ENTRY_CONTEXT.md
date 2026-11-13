# Executed Case entry and common resource contexts

This extension starts from main `5780afe9` (including #197, #198, #199).
`CommonDataCaseCfg` already proves actual fixed-ABI execution to branch entry.
`CommonDataTargetContext` already describes lexical aliases separately from
ownership and proves abstract Node opening and destructive context updates.
`CommonDataCaseEntryContext` connects these interfaces without changing either.

`node_entry_context` derives source entry, a successful fuel-bounded nine-tick
run, its stack-bounded operational prefix, and a `CommonContext` at block 4.
Child pointer locals 4 and 5 come from executed field loads and provenance-word
conversions, not assumptions about initialized children. The new lexical order
is right then left; every old parent alias becomes dead. Parent authority moves
to a pending shell. The source state, target heap, buffer size layout, ambient
source/target frames, and suspended caller stack are preserved.

`nil_entry_context` derives source stuttering, a successful three-tick run
emitting exactly one target free, its bounded prefix, and a `CommonContext` at
block 3. Removing the Nil inventory head retires all its aliases. No source
object is freed. Retained resources, existing pending shells, frames and buffer
sizes survive. The proof reuses the context's destruction preservation theorem
with empty source destruction and a singleton target free; this does not execute
a Drop call or claim that a Case is compiled as such a call.

## Assumptions and limits

- The context supplies source validity, agreement, related resources, exclusive
  source ownership, and target separation across resources, pending shells and
  ambient frames. Target Nil boxes count in separation despite having no source
  owner. External target frame entries need not be live or present.
- The selected lexical alias must refer to inventory head 0 and map to ABI root
  local 0. This is a direct local connection, not arbitrary operand compilation.
- At least seven target locals, sufficient fuel (9/3), and an independent stack
  bound are required. Node writes locals 1–5; Nil writes 1 and 6.
- `Reserved` excludes active lexical locals from those destinations. Node uses
  the original context, conservatively excluding even soon-retired parent
  aliases; relaxing this to only surviving bindings is future work. Nil uses
  the context after head removal. Dead/ghost entries impose no local constraint.
  Root 0 and multiple aliases of it are allowed. Ghost slots may be out of bounds.
- Branch blocks are arbitrary and are not executed. The result is a bounded
  prefix and can be converted to `ReferenceCalls.Steps` using the existing
  `BoundedPrefix.steps` theorem. It does not prove branch bodies, pending-shell
  finishing, whole Case lowering, source typing extraction, production compiler
  correspondence, native pointer/cast correctness, or reuse.
- The bridge uses the fixed one-function ABI. Relocated Case proofs exist
  separately, but transferring this context theorem through relocation remains
  an integration obligation.

## Checks and later integration

Run from `proofs/`, with the pinned Lean toolchain:

```sh
lake build --wfail Jihoo.CommonDataCaseEntryContext Jihoo.CommonDataCaseEntryContextChecks
lake env lean -DwarningAsError=true AuditCommonDataCaseEntryContext.lean
```

The concrete fixtures instantiate both context theorems. Node begins with
poisoned children and retains Nil, Buffer, scalar/nat bindings, a ghost and a
suspended caller. Nil retains a Buffer/scalar and nonempty ambient frames.
A subsequent child Drop retains the pending shell after its child dies.
Negative proofs reject scalar/unit local collisions and overlapping target
resources; alias retirement is checked explicitly.

No changes are made to `Audit.lean`, `Jihoo.lean`, `check.sh`, or workflows.
Later integration should import the extension/checks into the shared root,
include these 18 declarations in the aggregate axiom audit and update its exact
count, and wire the dedicated audit into CI. No full branch or native correctness
claim follows from these checks.
