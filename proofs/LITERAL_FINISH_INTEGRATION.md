# Literal and installed finish integration

Base: main `8ac8db21064bd1ec7cdb353d29c4e1c42340774a`.
Replayed only `d28b900726ea5e11f58ba5b75731df50e57f6b91` and
`0efd250fd54a0b3a12297a0f66592e44824c0a92` in an isolated worktree.

## What is proved

The literal constructor proves source typing and evaluation, a two-tick walk
in the supplied installed program, ownership postcondition and result-local
representation. It requires a signed-range natural literal, valid boundary,
empty images/Buffers/sizes, a fresh result local, exact assignment/goto block,
no exit override, index zero, an i64-declared in-bounds destination, an existing
continuation and sufficient stack budget. Other locals, heap and callers are
preserved. Nonempty pending/ambient frames and lexical contexts are allowed.

Installed finish derives a one-tick free from Site and pending authority.
The original all-locals certificate requires old unit scratch. Live finish
instead requires exclusion of scratch from every active lexical binding and
from the result local. It preserves only the needed local equalities and
constructs the frozen FinishResult. The existing installed_body_finish theorem
still takes an explicit BodyResult; this is not hidden or discharged generally.

CommonLiteralFinishChecks.combined has no premises, implicit certificate
parameters or provider assumptions. It constructs both certificates for one
program: literal 7 in slot 1, then free shell target 3 through slot 2, writing
unit to scratch slot 3. Its final Transfer is exactly three ticks and [free 3].
Separate kernel proofs establish the walk by reduction, final validity and
result preservation. It retains scalar 77, a ghost out-of-bounds slot, nonempty
ambient frames and a suspended caller. The old scratch is i64 123; Boundary.Valid
does not require every non-live local to match its declared runtime type.
The final continuation is reached, not executed or proved to return.

## Why this is not a full one-level Case theorem

The frozen Node entry produces l :: r :: rest images. The literal constructor
requires images = []. The audited node_inventory_nonempty theorem proves this
mismatch for every CaseInput and both children, even boxed Nil children.
A full Node-branch wrapper needs proved child consumption and the corresponding
source typing/evaluation before using this leaf constructor. Replacing that work
with an assumed BodyResult would only reproduce the previous conditional API.
Nil entry can consume the last boxed image, but does not itself create a pending
shell requiring Node finish, and does not establish a complete two-branch Case
source theorem. This integration therefore claims a closed literal/free seam,
not a full Case wrapper. It neither touches the separate register-renaming branch
nor establishes recursive compilation, native lowering, a return ABI, general
compiler correctness, or equality of source and target traces.

## Audit and validation

All preexisting root imports, 3,649 aggregate audit entries, the 60-entry Case
audit, dedicated scripts and CI workflows are preserved. All five new modules
are imported. AuditLiteralFinish enumerates 36 additional public named theorems,
including the closed combined type and the inventory obstruction. The aggregate
now expects 3,685 elaborated dependency reports. The private bindings helper is
covered transitively by literal. Anonymous regression examples are compiled
with warnings as errors. The allowed axioms remain only propext, Quot.sound and
Classical.choice. The new dedicated script is appended to the existing Case
check chain, already run in both CI workflows; the Nix aggregate fileset includes
all Jihoo modules and the extended Audit.lean without changes.

Validation commands with pinned Lean 4.34.1:

```sh
bash proofs/check-literal-finish.sh
bash proofs/check-common-case-composition.sh
bash proofs/check.sh
python3 scripts/check_nix_sources.py --offline --system x86_64-linux
```

Builds use the fresh integration worktree, with no copied .lake artifacts.

Completed validation: dedicated audit **36**, preserved Case audit **60**, full
aggregate audit **3,685**, all passing with warnings as errors and only the
allowlisted axioms. The full script also passed every generated-fixture diff.
The clean root build completed 375 jobs. Source isolation passed all 12 mutations
for x86_64-linux using the existing cached Nix runtime (`NP_LOCATION` set to the
workspace `.nix-runtime`); the default runtime attempt lacked that cache and
failed downloading nixpkgs. No Nix derivation build is claimed. `git diff --check`
passed. The displayed `#check @combined` has no theorem premises.
