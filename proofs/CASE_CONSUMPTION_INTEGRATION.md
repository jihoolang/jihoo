# Case consumption integration

Local integration base: tested #203 commit
`3facf6fb2b2bba8f1e3c954c6c16a7aaf402bac4`, tree
`6cde919b1ad3879f1bc48ea35b8a810f3ee73b2c`.
The published #203 head `a3793e381b480af13c59b9a4a0ad6effe84c363b`
has that same tree. The separate local branch is
`codex/case-consumption-integration`; #203 is unchanged.

The three input commits already form a direct dependency chain on the tested
base, so their identities are retained without replay or conflict resolution:

1. `41415f06ddce0b1d40dd35a4b0eebc753d2d1c7b`: child consumption.
2. `38239d84f8a332b716770891cd067b9311b7b708`: exact child transfer.
3. `885df4be0e7c16abae6f4648a58abca7baf97316`: enclosing source Case.

## Build and audit integration

All six new modules are root imports. All 47 exported named theorems are
listed in both AuditCaseConsumption.lean and the aggregate Audit.lean,
raising the aggregate from 3,685 to 3,732. The existing Case check chain now
runs check-case-consumption.sh; its existing 60-entry composition audit and
36-entry literal/finish audit are preserved. Both existing CI workflows invoke
that chain. No workflow or Nix source-set expansion is necessary: the aggregate
already includes proofs/Jihoo and Audit.lean. The new dedicated audit runs from
the checkout through the same mechanism as the earlier dedicated audits.

## Assumptions and scope

The generic child body starts at a valid Node-body boundary with exactly two
child images, no buffers or sizes, and a Node-bound lexical context. It requires
`n < 2^63`, an installed recursive drop function, checked call sites and their
continuations, fresh destinations, a checked literal assignment/goto site,
and sufficient independent stack budgets for both child depths. Heap ownership,
field representation, frame separation, and pending-shell authority come from
Boundary.Valid. It constructs BodyResult rather than assuming execution.

Generic enclosing source totality requires the literal bound, lexical agreement,
empty buffer layout, heap validity, separated ownership of tree plus ambient
frame, and stored-field representation. It supports finite recursive source
trees. The release/survival results additionally inspect an observed source run.
See CASE_CHILD_CONSUMPTION.md, CASE_CHILD_TRANSFER.md, and
CASE_SOURCE_CONSUMPTION.md for precise theorem premises.

The closed connection is a conjunction of source typing, independently derived
source evaluation, exact 24-tick target execution, and scalar 7 in local 1.
It has no certificate or execution premises. The target frees child boxes 1 and
2 and parent shell 3; the source frees shell 7. Logical Nil has no source
allocation. Trace equality is therefore neither asserted nor expected.
The target also has an administrative ghost slot; source/target context identity
is not asserted. The recursive target fixture separately checks 40 ticks.

This remains a handwritten restricted source graph and a closed execution
conjunction. It is not general lowering, a parametric simulation, compiler
correctness, a production frontend export, a return ABI, or a generalized
recursive Case linker. The frozen Supported contract is unchanged.

## Reproduction

Use pinned Lean 4.34.1 and LEAN_NUM_THREADS=2. The integration worktree starts
without inherited build artifacts; clean the Lake build before the aggregate:

```sh
(cd proofs && lake clean)
bash proofs/check.sh
bash proofs/check-common-case-composition.sh
bash proofs/check-recursive-fields.sh
python3 scripts/check_nix_sources.py --offline --system x86_64-linux
```

The offline source-isolation command needs the existing cached Nix runtime.
It evaluates source changes; it is not a Nix derivation build.

## Original replay plan (completed below)

Do not publish or merge this branch before #203 merges and actual main is
verified. After that, fetch actual main and verify #203 contents plus any
intervening changes. Create a fresh branch from that verified main and replay
only the three listed commits plus this integration-wiring commit, in order.
Do not replay #203's local ancestry merely because its tested tree was used here.
Resolve any differences, rerun the clean aggregate and dedicated fixture/audit
checks on the exact final tree, then seek publication/merge according to the
parent task's authorization. Current local success does not verify future main.

## Completed local validation

Pinned Lean 4.34.1, warnings as errors, clean Lake build: **381 jobs passed**.
`proofs/check.sh` passed all **3,732** elaborated theorem audits and all 12
existing generated-fixture diffs. The full Case chain passed, including the
new **47**-theorem audit, prior **36**-theorem literal/finish audit and unchanged
**60**-theorem Case composition audit. `check-recursive-fields.sh` passed its
**556** audits and the whole constructor-view JSON fixture comparison.
Only propext, Quot.sound and Classical.choice are permitted; no new axiom,
sorry, admit or native_decide declarations occur in the six input modules.
All **12** offline x86_64-linux source-isolation mutations passed. Earlier root
imports and aggregate audits remain verbatim prefixes, all new imports resolve,
and git diff --check passed. No publication, merge, native compiler rebuild or
Nix derivation build was performed.

Local logs alongside the worktree: case-consumption-full.log,
case-consumption-case.log, case-consumption-recursive.log, and
case-consumption-isolation.log. These results verify this local integration
only; actual main verification remains a later prerequisite.

## Verified main replay

#203 merged as `894b172596b6d8076ad8eb9c794e57f0a8392de5`.
The GitHub main ref and fetched origin/main both identify that commit. Its tree
is `6cde919b1ad3879f1bc48ea35b8a810f3ee73b2c`, exactly the tested #203 tree.
The four input commits were cherry-picked in order onto that actual main in
fresh worktree jihoo-case-consumption-main, branch codex/case-consumption-main.
The replay needed no conflict resolution and produced tree
`ef75eb0dd03d3f86671b44a1f84554b0257dd920`, exactly the previously tested
integration tree. This provenance update is the only additional change.

The final main-based tree is revalidated with the same aggregate, full Case,
recursive-field fixture and source-isolation commands. Logs use prefix
case-consumption-main- alongside the worktree. Publication is authorized as a
draft PR; merging is explicitly excluded from this task.
