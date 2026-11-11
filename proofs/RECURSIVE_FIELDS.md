# Recursive field ownership interface

`Jihoo.RecursiveFieldOwnership` models finite binary boxed data by allocation
identities and flattens its recursive fields into the existing
`LinearHeapPrograms.Owns` inventory. It proves root/descendant and cross-field
separation, fresh parent allocation, parent release preserving both fields and
an ambient frame, and exact per-identity release accounting.

`consume_left_total` connects this inventory to
`OwnedCoreApplications.Typing`: after releasing the parent, a typed consumer
of the left field has an execution with safe heap steps and a valid final
state. The right field and external frame remain owned. Successful execution
is a conclusion, not an input. `consume_left` also covers every admitted run.

Run with the repository-pinned Lean version and Python available:

```sh
bash proofs/check-recursive-fields.sh
```

This builds the dependency closure with warnings as errors and checks all 207
named new theorem dependencies against the standard logical axiom allowlist.
Regressions reject shared children, deep ancestor aliases, dead fields and
active field leases, and check parent release with a retained child and frame.

## Boundary

This is a resource interface for future recursive Core typing, not such a
judgment itself. Tree edges are mathematical metadata: the heap still stores a
scalar payload, and no theorem equates native field bytes with these edges.
The consumer interface is the existing flat Buffer1 Core judgment, not
`SizedCoreTyping.Typing` or PR #165's symbolic instantiation. No arbitrary data
constructors, dependent eliminators, Back rules, native compiler execution,
MIR/LLVM correspondence, or allocator success are proved. The 0.6 gate stays
open. No production compiler changes or native-test claims are included.

The independent `recursive-field-proofs` Nix check is included by the existing
`nix flake check` CI on x86_64 and aarch64. It leaves the shared `Jihoo.lean`,
`Audit.lean`, `check.sh`, roadmap and both active PRs untouched. Run it alone:

```sh
nix build .#checks.x86_64-linux.recursive-field-proofs
```

A concrete, nonempty fixture also executes an existing Core free/return graph:
it releases parent 0, consumes left child 1, returns 99, and retains frame 2.
The input validity and ownership are proved from the fixture rather than
assumed. This exercises the bridge but still does not certify native field
layout or source recursive-data rules.

## Integration assessment

The reusable result is a resource lemma needed by a future data-elimination
rule: release the parent allocation, transfer field capabilities, and preserve
unrelated capabilities while a typed body runs. The future rule must still
connect a source constructor, its runtime fields and lexical context to this
inventory. In particular, flattening a subtree does not by itself establish
that a Core variable denotes a recursive value. This work should not be counted
as closing the recursive-data or common-typing release blocker.

`ScopedLend.Graph.Node` currently has no recursive constructor/eliminator or
`Back`/`Give`/`Take` nodes. `SizedBufferContext.Value` and the sized heap also
model buffers rather than recursive runtime fields. Adding those representations
and their interpretation/preservation rules is a prerequisite to a common
typing theorem for data. This module neither bypasses that prerequisite nor
identifies arbitrary tree nodes with well-typed Buffer values.

The [runtime field interpretation](RECURSIVE_FIELD_RUNTIME.md) now connects
stored child references to this inventory and retains that interpretation
through a parent split and an existing Core consumer. It does not yet add a
source recursive-data rule. The standalone check covers both interfaces.

The [lexical field interface](RECURSIVE_LEXICAL_FIELDS.md) now binds actual child
roots, retires parent aliases, and preserves a pending shell for later release.
Its separate Buffer-only compatibility theorem connects to sized Core typing;
recursive source Case typing and dependent elimination remain open.

The [source-typed body segment](RECURSIVE_CASE_BODY.md) derives preservation of
the pending parent and child inventory from existing sized Core body typing.
It leaves residual child ownership for a continuation and is not a full Case rule.

The [common binary Case judgment](COMMON_DATA_CASE.md) now checks both branches,
executes existing sized Buffer effects and returns a complete owned Data tree.
It closes the residual-inventory gap for a monomorphic reconstruction fragment,
while dependent motives, recursive bodies and native correspondence remain open.

The [store-driven Drop extension](COMMON_DATA_DROP.md) adds recursive tree
consumption and scalar/nested Case bodies to that judgment. Its primitive has
exact release accounting; whole-language accounting and native refinement remain open.

The [computed Data application extension](COMMON_DATA_APPLICATION.md) connects
Data-producing arguments to subsequent typed bodies through source App/Lam/Ind
shapes. It retires old aliases and derives the returned-tree interpretation.
