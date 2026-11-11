# Restricted source-view execution

`Jihoo/CommonDataSourceExecution.lean` gives the fixed binary Tree constructor
view of `CommonDataSourceRules` its own inductive big-step execution relation.
It reads source `con`, `caseOf`, `drop`, variable, literal and direct-application
nodes. Case validates the constant I64/Tree motive and two field binders; runtime
branch selection reads the actual reference/store. Split application is an
ownership typing rule with the same ordinary application runtime rule.

The relation is not an alias for an adapter or for successful common execution.
Its scalar sublanguage uses `sourceCore`, a direct source-node projection;
`sourceCore_eq` separately proves agreement with the adapter's Core projection.
`Eval.to_common` preserves the exact value, event trace and final abstract state.
`reflect` proves the reverse direction for source-typed programs. Untyped reverse
correspondence is deliberately not claimed, since adaptation forgets motive
information. `correspondence` packages those two directions.

`total_accounted` starts with source typing, agreement with the lexical
environment, buffer layout, valid initial heap, disjoint ownership including an
arbitrary external frame, and represented Data fields. It derives an execution,
safe heap steps, final heap validity and allocation conservation. It does not
assume successful source/common execution or post-body ownership. The proof
uses independently established common typed totality and then reflects its
execution. `Eval.deterministic` and `every_run_accounted` cover arbitrary
observed source runs as well.

## Evidence

`CommonDataSourceExecutionChecks.lean` directly constructs source derivations
for scalar Case with recursive Drop, nested nonempty Case, split application
with real retained Data references, a computing nil branch, and recursive
whole-tree Drop. Nested Case frees descendants 2 and 3, inner shell 1, then
outer shell 0. A separate existence regression supplies no execution premise.
The checks print axiom dependencies for all seven public bridge theorems and
eight regressions; only `propext`, `Quot.sound`, and `Classical.choice` occur.
Fixtures are hand-written, not new compiler exports.

## Boundary and remaining work

This is a source *constructor-view* abstract runtime, not the full language's
operational semantics. It intentionally shares `Value`, the abstract heap and
cell store, `Destroy`, `enter`, `allocate`, `finish`, and the existing scalar
`SizedCoreExecution` semantics. Their model is part of the statement, not a
claim about native object representation. Initial ownership, field
representation, layout and validity are explicit hypotheses; production checker
soundness does not establish them here.

There is no theorem for parser/elaborator/export fidelity, production-checker
soundness, native compiler refinement, concrete allocator/layout/reuse,
unrestricted dependent motives, recursive functions, arbitrary families,
first-class functions, or full-language ownership/Back. Runtime recursive Drop
on represented finite trees is covered; recursive source functions are not.
The source graph/family validators remain separate, as in #178; callers needing
a top-level certificate should use its `CheckedEntry` and extract source typing.

The source typing module was integrated by PR #178. Both execution modules are
imported by `proofs/Jihoo.lean`, and `CheckRecursiveFieldOwnership.lean` audits
all 15 new theorems alongside the existing 300. The recursive-field runner
builds the execution checks and requires 315 allowlisted audits. Both Nix proof
checks include the complete `proofs/Jihoo` source directory; the existing
x86_64/aarch64 CI runs these checks through `nix flake check`.

Standalone validation from `proofs/` with Lean 4.34.1:

```sh
lake build --wfail Jihoo.CommonDataSourceExecution Jihoo.CommonDataSourceExecutionChecks
lake env lean -DwarningAsError=true Jihoo/CommonDataSourceExecutionChecks.lean
```
