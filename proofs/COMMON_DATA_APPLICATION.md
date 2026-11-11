# Computed Data arguments in the common Core judgment

The 0.6 roadmap requires one specified typing-to-runtime ownership theorem,
not a sum of unrelated resource lemmas. After Case reconstruction and Drop,
the next missing connection was feeding a computed Data result to another
body. `Typing.dataLet` and `Eval.dataLet` now extend the same `CommonData`
judgment to direct-lambda application with Data arguments and scalar/Data results.

## Source shape

No synthetic let node is introduced. The rule recognizes existing
`App(function, argument)` and `Lam(false, domain, body)` shapes, with the new
constructor view `Ind(0, [])` for the fixed binary type. The `Ind` family ID
is not a graph child; its argument IDs are. The old Buffer projection maps
`Ind` to opaque. Both typing and execution check the exact domain shape, so
this rule is operationally distinct from the existing i64 Buffer scalar let.

These are the actual `Term.App`, `Term.Lam` and `Term.Ind` field shapes in
`compiler/core.jh`. This remains a hand-built constructor view, not an exporter
or checker refinement proof. Production application inference normalizes a
function's Pi type, checks its domain, substitutes the result type, and checks
partial-application restrictions. This rule covers only a syntactically direct,
non-erased lambda with exactly `Ind(0, [])`; no general Pi typing/substitution,
domain conversion, indexed families, closures or function values are modeled.

## Derived continuation interpretation

The argument is checked by the common judgment against the entire active
Data/Buffer inventory and must return Data. Its totality theorem produces the
actual returned root, a tree represented by the post-argument cell store,
valid heap and ownership of that tree plus the arbitrary external frame.

`dataContinuation` retires **all** old Data and Buffer aliases and prepends a
new Data slot. Naturals, scalar values, ghost slots and dead slots keep their
relative lexical positions. `agrees_dataContinuation` derives agreement with
the returned root prepended to the original environment. The old owner values
may still physically occur in that environment; their entries are dead and
cannot authorize access. The returned tree is not assumed equal to an input
tree or root, and empty results still carry one logical Data capability even
though their allocation footprint is empty.

The common `Typing.total` proof derives the singleton inventory, its field
interpretation and empty Buffer layout, then applies the body induction
hypothesis. It concatenates argument and body traces without assuming either
successful execution or preservation as extra premises. Determinism and
`Typing.every_run` include the same rule. This does not add generic exact
trace accounting: positive result/frame ownership is not exhaustive ownership.

## Scope and regressions

This is whole-active-inventory sequencing. Some capabilities cannot remain
available to the lambda body alongside its result; the arbitrary theorem frame
is retained but inaccessible to this application. General context splitting,
recursive function bodies, dependent motives, arbitrary constructor telescopes,
Back and native lowering/layout correspondence remain open. The abstract empty
and binary cells retain the existing representation boundary.

Fixtures reconstruct input root 0 to 7 and then 8, or feed the computed root to
Drop and return scalar 99. A nested application consumes the twice-rebuilt
root. A Buffer-effect argument frees Buffer 4 before its Data result is dropped.
Empty arguments are returned and consumed without allocation. Concrete safety
checks retain external frame `[4,5,6]`; alias and annotation regressions reject
stale owner access, erased lambdas, other families, indexed domains and scalar
arguments where Data is required. The mixed lexical layout check retains
natural/scalar/ghost positions while retiring separated owner aliases.

Run `bash proofs/check-recursive-fields.sh` or the independent Nix
`recursive-field-proofs` check. Compiler and shared Core audit/CI sources are
unchanged; this is a step toward the common gate, not closure of that gate.
