# Store-driven Drop in the common binary judgment

The common Case fragment can now consume a recursive child and continue with
another Data or scalar body, instead of always reconstructing both children.
`CommonData.Typing.drop` and `Eval.drop` extend the existing judgment; they do
not form a disconnected resource model. `Typing.total` and `Typing.every_run`
now cover this rule as well as the earlier Case and Buffer rules.

## Actual source shape and limits

The node is `drop family owner rest`, matching the argument order of
`compiler/core.jh`'s `Term.Drop(f, x, rest)`. The family is an identifier, not a
child graph node: `children` contains only owner and rest. This specified
fragment recognizes family **0**, one fixed monomorphic binary family, and a
variable owner denoting the first Data capability. Other families are rejected.
The owner aliases are retired by `removeHead`, the remaining capability slots
shift, and the continuation checks the whole remaining Data/Buffer inventory.
The old Buffer graph projection maps Drop to opaque.

This is constructor-shape correspondence based on inspection of the actual
source checker/lowerer, not a verified exporter, parser or checker refinement.
The production checker also verifies the boxed family's identity and supports
other constructor layouts; that general check is not modeled here. In particular,
our empty value is `none` with no allocation. Native boxed nullary constructors
and their tag/layout are not identified with this representation.

The runtime order follows the binary part of `core_lower.jh`'s `drop_glue`:
read and save both child references, free/clear the parent, then destroy left
and right. This differs from Case's pending-shell release after its body.
No native simulation, allocation reuse or memory-byte correspondence is proved.

## Derived destruction and continuation safety

`Destroy` is an inductive operational relation on references and states. It
reads actual cell contents; it takes no Tree witness, ownership certificate or
successful-run premise. Raw cyclic/missing-cell graphs need not have a finite
safe run. The raw relation checks cell lookup but has no dynamic liveness or
lease guard; legal frees are derived from the safety theorem's input ownership,
not enforced by an executable runtime checker. `destroy_total` uses structural induction on a finite `Represents`
witness and disjoint live, lease-free ownership to construct a finite run and
safe heap steps while retaining an arbitrary frame. This is relational totality,
not an extracted fuel interpreter or a native drop-glue termination proof.

`Destroy.cells_frame` preserves cells outside the release trace, and
`Destroy.lengths` preserves Buffer lengths. The common typing proof derives
remaining Data interpretation and Buffer layout from these lemmas before
invoking the continuation's induction hypothesis. Frame or body preservation
is not added as a typing premise. Operational determinism transfers these
results to every run.

`destroy_accounting` proves that this primitive emits exactly the input tree's
preorder list of frees, with no duplicate identity or other event. This is an
exact accounting result for **Drop itself**, not for arbitrary common programs.
General common-language allocation/release accounting remains open. The body
language now admits nested Case and scalar tree consumption, but general
recursive functions, dependent motives/indexed families, arbitrary constructors,
general data let-binding and Back remain outside the judgment.

## Regression coverage

The concrete whole-tree Drop frees `[0,1,2,3]`, preserves frame `[4,5,6]`, and
returns scalar 99. Another example follows Drop with the existing typed Buffer
free operation. A nested Case consumes its empty leaf fields and returns the
represented sibling rooted at 2; a separate Case drops nonempty child 1 then
returns that sibling. Both preserve the pending parent until the Case body ends.
Negative checks cover other family IDs, stale aliases, missing cells, shared
child ownership and leased child ownership. Existing reconstruction regressions
remain in the standalone check.

Run `bash proofs/check-recursive-fields.sh` or the Nix `recursive-field-proofs`
check. Shared Core audit/CI files and compiler implementation are unchanged.
