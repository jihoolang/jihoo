# Symbolic dependent Buffer typing

This proof connects a value-independent source judgment to the existing sized
Core ownership semantics. It is a step toward the [common typing blocker](0.6-proof-status.md), not completion of the 0.6 soundness gate.

## One derivation before the inputs are known

`SymbolicCoreTyping.Typing` is an inductive judgment over the original Core
constructor graph. Its context contains natural parameters, scalar slots,
owner capabilities, erased `Lt` assumptions and unavailable names. Buffer
lengths and owned result types contain open index expressions rather than
already chosen natural numbers.

The supported rules are scalar literals and variables, owned variables,
allocation, allocation binding, direct owned-variable application, natural
application, `Free`, `IfLt`, and a read-only scalar-result `Lend`. Every rule
checks the actual graph constructor and relevant annotations. Both alternatives
of `IfLt` need finite derivations with the same result and resource inventory.
A branch cannot be admitted merely because one particular input avoids it.

The index grammar is U64 literals, natural variables and direct U64 lets. Its
static availability judgment excludes scalar, owner, erased and dead slots.
`Index.raw_typed` derives the existing `Raw.Beta.HasType` judgment through a
slot-preserving pure context projection. The projection retains natural,
scalar and erased-bound entries; owner authority never becomes unrestricted
pure-variable authority.

## Binding and dependent results

Every symbolic length and bound is interpreted in the current lexical scope.
Introducing any binder shifts the old inventory, result and bound expressions,
even when the new slot is erased or non-natural. The new `Lt(a,b)` assumption
is itself shifted under its binder. Runtime slots are not silently removed.

The natural application rule permits a result that depends on the new natural
parameter. Its conclusion substitutes the actual argument into the body result
using capture-avoiding `Expr.subst`. The encoding commutes with the existing Raw
substitution, and `index_beta_preservation` reuses Raw's typed beta theorem.
`ResultEval.beta` and its inverse connect this syntactic operation to the actual
closing values used by ownership typing. This is index/result instantiation,
not a theorem for every dependent `Buffer`/`Ref` Pi type.

Direct owned-variable application instead transfers a capability. It preserves
its concrete identity and invalidates every old lexical alias. A scalar-result
`Lend` restores the original capability and binds the copied scalar; its reader
cannot return the borrowed reference. `Free` clears every alias of the consumed
capability while preserving unrelated lexical positions.

## Constructed safety and accounting

`Typing.instantiate` is an induction from symbolic rules to the existing
`SizedCoreTyping.Typing` on the same graph. Its input interpretations supply
natural values, true erased bounds and initial resource lengths. The induction
derives the annotation, read-index, lease and consumption premises needed by
the existing runtime proof.

`Typing.result_total` constructs the output type interpretation. The public
`Typing.total_accounted` endpoint then constructs:

- A terminating `SizedCoreExecution.Eval` derivation.
- The corresponding safe `SizedBufferHeap.Steps` and valid final heap.
- A scalar result, or a live unborrowed owner with its exact interpreted length.
- The identity-based release account: every initial or newly allocated owner is
  released or returned, with the established lifecycle proof ruling out repeated
  release and use outside a live lease.

The endpoint assumes a closing input context, an interpreted initial length
inventory, agreement with the runtime environment, matching heap layout, a
valid initial heap and ownership of the input capabilities. It assumes no
successful runtime execution, safe event trace, output evaluation or accepted
certificate. `Typing.every_run_accounted` transfers the result to every run of
the independent deterministic lexical evaluator.

Input interpretation is an explicit admission boundary. Arbitrarily malformed
symbolic inventories need not have a closing interpretation. In particular,
an owner slot used as its own natural length admits none; the proof does not
claim formation or nonvacuity for arbitrary input contexts.

## Regression coverage and limits

One static derivation covers both branches of the unchanged dynamic n/i buffer
graph, before n and i are supplied. Closing it yields safety for arbitrary U64
inputs, including zero lengths and out-of-range indices without a read. A
separate natural application example substitutes `Buffer(m)` to `Buffer(n)`
and proves the actual returned allocation has length n. The native
`symbolic-buffer-result.jhc` preservation fixture also checks this pattern and
exactly-once consumption through the production checker; that association is
a regression check, not an implementation-refinement theorem.

Lean regressions reject dead names, both old aliases after transfer and free,
mismatched symbolic `Lt` indices/lengths, and an invalid unselected branch. They
also check nested capture-avoiding substitution and every lexical shift.
All new theorems participate in the elaborated axiom audit.

This judgment is a syntactic **subset** of the existing sized fragment. It does
not yet include its framed applications or owned-result Lends. The broader
omissions remain: arbitrary reader bodies and nested active-reader Lends,
nonuniform buffers and `Store`, recursive data/field ownership, `Back`, general
closures or recursion, full dependent Pi preservation, the rest of Raw typing,
and an executable symbolic checker. The graph/exporter association, production
checker, native lowering, MIR-to-LLVM, physical addresses and allocation failure
remain outside this result. Existing erasure and generated-MIR theorems can
consume the instantiated sized judgment under their own stated premises.

## Mixed binary Data source typing

`SymbolicCommonDataSource.Typing` connects the same symbolic Buffer rules to
`CommonDataSourceRules.Typing`. Its separate mixed context has natural markers
without values, scalars, Data and Buffer capability slots, ghosts and dead
slots. `SymbolicCommonDataContext` reuses `SymbolicCoreContext` for the Buffer
projection and closes into `RecursiveBodyProjection.context`; Data authority
never becomes Buffer authority or erased bound evidence.

| Source rule | Actual supported behavior |
| --- | --- |
| `literal`, `empty` | Scalar literal or empty Tree, with no owned inventory |
| `dataVar` | The sole Tree capability at slot 0 |
| `construct` | Fixed binary constructor from Tree slots 0 and 1 |
| `bufferLet` | Existing symbolic Buffer derivation with a scalar result, consuming the Buffer suffix; retained Trees survive |
| `dataLet` | Direct Tree lambda application consuming all old capabilities before binding the returned Tree |
| `dataLetSplit` | Direct application consuming selected Tree/Buffer prefixes and preserving the suffix; all consumed aliases are dead |
| `drop` | Consume the head Tree and shift capability slots without removing lexical positions |
| `caseTree` | Fixed binary Tree, constant scalar/Data motive, both branches checked; node fields occupy lexical slots `[right, left]` and retire all parent aliases |

The split continuation shifts saved length expressions by one lexical binder.
The node branch shifts every length by two. Argument contexts, empty branches
and drops do not shift lexical indices. Closing proves those transformations
commute with the existing concrete contexts, including the length of the used
Buffer prefix.

`Typing.instantiate` derives the existing concrete source judgment at **every**
suitable closing and evaluated initial inventory. No execution is a premise.
`Typing.total_accounted` constructs an actual `CommonDataSourceExecution.Eval`;
`Typing.every_run_accounted` gives safe heap steps, final heap validity and
`AccountedPost` for every such execution. Both retain the established initial
layout, ownership, field-store and frame assumptions.

Lean regressions use open lengths in Case and split applications, including
distinct used/saved natural parameters and zero/nonzero closing sizes. They
reject unshifted or missing natural indices, consumed Data/Buffer aliases and
wrong motives/branch results. The scalar-result Buffer family includes its
restricted read-only `Lend`, not arbitrary readers. General dependent Pi,
recursive functions, dependent motives, production-checker refinement and
native compiler soundness remain outside these theorems.
