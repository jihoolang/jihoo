# Representation bridge to the core

The Lean representation bridge in `proofs/Jihoo/CoreBridge*.lean` translates a
bounded, annotated subset into trees with selected constructor shapes from
`compiler/core.jh`. It addresses a concrete gap between the two-sorted
[proved calculus](lean-proofs.md) and the core's single de Bruijn namespace.
It is **not** a proof that the executable checker implements the calculus, or
that every encoded term is accepted. A separate restricted declarative typing
translation is described below; it is not the executable graph checker.

## The selected subset

Index expressions contain variables, bounded u64 literals, addition, and certified
closed subtraction. Types contain `U64`, `I64`, indexed arrays, `Lt`, `Eq`, and
natural-index Pi types. Terms contain value variables, numeric literals and
constant arrays, closed `Decide`, `Refl`, `ZeroLe`, indexing, index lambdas and
applications, and value lets with explicit type annotations.

The annotated input has an explicit erasure to `Indexed.Term`/`Indexed.Ty` and
`Arithmetic.Expr`. Erasure preserves scope. The mixed-binder example is also
checked in the earlier finite typing judgment. The representation guarantees alone do not establish typing: a let annotation
can be wrong while every representation-side property still holds. The restricted
typed translation below checks that annotation explicitly.

`Index.ofExpr` is a checked partial conversion from the earlier arithmetic syntax.
Successful conversion erases back to **exactly** the input expression. It rejects
out-of-range literals rather than wrapping them, and rejects unsupported
subtraction instead of silently deleting its evidence requirement. There is no
claimed completeness or normalization of the input: subtraction of nonliteral
operands is rejected even if those operands could reduce to numerals.

## Unified binders

The source has separate index and value variables. The target `Raw.var` has one
namespace. Encoding an index lambda puts the new index at target zero and shifts
both older namespaces. Encoding a value let similarly puts its value at zero,
shifts both namespaces, and translates its annotation outside the new binder.
A value let becomes an application of an annotated lambda. Proposition-valued
annotations, including Pi types ending in propositions, select an erased lambda;
index lambdas use non-erased `U64` binders.

A mixed `Layout` records the kinds of the existing binders. The layout theorems
prove that every valid source variable selects an existing target slot of the
right kind, distinct variables of the same kind have distinct slots, and an
index variable cannot alias a value-variable slot. Scope preservation connects
these layouts to the encoded target tree.

Encoding also commutes with unified capture-avoiding renaming, including beneath
both binder sorts and within annotations. Weakening is an instance. This representation theorem alone does not establish arbitrary term substitution
or beta simulation. The typed extension below separately proves the type-substitution
correspondence needed by its application rule.
General encoding functions permit arbitrary maps; the non-aliasing guarantees
apply when using a valid mixed layout.

## Literal and subtraction guarantees

Every emitted `Natural` literal is below 2^64. Every emitted `Integer`, including
array elements, lies between -2^63 and 2^63-1. These are literal-node guarantees,
not promises that addition never overflows at runtime.

The only subtraction form has natural operands a and b with checked premises
`b <= a` and `a + 1 < 2^64`. It emits exactly:

```text
(usub a b (decide-lt b (a + 1)))
```

Here `a + 1` is emitted as its numeral, not as an unevaluated expression.
The proofs establish that every emitted `USub` has this matching certificate,
that both operands and the certificate endpoint fit, and that `b < a + 1`, so
subtraction cannot underflow in the natural model. They do not prove execution
of the compiler's normalization or evidence checker.

The largest permitted left operand for this encoding is 2^64-2. Subtraction
from 2^64-1 is deliberately rejected, even when mathematically safe, because
this particular `Decide` encoding needs a representable endpoint. Open
subtraction needs an explicit evidence-preserving extension; it is not translated
by an unchecked cast or an assumed certificate.

## Generated implementation tests

`proofs/EmitCore.lean` serializes the encoded examples to the canonical
`tests/core_preserves/lean-core-translation.jhc` fixture. `proofs/check.sh`
regenerates it and compares the bytes, and the ordinary core suite asks the
actual compiler to check and recheck pure normal forms of that fixture. The
proof-only Nix derivation includes the serializer and canonical fixture, so stale
hand-edited generated output fails CI.

The fixture covers mixed binders, erased proof lets, nested values, array reads,
the largest u64 literal, signed extrema, ordinary subtraction and subtraction
whose certificate uses the last representable endpoint. It also includes an
addition of individually representable literals whose sum would overflow if
executed. Checker/preservation acceptance is not a claim that this addition
runs successfully. These generated definitions are not runtime execution tests.

Lean examples reject overflowing literals, open/underflowing subtraction, and
the unsupported maximum subtraction endpoint. They inspect exact target binder
positions and show the bridge input's connection to the earlier scoped calculus.
The serializer itself is bounded and fallible; exhaustion or an unbound rendered
variable fails generation. Generation starts with an empty naming environment; the helper does not promise
freshness for arbitrary caller-supplied open names. Renderer/parser agreement is
regression-tested, not mechanically proved.

## Remaining correspondence obligations

`Raw` is a tree, while the implementation stores graph-node identifiers and
validates their ordering. Its mathematical variable indices are `Nat`, while the
implementation uses `u32`. The bridge does not prove graph construction,
identifier bounds, depth/step/node budgets, arbitrary ghost-position restrictions,
or the executable parser, checker, normalizer and lowerer. It also omits universe
formation, inductive families and eliminators, ownership, memory effects and
most core evidence terms.

Well-scoped, bounded syntax with guarded subtraction can still be ill typed.
The restricted typing theorem below connects a source typing derivation to a
target declarative judgment. A relationship between that judgment and the
executable checker remains a separate, unproved obligation. The existing
fragment preservation and consistency results do not automatically become
guarantees about all accepted core programs merely because a serializer exists.

## Restricted declarative typing

`CoreBridgeTyping.lean` adds a separate target typing judgment over `Raw` trees.
Its rules do not mention the source encoder. Variables use a single namespace;
context entries are expressed in the current scope, and extending a context
weakens both existing entries and the new annotation. This differs in storage
convention from the executable checker, which stores declaration-time types and
weakens them on lookup. Equivalence of those implementations is not assumed to
be an executable-checker theorem.

The target has ordinary dependent lambda/application rules with capture-avoiding
substitution into the result type. Type formation checks the indices occurring
in arrays, inequalities and equalities. A small target conversion relation folds
non-overflowing numeral addition and transports that equation through selected
type constructors. In particular, subtraction requires evidence of
`Lt(b, UAdd(a, 1))`; the generated numeral-endpoint certificate is connected by
conversion rather than a special rule recognizing the source encoder.

This target is a universe-free **ghost-mode** specification. Proposition domains
select erased binders, but variable lookup does not enforce runtime erasure
restrictions. It does not model ownership, lowering or execution. Its conversion
rules are a specified subset, not the compiler's resource-bounded `equal` routine.
A proof of translation into this judgment therefore cannot by itself establish
acceptance by the executable checker or runtime safety.

The finite source judgment `SourceTyping` inspects the annotated bridge syntax.
In particular, its let rule requires the value to have the stated annotation and
types the body in the extended value context. It has no general conversion rule
and no rule for `zeroLe`. It supports bounded numeric literals, arrays and indexed
reads, closed comparisons, reflexivity, certified closed subtraction, natural-index
lambdas/applications and value lets. Array lengths must also fit the literal range.

`SourceTyping.translate` proves that every such derivation translates to a target
typing derivation. Its context correspondence supplies only variable-lookup facts;
it does not assume target typing of the translated term. Both binder extensions
preserve that correspondence by proved context lemmas. Dependent application uses
`Ty.encode_instantiate`, a theorem connecting source index substitution to unified
target substitution. Value-let elimination uses `Ty.encode_drop_value`, since
source types cannot depend on value variables.

The target deliberately selects fewer binder modes than the implementation: its
erasure flag is exactly the domain's proposition classification, excluding legal
erased U64 binders. Arbitrary target contexts can contain malformed types; no
regularity theorem for arbitrary contexts or general target preservation/consistency
theorem is claimed here. The earlier calculus's soundness results apply to its own
judgment, not automatically to every inhabitant of this target judgment.

`SourceTyping.translate_closed` removes the open context-correspondence hypotheses
for closed input. The source erasure theorems `SourceTyping.erases` and
`SourceTyping.erase_closed` also connect this annotation-checking judgment to the
earlier calculus. Open context matching alone permits same-typed variable aliasing,
and unused source context entries need not be scoped. The translation theorem is
valid with these weaker assumptions, but an injective, globally well-formed open
embedding requires the separate layout/scoping invariants. Closed corollaries avoid
these open-context issues.

`CoreBridgeTypingExamples.lean` proves source and target typing for every emitted
fixture declaration, including dependent applications whose result changes under
index substitution. It also proves that an I64-valued let falsely annotated U64 is
rejected at every claimed result type, even though its annotation-erased image is
typable in the earlier calculus. The closed type-formation corollary
`SourceTyping.closed_type_formed` checks the translated result type separately.
