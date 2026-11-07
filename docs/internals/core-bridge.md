# Representation bridge to the core

The Lean representation bridge in `proofs/Jihoo/CoreBridge*.lean` translates a
bounded, annotated subset into trees with selected constructor shapes from
`compiler/core.jh`. It addresses a concrete gap between the two-sorted
[proved calculus](lean-proofs.md) and the core's single de Bruijn namespace.
It is **not** a proof that the executable checker implements the calculus, or
that every encoded term is accepted. The target has no formal typing judgment
in this bridge.

## The selected subset

Index expressions contain variables, bounded u64 literals, addition, and certified
closed subtraction. Types contain `U64`, `I64`, indexed arrays, `Lt`, `Eq`, and
natural-index Pi types. Terms contain value variables, numeric literals and
constant arrays, closed `Decide`, `Refl`, `ZeroLe`, indexing, index lambdas and
applications, and value lets with explicit type annotations.

The annotated input has an explicit erasure to `Indexed.Term`/`Indexed.Ty` and
`Arithmetic.Expr`. Erasure preserves scope. The mixed-binder example is also
checked in the earlier finite typing judgment. There is no general proof that
source typing entails target typing; a let annotation can be wrong, for example,
while every representation-side property still holds.

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
both binder sorts and within annotations. Weakening is an instance. This is **not**
yet a theorem about arbitrary substitution, beta simulation or typing translation.
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
The needed next bridge theorem must connect a precisely restricted source typing
derivation to a target declarative typing judgment, followed by the separately
stated trusted or proved relationship to the executable checker. The existing
fragment preservation and consistency results do not automatically become
guarantees about all accepted core programs merely because a serializer exists.
