# Lean proof boundary

The mechanized work toward 0.6 includes arithmetic evidence, an index-dependent
calculus with value lets and conversion, finite scoping, and a logical interpretation
of that calculus. These are separate declarative specifications inspired by the
[core specification](core-spec.md), not translations of `compiler/core.jh`.
They establish preservation and consistency for the stated fragments, **not** the
full dependent kernel, its normalization algorithm, ownership, lowering or whole
executables.

## Arithmetic evidence

Expressions contain free variables, natural literals, addition and subtraction.
A valuation assigns a natural number to every free variable. Propositions are
`Lt(a, b)` and `Eq(a, b)`, interpreted as natural-number comparison and equality.
An evidence context is a list of such propositions.

- `Expr.eval_subst`: simultaneous first-order substitution agrees with valuation
  substitution.
- `Conv.sound`: every derivation of the selected syntactic conversion rules
  preserves the expression's value, for every valuation.
- `Conv.subst`: these conversion derivations survive first-order substitution.
- `Formula.holds_subst`: proposition substitution agrees with its semantics.
- `Derives.sound`: evidence derived from a context is true in every valuation
  satisfying that context. The proof is by induction on a syntactic derivation;
  truth of the conclusion is not an assumed typing rule.
- `no_closed_false_lt`: no derivation in the empty context proves `Lt(0, 0)`.
- `certified_sub_add`: evidence of `Lt(b, a + 1)` justifies `(a - b) + b = a`.
- `certified_index_lt`: derived bounds evidence implies the corresponding
  natural-number bound. This is only the arithmetic premise of memory safety,
  not a theorem about machine addresses or heaps.

The example module checks nested conversion, open assumptions, equality transport,
and the maximum u64 boundary, and proves that unrestricted subtraction cancellation
and a closed equality between zero and one are impossible in this fragment.

### Arithmetic correspondence and differences

`Expr.var`, `lit`, `add` and `sub` abstract `Var`, `Natural`, `UAdd` and `USub`.
Unlike the core's graph, these are trees. Their free variables have natural indices;
there are no binders, so this is not the kernel's de Bruijn substitution theorem.
The Lean literal type is unbounded `Nat`. Core literal nodes are u64, but symbolic
core sums denote mathematical naturals. They must not be modeled by wrapping
`UInt64`: for example, `ZeroLe` at the largest u64 still establishes
`Lt(0, a + 1)`. Runtime overflow traps require a separate semantics.

The evidence constructors correspond to assumptions, `Refl`, closed `Decide`,
`ZeroLe`, `LtAdd`, `LtCancel`, `LtLe`, conversion and `Transport` specialized to
first-order `Lt`/`Eq` proposition families. Instantiating a family replaces variable
zero and leaves other variable numbers unchanged; it is not beta reduction of a
core lambda. Closed `Decide` takes a Lean proof of a numeral comparison, which is
computable and checked by the Lean kernel, not an oracle for open propositions.

`Conv` is an equational theory, not `normal` or `identical`. It includes symmetry,
transitivity, congruence, commutativity and associativity of addition, zero removal,
numeral arithmetic and `(a + b) - b = a`. These equations are sound in naturals.
There is no claim that every such equation converts in the resource-bounded
implementation or that every implementation conversion is represented here.
Numeral rules need not respect the implementation's folding and overflow limits.
The evidence field of `USub` is omitted, and subtraction is total natural truncated
subtraction. The core additionally requires evidence ruling out underflow. That
requirement is essential for the separate `certified_sub_add` theorem; unrestricted
`(a - b) + b = a` is deliberately absent from `Conv`.

Consequently this model does not prove proof-irrelevant ordering in `compare`, or
that removing an evidence child preserves the typing of a core term. It proves a
sound arithmetic foundation on which that correspondence can later be established.

## Index-dependent beta preservation

`Indexed.lean` proves capture-avoiding index substitution and beta subject reduction
for an **extrinsically typed**, natural-index-dependent calculus with index lambdas and value lets. Types include scalar types, arrays indexed by length, `Lt`, `Eq`,
and `pi B`: a function whose implicit domain is a natural index and whose result
is B. For example, `lam (refl (var 0))` has result type `Eq(i, i)` depending on its
argument i. Applying it to seven substitutes seven into that result type.

Raw terms, the typing judgment `HasType`, and the reduction relation `Step` are
independent definitions. `Step` does not require or carry typing evidence. The
preservation theorem is therefore not enforced by the definition of reduction:
its beta case uses the proved substitution theorem and restores the weakened
context of free value parameters.

The eight additional audited guarantees are:

- `Ty.subst_comp` and `Term.subst_comp`: capture-avoiding simultaneous substitution
  composes, including beneath index binders.
- `Ty.instantiate_subst` and `Term.instantiate_subst`: substituting free indices
  commutes with instantiating an index binder, with the required lifting.
- `HasType.substitution`: substituting indices in the context, term and type
  preserves typing.
- `Step.substitution`: substituting indices preserves the untyped reduction
  relation.
- `preservation`: a beta step, or its compatible closure, preserves a term's type.
- `preservation_many`: a finite sequence of these steps preserves the type.

`IndexedExamples.lean` checks a dependent equality result, a dependent bound result,
nested lambdas with a free index argument that must not be captured, weakening of
an array-typed free value parameter, and beta reduction within an array expression.
Negative examples reject a false equality annotation and a wrong array length.
Arithmetic conversion now accepts a structurally different but provably equal
length; that old rejection example has become a positive regression.

`tests/core_preserves/lean-indexed-beta.jhc` exercises matching beta patterns in the
real kernel, including closing the free array parameter with ordinary value
binders. It is an implementation regression, not a proved translation between
Lean terms and core graphs.

### Indexed correspondence and differences

- Pi and lambda bind **only natural indices**. Their domain is implicit; there is
  no arbitrary dependent function domain, value lambda, type abstraction or
  dependent telescope. The nondependent value lets are described below. Applications accept an arithmetic expression rather than
  an arbitrary term of type `u64`.
- Index variables use de Bruijn numbers: zero is the latest index binder; lifting
  a substitution shifts its inserted expressions beneath a binder. The value
  variable namespace is separate; value lets and their substitution operate in
  that namespace, while index substitution does not change its identifiers.
- The raw typing judgment uses a total `Context` function from value identifiers
  to types. The stronger `ScopedTyping` judgment below uses a finite list and
  explicitly bounds both kinds of variables. Preservation still does not
  establish the truth of proposition assumptions in those contexts.
- The arithmetic syntax is reused from the first fragment, including totalized
  subtraction. `natural`, `integer`, and `elements` use unbounded mathematical
  numbers. The names `u64` and `i64` identify intended core counterparts; they
  do not enforce machine representability, subtraction evidence or trap behavior.
- Conversion is the selected arithmetic equational theory lifted structurally
  through types, including Pi bodies. It is not the core's resource-bounded
  normalization algorithm, and there is still no arithmetic evaluation step.
- Reduction is beta plus closure beneath lambda, in the function of application,
  and in the array/evidence positions of indexing, plus value-let substitution
  and closure in a let's value and body. Array reads do not reduce,
  just as they remain neutral in the core's pure normalization model. There is
  no runtime lookup semantics, progress theorem or executable bounds-safety proof.
- Universe/Prop formation, ghost/code modes, erased binder distinctions,
  quantities, general evidence elimination, inductive families, heaps, effects
  and erasure are absent. The arithmetic `Derives.sound` theorem is not
  automatically a soundness theorem for `Indexed.HasType`.

This is genuine dependent-result substitution and preservation for the stated
calculus, but **not** preservation for the full core or every reduction it performs.
A restriction/translation theorem relating the two remains necessary.

## Finite scope and value lets

A value let adds a separate de Bruijn value binder. `Term.valueSubst` shifts the
inserted term's **indices** when it crosses an index lambda, and its **value
variables** when it crosses another value let. `HasType.valueRenaming` and
`HasType.valueSubstitution` prove preservation for these operations, and
`Term.valueSubst_indexSubst` proves that value and index substitution commute with
the appropriate transformed substitutions. The earlier `HasType.substitution`
and `Step.substitution` names continue to mean **index** substitution.

The untyped `Step.letBeta` substitutes any raw value into a raw body. Its subject
reduction case invokes the value-substitution theorem; typing is not built into
that reduction rule. The existing single- and multi-step preservation theorems
therefore now cover both index beta and value-let reduction.

`Scoped.lean` independently defines scope for arithmetic expressions, types and
terms. A term at scope `(n, m)` has n available index variables and m available
value variables. An index lambda increments n; a value let's body increments m.
There are no semantic or typing premises in these structural scope definitions.

The new audited scope guarantees establish:

- Index substitution preserves expression, type and term scope when each inserted
  expression is within the target scope.
- Value substitution preserves scope when each inserted term is within the target
  index and value scopes.
- `scoped_step`: raw reduction preserves both finite scopes.
- `ScopedTyping.indexSubstitution`: index substitution preserves finite-context
  typing, substituting the context's types as well as the term and result type.
- `scoped_preservation` and `scoped_preservation_many`: one or many reduction steps
  preserve the finite typing judgment.
- `no_closed_parameter`: a free value parameter cannot be typed in the empty
  finite value context.

`ScopedTyping n Γ t A` requires all types in the finite list Γ and the result A to
be index-scoped at n, the term t to be scoped at `(n, Γ.length)`, and the existing
extrinsic typing derivation. Internally Γ is completed to a total context with a
scalar default, but the independent scope condition forbids a term from accessing
those default entries. Examples demonstrate that raw `HasType` can type such an
entry while `ScopedTyping` rejects it. A closed scoped judgment uses n = 0 and an
empty value context; scope/typing preservation is not a progress or consistency
theorem.

The additional examples cover a closed let beta step, a value with free indices
moved beneath an index lambda, a free value variable moved beneath a nested value
let, both binder sorts interleaved, and rejection of dangling indices, value
variables and context-type indices.

### Value and scope boundaries

These are **nondependent value lets**: types mention index variables, not value
variables, so the result type does not need substitution of the bound value. This
is not general dependent value substitution. The auxiliary `letValue` form is
intended to correspond to suitable core lambda/application redexes; it is not a
constructor of `core.Term`, and no translation or simulation is proved. The core's
unified binder namespace also still needs an explicit correspondence with this
model's two namespaces.

The reduction is pure substitution. It may duplicate or discard a let argument,
and it reduces underneath a let. It does not model call-by-value evaluation,
single evaluation, overflow traps, effects, ownership or quantities. Finite scope
also does not establish numeric ranges, subtraction evidence, universe formation
or proposition truth. General value-dependent domains remain future work.
Conversion-aware typing and logical inhabitation are established separately below,
not silently supplied by the scope judgment.

## Conversion-aware typing and logical consistency

`Ty.Conv` lifts the arithmetic `Conv` relation through array lengths, `Lt` and `Eq`
indices and natural-index Pi bodies. Scalars convert only to the same scalar
constructor. Reflexivity, symmetry, transitivity, substitution stability and Pi
injectivity are proved. `view_sound` shows that converted types have equal
structure and evaluated natural indices under every valuation, including every
argument of a Pi. This is semantic soundness of the chosen equations, not a claim
that every equation succeeds in the actual compiler's normalizer.

`HasType.convert` may occur **anywhere** in a typing derivation. The index/value
substitution proofs now include conversion, and `contextConversion` permits
replacing context entries with convertible types. The revised preservation proof
uses conversion-aware lambda inversion: the lambda's original body type may only
be convertible to the function type expected by the application. That conversion
is transported through argument substitution before concluding the beta case.
Finite-context preservation continues to follow from typing and scope preservation.

`ScopedTyping.convert` explicitly requires its new result type to be scoped.
Arithmetic conversion alone does not preserve scope: reversing
`(0 + x) - x = 0` can introduce an otherwise unused free x. A regression demonstrates
that the raw typing judgment can use this conversion while the finite judgment
rejects its out-of-scope result. Finite scope constrains the context, term and
final type; the enclosed raw typing derivation may still have intermediate types
with additional free indices. Equivalence to a typing derivation whose every
intermediate type is scoped has **not** been proved.

### Logical interpretation

`Semantics.lean` interprets the modeled scalar types as `Nat` and `Int`, an array
of length n as `Fin n → Int`, propositions as lifted natural-number comparisons
or equalities, and a Pi as a dependent function over mathematical naturals.
Substitution commutes with this type interpretation, and type conversion gives
equal interpreted types.

`HasType.realize` proves that a typing derivation has an **inhabited result type**
whenever its context entries have inhabited types. It recurses on the actual typing
derivation, with no rule assuming semantic validity of an arbitrary conclusion.
For a proposition result this supplies evidence that the proposition is true.
It uses Lean's standard `Classical.choice` to assemble a Pi inhabitant from
pointwise inhabited result types. This is a classical logical interpretation,
not constructive extraction.

The resulting theorems quantify over every term of this calculus:

- `no_closed_false_bound`: no `ScopedTyping 0 [] t (Lt(0, 0))` exists.
- `no_closed_false_equality`: no `ScopedTyping 0 [] t (Eq(0, 1))` exists.

These consistency results include arbitrarily nested index lambdas, value lets
and internal conversions. They are stronger than the first arithmetic-derivation
result, but still concern this restricted calculus only.

The interpretation supplies `Nonempty` types, not a fixed valuation of concrete
parameter values. It does not associate a particular term with a particular
semantic result, require repeated parameter uses to choose the same witness, or
show that reduction preserves a result value. Consequently it proves neither
operational adequacy, executable array bounds safety, normalization nor generated
code correctness. General dependent domains, universes, proposition families and
eliminators, the remaining core evidence rules, and a core translation remain
outside these theorems.

`ConversionExamples.lean` exercises conversion around both a lambda and a whole
application, dependent Pi instantiation, converted let/array/index evidence,
convertible context entries, finite-scope conversion, non-convertible false
propositions/type constructors, and both universal consistency corollaries.

## Reproducing the checks

The project pins Lean 4.34.1 in `proofs/lean-toolchain` and uses only its bundled
standard library, with no downloaded Lake packages or mathlib dependency.

With that Lean toolchain and Python 3 on `PATH`:

```sh
bash proofs/check.sh
```

With the repository's pinned Nix inputs:

```sh
nix build .#checks.x86_64-linux.lean-proofs -L
# On an aarch64 host, use checks.aarch64-linux.lean-proofs.
nix flake check -L
```

The proof check also regenerates the core bridge fixture and compares it with its
checked-in canonical copy. The existing two-target CI runs `nix flake check`,
including this derivation and the actual compiler's core suite. The
Lean package version provided by Nix must match `lean-toolchain`; a toolchain
upgrade must update and recheck both rather than silently changing proof behavior.

`check.sh` rejects build warnings, checks the toolchain, and inspects the elaborated
axiom dependencies of 444 selected public guarantees in `Audit.lean`. Only Lean's
standard logical axioms (`propext`, `Quot.sound`, `Classical.choice`) are permitted.
The current proofs use `propext` and `Quot.sound`; the logical inhabitation
and its consistency corollaries also use `Classical.choice`. No admitted proof or custom axiom is accepted as a dependency of these theorems. This still
trusts Lean's kernel and standard logical foundation, as well as the toolchain
used to run it. The theorem audit is an explicit list, not a ban on every unused future declaration: add new public guarantees
to both that list and its expected count.

## Representation bridge

A [separate checked representation bridge](core-bridge.md) translates bounded,
annotated inputs into selected actual core constructor shapes, unifies the binder
namespaces, and proves scope/renaming and numeric certificate properties. It has
explicit erasure back to the modeled syntax and generates textual fixtures checked
by the actual compiler. A restricted annotation-checking source judgment now
translates to an independently defined unified-target typing judgment, including
dependent application and mixed value/index binders. Closed corollaries remove
context-correspondence premises and connect source typing to the earlier calculus.
The target is ghost-mode and universe-free. Executable-checker correspondence,
target preservation and runtime correctness remain separate obligations.

## Graph artifact certificates

A [separate certificate check](graph-certificates.md) validates decoded snapshots
of actual core shifts and substitutions against the unified formal operations.
It checks the entire original graph remains a prefix of the final graph. This
certifies specific exported artifacts, not every compiler execution or typing of
those artifacts. Exporter fidelity and association with the invoked implementation
remain trusted. A canonical byte codec now proves roundtrip and injectivity,
and replay certificates bind exact graph/root continuity and an independently
requested operation. The real replay driver reconstructs its graph solely from
the retained validated artifact; its importer and invocation remain trusted.

## Remaining obligations

A [data-only typing-certificate checker](typing-certificates.md) now derives
closed beta-aware target typing and formation from accepted graph artifacts. Its
canonical snapshot-bound interface checks the exact exported graph and roots.
There is still no map from all accepted core programs to either `Derives` or
`HasType` with a proved executable-checker refinement theorem. Full soundness requires the remaining term syntax, universes, ghost/code
positions, dependent functions, families and elimination, followed by preservation
and full consistency. Quantity rules need an execution model of ownership and
scoped borrows. Erasure and runtime normalization must be related to the pure model,
with traps specified, before lowering can be connected to a semantics of MIR.

Finite rejection, preservation and differential tests remain implementation
regressions. They are not replaced by these proofs, and they do not discharge the
missing correspondence. The [roadmap](roadmap.md#the-050-release-gate-for-the-native-core)
continues to distinguish these obligations and their trusted implementation boundary.

## Historical target substitution and head beta

The unified target judgment can be studied without changing its rules or claiming
that the executable core checker implements them. Renaming and typed substitution
transport a derivation through a precisely stated context relation. Substitution
requires each replaced variable to have its substituted type in the destination
context; it does not assume typing of the final transformed term.

The useful beta statement is **head beta**: a typed application of a lambda to a
typed argument can be replaced by capture-avoiding substitution into its body.
Its result type is instantiated by the same substitution. This is separate from
an unrestricted contextual-reduction theorem.

### Why the historical conversion cannot preserve contextual beta

The target's deliberately small `Raw.Conv` has numeral addition and selected type
congruence, but no beta or application conversion. In the empty context, write:

```text
a = (lambda y : U64. y) 0
f = lambda x : U64. refl x
```

The term `f a` has target type `Eq(a, a)`. Reducing its argument gives `f 0`, with
result type `Eq(0, 0)`. The historical target conversion cannot identify those two
types. Thus full fixed-type contextual beta preservation is false for these
unchanged rules. This is a limitation of the selected declarative target, not a
counterexample to the implementation's richer normalization-based conversion.
A broader preservation theorem needs a justified richer conversion model or a
statement that explicitly transforms types as well; neither is silently assumed.

Arbitrary target contexts also need not contain well-formed types. A context that
maps variable zero to the raw numeral zero allows that variable to be typed at a
non-type. Structural transport can remain valid under its exact context premises,
but does not establish general type-formation regularity or consistency. Likewise,
proposition classification is stable under substitution of a formed type, not of
an arbitrary raw term: replacing a raw variable with an equality changes that
classification.

The paired executable-core fixture
`tests/core_preserves/lean-target-contextual-boundary.jhc` checks both expressions
against the same unreduced equality type. The actual checker and preservation
regression accept both, exercising precisely the richer conversion omitted from
the target judgment.

The public transport endpoints are `Raw.IsType.renaming/substitution` and
`Raw.HasType.renaming/substitution/instantiate/head_beta`. The examples include an
open replacement under mixed ordinary/erased binders, a nonreflexive arithmetic
conversion around a head application, and accepted typed shift/substitution
certificates. `dependent_after_not_original_type` kernel-checks the closed
contextual limitation above as failure of the original typing judgment, not only
failure to find a conversion proof. The existing judgment and conversion
definitions are unchanged.


## Beta-aware target conversion and contextual preservation

The separate `Raw.Beta` namespace extends the target model, without changing the
historical `Raw` judgments or the compiler. Its conversion relation includes
capture-avoiding beta equivalence and congruence for every selected constructor,
including both parts of Pi and lambda binders and array elements. It retains only
non-overflowing closed numeral addition as an arithmetic computation rule. It does
not equate open machine arithmetic with unrestricted mathematical arithmetic.

This extension requires more than adding a beta rule to the old proof. A lambda's
type may now be converted through other raw expressions, so the historical Pi
rigidity lemma no longer applies. The new conversion development uses parallel
reduction and complete developments to prove the diamond property, confluence,
and a common-reduct characterization. Pi injectivity follows from that argument;
it is not a supplied axiom or a premise of preservation.

The beta-aware typing rules otherwise follow the restricted target judgment.
Renaming, typed substitution, and conversion of current-scope context entries are
proved again for the extended rules. Legacy derivations embed into the new model.
Formation and typing preservation are proved together. In particular, changing a
lambda annotation transports its body derivation to the converted context and
preserves the erasedness classification of the **formed annotation**. Arbitrary
raw conversion is not assumed to preserve that classification.

`Raw.Beta.HasType.preservation` keeps the exact original result type through one
contextual beta step; `preservation_steps` covers finite sequences. Steps may occur
in dependent application arguments, binder annotations and bodies, indexed types,
evidence, and array elements. The former dependent-argument counterexample is now
typed at its original equality type. Negative examples keep distinct type heads
and binder erasedness separate. This is a theorem for beta reduction and its
compatible closure, not for all arithmetic, array indexing, or compiler reduction
rules. It proves neither termination nor progress, and does not establish global
consistency for arbitrary contexts.

The graph-certificate typing variants use the new judgment, while retaining the
same explicit input/replacement typing and context-transport premises. Certificate
acceptance still checks structural transforms rather than these typing premises.
The exporter, importer, execution association and checker-refinement boundaries
are unchanged.

### Comparison with the executable core

In `compiler/core.jh`, pure `Core.normal` contracts an application of a lambda by
`Core.substitute`, and normalizes Pi/lambda annotations and bodies, arrays, bounds
and equality indices. `Core.equal` normalizes both terms before `identical` compares
them. The model's beta and constructor congruence rules follow this pure behavior;
`tests/core_preserves/lean-target-beta-conversion.jhc` exercises dependent argument
conversion, erased binder annotations, open substitution and array lengths in the
actual checker and preservation regression.

These finite tests are not a proof that every Lean conversion is accepted by the
executable checker. The implementation has finite depth/work limits, mutable
bounded graphs, a broader constructor set, additional computations and proof
irrelevance. Conversely, the Lean relation is not a decision procedure for the
implementation. The runtime mode also retains certain effectful arguments and
tracks traps with `Strict`; the pure beta theorem does not model that evaluator,
erasure, lowering, or generated machine code. Full compiler soundness remains open.

## Formed type shapes and conditional literal evidence

`CoreBridgeBetaShapes.lean` derives rigid-head separation and equality, bound,
array and numeral injectivity from the existing Church–Rosser theorem. It also
retains the complete higher-order Pi structure and binder flags in a type
skeleton while erasing scalar indices. `IsType.skeleton_conversion` proves that
conversion preserves this skeleton **when both endpoints are independently
formed types**. It does not interpret Pi as a function space or assume semantic
conversion soundness.

That qualification is necessary: the raw beta expansion
`(lambda x: U64. U64) 0` converts to `U64` but is not an `IsType`-formed type and
has no syntactic type skeleton. `expanded_type_not_formed` and
`arbitrary_expansion_changes_skeleton` check this boundary in Lean. No arbitrary
raw-conversion shape-invariance axiom is introduced.

`CoreBridgeBetaEvidence.lean` proves closed weak-head canonical forms and literal
truth for equality/bound evidence. The [typed snapshot observer](typing-certificates.md#closed-literal-evidence-observations)
connects those results to accepted exact bytes. Head normality or a finite
reduction witness reaching it is explicit; normalization of all typed terms is
not proved. The existing `Indexed.HasType.realize` remains a theorem about its
separate Nat-index calculus, not a semantic interpretation of arbitrary
higher-order `Raw.Beta` arguments.


## Conversion-stable higher-order simple erasure

`CoreBridgeSimpleErasure.lean` proves a structural theorem for the unchanged
`Raw.Beta.HasType`, including arbitrary higher-order domains and internal
conversion rules. It supplies a foundation for a later normalization proof;
it does not reuse the natural-index-only `Indexed.HasType.realize` theorem.

A direct syntactic skeleton cannot type every intermediate result: for example,
`(lambda x : U64. U64) 0` beta-converts to `U64` but is not itself a formed type.
`Arity A a` instead means that A converts to a structural representative with
simple type a. Structural representatives collapse U64, I64, arrays, Eq and Lt
to one base type and retain Pi domains and codomains as arrows. Arity is proved
unique using the existing Church–Rosser head discrimination and Pi injectivity.
It is stable under the full existing conversion relation, renaming and arbitrary
raw substitution, including replacement beneath binders. No normalization or
semantic soundness of arbitrary conversion is postulated.

The simple term erasure retains variables, lambdas and applications. All other
constructors become an inert atom; annotations and binder flags are discarded.
`typed_erasure` proves that a declarative typing derivation erases to a simply
typed term when each accessible raw context entry has the assigned Arity.
`ContextMatch.extend` accounts for the dependent context's weakening of both
new and existing entries. The closed theorem has no context assumption, and
the result type need not be syntactically formed. Application uses Arity Pi
inversion, uniqueness and substitution stability rather than assuming its
result has the required simple type.

`CoreBridgeSimpleSimulation.lean` proves erasure commutes with renaming,
simultaneous capture-avoiding substitution and beta instantiation. Its `HeadStep`
is precisely root beta plus function-spine closure. Each such step maps to one
simple beta step. `TypingSimpleErasure.selected_head_step` connects this relation
to successful contracts selected by the existing `HeadNormalization.headPath`.
`trace_simulation` preserves the exact certificate trace length; no successful
head contraction disappears as a reflexive step. `validate_head_simulation`
combines the accepted trace with simple typings of both endpoints at the same
simple type. `validate_erasure` derives closed simple typing from the exact
snapshot-bound typing certificate.

`accessibility_transfer` transfers accessibility of the erased term to the raw
head relation. Its accessibility premise is explicit. The erasure/simulation batch alone does **not**
prove accessibility/normalization of all simply typed terms, existence of a
normal form for every raw typing derivation, or unconditional false-evidence
exclusion. The closed-normalization layer below discharges these head-normalization and
literal-consistency obligations. The erasure regression proofs
exclude self-application and the standard closed Omega term through simple
typing, cover higher-order arguments and capture avoidance, and show that an
unformed expanded result still has Arity.

This erasure cannot establish arithmetic truth, array bounds or runtime behavior:
zero and one have the same erased atom, as do all evidence constructors. A beta
step beneath Refl or an annotation may disappear, so the one-step simulation is
not asserted for arbitrary contextual beta or `Core.normal`. There is no claim
about actual ghost-mode normalization, symbolic sum/subtraction canonicalization,
compiler erasure, generated code, exporter fidelity or full checker soundness.
No production checker, certificate format or admissible typing rule is changed.


## Closed head normalization and literal consistency

`SimpleHeadNormalization.lean` now discharges the simply typed accessibility
obligation using a logical relation indexed by simple types. Base reducibility
means a finite head reduction to a head-normal term. Arrow reducibility requires
a finite reduction to a lambda whose instantiated body is reducible for every
reducible argument. The fundamental lemma is proved by the unchanged simple
typing derivation under reducible simultaneous substitutions. Its lambda case
uses capture-avoiding substitution composition and weakening/instantiation;
higher-order arguments use the arrow relation rather than a natural-number
valuation. Substitution algebra is transferred through the proved erasure of a
syntactic Raw representation; this introduces no semantic assumption.

The fundamental lemma gives head normalization for every **closed** simply typed
term. The simple head relation is independently proved deterministic. A finite
path to a normal term then supplies accessibility of that relation, ruling out
infinite paths rather than merely selecting a terminating path. These proofs do
not postulate normalization, use `sorry`, or import a normalization oracle.

`CoreBridgeClosedNormalization.lean` combines this result with the earlier
closed typing erasure and one-for-one head simulation:

- `HasType.closed_head_accessible`: every closed `Raw.Beta.HasType` derivation
  has an accessible root-beta/function-spine reduction relation.
- `HasType.closed_head_normalizes`: there exists a finite `Beta.Steps` path to
  a term satisfying the existing `Beta.headNormal` predicate.
- `HasType.closed_literal_eq` and `closed_literal_lt`: closed evidence at exact
  literal Eq/Lt endpoints implies the literal equality/comparison, with **no**
  separately assumed normal-form or reduction witness.
- `no_closed_false_equality` and `no_closed_false_bound`: arbitrary closed
  terms cannot inhabit false literal propositions in this declarative calculus.

The last two conclusions use existing beta preservation, closed canonical forms
and Church–Rosser literal injectivity. They apply to the unchanged higher-order
Raw typing rules, including internal conversions; they are no longer limited to
the earlier natural-index-only calculus. They do not interpret arbitrary symbolic
indices as mathematical values or establish general semantic realization.

`TypingClosedConsistency.lean` transfers these conclusions through the existing
snapshot-bound typing certificate theorem. Accepted exact snapshot/certificate
bytes imply existence of a typed head-normal Raw result; an independently matched
literal type implies its truth even when the input evidence is not head normal.
The theorem does not manufacture an output graph, alter the typing checker,
relax any wire/step/resource check, or change the existing finite-witness tools.
A regression accepts a beta-reducible typing certificate, rejects its old
head-normal observation and empty normalization trace, and applies the new
literal theorem without a normalization-certificate premise.

### Exact normalization boundary

This is **head beta normalization of closed terms in the selected declarative
calculus**. Reduction stops at lambdas and non-application constructors. A lambda
can be head normal while containing a contextual beta redex, and `3 + 4` is head
normal without evaluating the sum; explicit regression proofs record both facts.
There is no theorem here of full contextual/strong beta normalization, arbitrary
open-context normalization without a context condition, arithmetic or array evaluation, compiler termination,
actual ghost `Core.normal` refinement, runtime behavior or full checker soundness.

The proof supplies no uniform step/time/space bound and no total bounded producer.
The 64-step finite certificate limit and all graph, expansion, substitution and
input-byte caps remain unchanged. The regression family of arbitrarily many
nested identity applications is covered by the mathematical theorem, including
65 applications; it does not promise acceptance by the bounded producer. Graph
export/import and IO correspondence remain independent trust boundaries. Actual
`Core.normal` still canonicalizes symbolic arithmetic and subtraction beyond the
modeled head-beta relation and requires separate correspondence work.


## Open head normalization in formed contexts

`OpenHeadNormalization.lean` extends head accessibility from closed simply typed
terms to **every simply typed term in an arbitrary simple context**. It constructs
a closed reducible inhabitant of each simple type, then a closing substitution
for the context. The existing fundamental lemma normalizes the substituted term.
A new substitution/instantiation commuting lemma proves that each original head
step remains a genuine head step after substitution. Accessibility therefore
reflects back to the original open term. Substitution may introduce extra redexes;
the proof does not assume the converse simulation or preservation of normal forms.

These simple inhabitants are not inhabitants of arbitrary dependent propositions:
all base sorts have collapsed to the simple atom. The new `FormedContext` judgment
instead describes finite dependent telescopes whose successive domains are formed
in the preceding context. Induction on that telescope supplies the existing
conversion-stable simple context correspondence. The resulting theorems are:

- `HasType.head_accessible_of_match` for an explicitly matching simple context;
- `HasType.head_accessible` and `head_normalizes` for a formed dependent telescope;
- `HasType.typed_head_normalizes`, retaining the original dependent result type
  through the existing contextual preservation theorem.

This removes closedness for **head beta normalization**, not for literal truth.
Examples cover an arbitrary open identity chain, a 65-step instance, an open
higher-order argument, and an evidence hypothesis whose type depends on an earlier
natural. A separate example deliberately hypothesizes `Eq(0, 1)`: its proof variable
is typed and normalizable, while `0 ≠ 1` still holds. Open literal consistency
would require a semantic validity condition on assumptions and is not claimed.
An explicit self-reducing untyped loop is proved to lack head accessibility
and therefore to be untypable in every formed context.

The head relation still stops at lambdas and arithmetic/data constructors. This
does not establish full contextual/strong normalization, normalization in an
arbitrary raw context without the stated correspondence, arithmetic evaluation,
source alias purity, actual `Core.normal` refinement, runtime correspondence or
full checker soundness. No certificate admission, producer fuel, graph limit or
wire format changes. All new public proof results and boundary examples are
included in the axiom audit.

## Checked actual ghost Core.normal output

`CoreBridgeComputation.lean` introduces a **separate** reduction relation with
contextual beta and non-overflowing literal UAdd contraction. The historical
beta-only `Beta.Step` and existing certificates keep their meanings. The new
relation has conversion, type-formation preservation and fixed-original-type
term preservation proofs for all its contexts, including dependent arguments,
binder annotations and evidence positions. Addition's root rule requires
`m + n < wordBound`; it is not wrapping arithmetic or symbolic sum equivalence.
The proofs use the unchanged beta-aware typing/conversion judgments.

`CheckedCoreNormalization.lean` is a bounded, proof-producing partial normalizer
for a conservative subset of that relation. A syntactic application of a lambda
contracts beta before descending into its body or argument; other contexts are
scanned left-to-right. It performs at most one contraction per scan and counts
total contractions across the entire term. Supported normal-form constructors
are variables, numeric literals, U64, I64, Array types, Eq, Lt, Pi, Lam, App, Refl
and Decide. An encountered UAdd must reach two literals whose sum fits U64;
no residual UAdd is a supported normal form. Encountered subtraction, ZeroLe,
indexing and array values are rejected.

Beta-first search admits closed calls such as `(app (lam x U64 (uadd x 1)) 6)`,
curried addition, higher-order arithmetic functions and dependent evidence.
A surviving lambda with symbolic arithmetic remains unsupported. Beta can erase
unused arguments, including an overflowing sum; no overflowing addition rule is
introduced. This is a directed proof-search strategy, not a reproduction of
Core's evaluation order. Actual Core output must still match the complete
computed result, and Core resource failure still prevents publication. Search
remains partial and bounded, without a completeness or universal termination
claim. The same size/depth/product guards run before each selected substitution.

The test adapter now invokes **actual `Core.normal(root, depth)` with runtime
mode explicitly false**. It reconstructs and re-exports a once-retained complete
input graph before invoking Core, then exports the actual resulting graph and
root. The existing beta/path and type-index modes continue using substitute;
the new schema-6 record identifies the distinct ghost normalization operation.
This difference is tested by a literal sum which Core.normal folds but the
substitute-only head replay cannot contract.

The checker independently computes a proof of directed beta/add reduction from
the certified input to a supported normal form and compares it with the decoded
actual output. It binds the complete independently supplied input/output
snapshots, both roots, initial typing certificate, requested Core depth and
proof-search fuel, and all four canonical byte artifacts. The output retains
the original type-root ID and exact decoded original type. The whole input graph
must remain an unchanged prefix, including unreachable nodes. Output typing at
that original type is derived by preservation; no output typing certificate or
mere convertibility test replaces the directed reduction proof.

### Actual-normalization resource and trust boundary

Input typing and bounded model normalization must succeed **before** invoking
Core. The proof search permits at most 64 total contractions, 8192 expanded term
nodes per scan, and depth 128. Every selected substitution is checked against the
8192-node product bound and depth bound before expansion, and every next result
is checked again before another scan. Shared graph references count repeatedly
when expanded. The fixed scan cap and per-scan/product caps bound this search;
no exact time-complexity or Lean-runtime cost theorem is claimed. Existing graph
limits (4096 nodes and 200000 expanded nodes per graph root), typing-proof limits,
64-bit canonical tokens and the 8 MiB total CLI input envelope also apply.

The independently requested Core depth must lie in 1..128. Core has its own
checking-step and node limits, and can fail even after model admission: a depth-1
sum is an explicit test. Such failures, unsupported inputs, fuel exhaustion and
invalid output yield no published bundle or downstream callback. Input files
are read once, and the immutable retained bytes are used for both invocation
and validation. The standalone producer emits only a complete validated bundle.

The pure theorem is about decoded retained artifacts and the separate declared
beta/add relation. Actual execution, importer/exporter, compiler, IO and provenance
are still tested boundaries, not formally verified source-to-model correspondence.
This is per-run result validation, **not** general `Core.normal` refinement,
completeness, bounded success for every typed term, runtime-mode correctness or
full compiler soundness. Actual Core can reorder symbolic sums and cancel
subtractions; tests obtain such actual outputs and show this checker rejecting
them outside its profile. No arithmetic rule was added to the beta-only head
normalization or consistency theorems.
