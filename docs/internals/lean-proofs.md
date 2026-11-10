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
axiom dependencies of 862 selected public guarantees in `Audit.lean`. Only Lean's
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

## Symbolic natural-sum result validation

`LinearNaturals.lean` adds an independently defined first-order fragment:
scoped natural variables, word-sized natural literals, and addition. Its
coefficient normalizer has a proved all-environment evaluation theorem.
Equal coefficient records imply equal mathematical-natural values, with an
independent structural `Evaluates` relation and a determinism theorem. The
extractor supplies exact Raw representation witnesses and derives both input
and output `Beta.HasType` judgments at `U64`; output typing is not an assumption.

`CheckedLinearNormalization.lean` connects this arithmetic checker to retained
actual-core graph snapshots. `validateBytes_sound` binds canonical input,
output and operation-record bytes, including both root IDs and whole graphs.
It also preserves the input graph prefix and exact scalar type root, and proves
that the decoded expressions have the same value for **every** natural-valued
variable environment. This covers symbolic reordering and wide ghost sums that
remain outside the directed beta/add validator's profile.

The caller supplies a context arity of at most 128; variables must fall within
that context and all have type `U64`. The integration test extracts open bodies
from real-core checked scalar lambdas, then runs actual ghost `Core.normal` on
those retained body roots. Selecting those roots and the arity is a tested
adapter boundary, not a proof about source elaboration or lambda application.
The operation record retains the existing version-6 depth/fuel fields; arity is
an independent semantic-context parameter, and this checker performs no
fuel-indexed reduction search.

Before graph expansion, the profile caps each selected tree at 8192 occurrences
and the sum of expanded sizes of **all** graph nodes at 131072. Repeated
references count repeatedly. Existing 4096-node, depth-128, payload and
backward-edge bounds apply, as do canonical 64-bit tokens and the CLI's 8 MiB
input limit. These are executable resource guards, not a proved runtime bound.
The input gate runs before Core; the exact output is checked before publication.

This checker proves semantic equivalence, **not** a directed reduction or that
the output is normal. An unchanged valid input is intentionally an acceptable
semantic result. It does not prove that the recorded operation actually ran:
import/export, compilation, execution provenance, IO and Python association
remain tested trust boundaries. No rules are added to `Beta.Conv`; arbitrary
dependent conversions, subtraction, higher-order application, effects and
runtime overflow/traps remain outside this fragment. The existing beta-only
consistency and normalization theorems are unchanged. No completeness or
universal success claim is made for `Core.normal` or the coefficient checker.

## First-order evidence with symbolic conversion

`LinearEvidence.lean` defines an independent `Derives` judgment for `refl`,
`zeroLe`, closed computed `decide`, and non-erased `U64` lambdas. Its propositions
are equality or strict order of linear-natural expressions, optionally under
nested natural quantifiers. `Converts` compares corresponding coefficient
normal forms; its soundness theorem proves logical equivalence for every
natural environment, including beneath quantifiers. `Derives.sound` then proves
that every derived proposition holds. It does not assume semantic soundness of
unrestricted raw beta conversion.

The proof-producing `infer`, `parseFormula` and `check` functions reconstruct an
exact proposition and derivation from Raw syntax. Evidence is checked, rather
than accepting any term merely because the requested proposition is true.
`Formula.formed` separately establishes formation of the encoded proposition
in the existing `Raw.Beta.IsType` judgment. This is **not** a theorem that the new
`Derives` judgment implies `Raw.Beta.HasType` at the converted type: the latter's
conversion relation has not been extended with symbolic arithmetic. The later
[closed primitive safety extension](#closed-local-array-and-subtraction-safety)
adds a `zeroLe` typing rule to `Raw.Beta.HasType`, but does not identify these
two evidence judgments or extend the typing-certificate rule language.

`CheckedLinearEvidence.lean` applies this checker to a closed retained snapshot.
`validateBytes_sound` identifies the entire canonical artifact and both exact
requested root IDs, reconstructs a closed formula and derivation, and establishes
its truth in every natural environment. Its literal-equality and literal-order
corollaries reject false closed claims. The semantic model permits mathematical
natural sums above a word; each literal leaf still lies below the word bound.

The CLI reads one artifact once, with the existing canonical token, 8 MiB,
4096-node, depth-128 and graph-validity checks. Before expansion, it reuses the
8192 selected-tree and 131072 total-expanded-graph guards, charging repeated
references and unreachable nodes. Inference and conversion traverse only those
bounded syntax trees; no beta search or general proof search is introduced.
These defensive checks do not constitute a formal implementation cost theorem.

The real-core suite builds the exporter against the current `compiler/core.jh`,
runs actual `Core.check`, `Core.infer` and `Core.require`, and validates the
once-retained result before publishing it. This is a per-artifact correspondence
check on successful executions, not a proof of the implementation. Source
parsing, export fidelity, compiler execution and IO association remain tested
boundaries. A snapshot is the complete submitted claim, not an authenticated
record tied to an independently supplied source or graph: another valid graph
can also pass when its roots are requested. Invalid unreachable nodes and root
mismatches are rejected; harmless valid unreachable nodes need not be rejected.

Arbitrary applications, beta-equivalent proof terms, proof hypotheses,
higher-order domains, subtraction and other arithmetic, runtime behavior and
full checker soundness are outside this profile. Existing general Beta typing,
normalization and consistency theorems are unchanged.

## Principal inference correspondence for first-order evidence

`CorePrincipalEvidence.lean` connects the first-order `Derives` judgment to a
more restrictive `Principal` inference model whose types follow the selected
actual `Core.infer` cases. `refl a` infers exactly `Eq a a`; `zeroLe a` infers
exactly `Lt 0 (a + 1)`; `decide a b` retains exactly `Lt a b`; scalar lambdas
retain the recursively inferred body type. There is no conversion rule inside
`Principal`, and its encoded type is unique. This is a selected inference-shape
model, not a theorem about principal types for the whole language.

The additional obligation is `DecisionBounded`: every computed comparison has
two word-representable values. `principal_iff` proves that a principal derivation
followed by first-order coefficient conversion exists exactly when the earlier
`Derives` derivation and this obligation both hold. `Principal.bounded` proves
the obligation for results of the new checker; callers do not supply an assumed
proof of it. `closed_reduces` also connects closed coefficient normalization to
the existing directed `Raw.Computation.Steps` relation: a closed sum below the
word bound reduces by bounded addition to its literal value.

This restriction is necessary for correspondence with actual code. The earlier
semantic evidence model accepts `decide 0 (MAX_U64 + 1)` as a true mathematical
inequality, but `Core.infer` requires normalization to two `Natural` nodes and
rejects that expression with its closed-inequality diagnostic. The new model
rejects it too, while retaining wide sums in `refl` and `zeroLe`. Regression
proofs and real-core tests preserve this distinction rather than silently
narrowing the earlier semantic theorem.

`core_typing_snapshots.jh both` freezes the declared and actual inferred type
roots in the same post-`require` graph. `CheckedCorePrincipal.lean` requires
identical whole graphs, identical term roots and the three independently
requested root IDs. The inferred type must be structurally identical to the
model's principal type, not merely convertible or true. Only the declared type
is checked by proved coefficient conversion. The canonical-byte theorem derives
the principal judgment, declared `Derives` judgment, comparison bound obligation,
truth for every natural environment, and declared type formation. The CLI
retains the existing byte, graph, depth and expanded-tree limits before inference.

This remains per-run validation. The conditional bridge is a theorem about
explicit Lean models; it does not assert that every compatible `Derives` term
will be accepted by the executable checker. Core's allocation/resource limits,
normalization and equality implementation, parser, exporter, compilation and IO
provenance are not formally verified. No general `Beta.HasType` or `Beta.Conv`
soundness is assumed or established. Arbitrary beta applications, higher-order
domains, proof hypotheses, subtraction and runtime behavior remain excluded.

## Capture-avoiding first-order application

`LinearSubstitution.lean` proves substitution for scoped natural expressions
and quantified formulas. Substitution lifts the argument under each retained
quantifier, preserving its free variables. Encoding commutes with the existing
`Raw.subst` and `Raw.single`; semantic substitution commutes with environment
extension. Open-variable regression proofs demonstrate that omitting the lift
would change a false proposition into a true one, and cover two retained binders.
These are general scoped substitution theorems, not closed-instance tests.

The `Applied` judgment extends the earlier evidence model compositionally with
natural-index application, scalar lambdas and proved coefficient conversion.
`Applied.sound` derives truth for all natural environments using the substitution
lemma. It permits only natural arguments, not higher-order or proof arguments.
The historical `Derives`, `Principal`, general Beta typing and conversion
judgments are unchanged.

`CheckedFirstOrderApplication.lean` validates one selected **closed** application
from four retained actual-core observations: function inference, normalization
of that function type, application inference, and the requested type. The test
exporter's `apply` mode freezes all four in one final arena. The explicit
normalization observation is a separate actual Core call; it is not asserted
to expose the internal execution trace of the earlier application inference.
The validator instead checks the relationships between the returned data:

- All complete graphs agree, all six requested roots match, and the selected
  application node points to the exact retained function root.
- The function has the exact first-order principal type. Its observed normalized
  type is a natural Pi whose coefficient conversion is proved sound.
- The argument is a closed linear-natural expression with derived `U64` typing.
- The actual inferred application type equals the exact capture-avoiding Raw
  substitution of the argument into the observed Pi body. Merely convertible
  output types do not satisfy this equality.
- The requested type follows by proved coefficient conversion, yielding an
  `Applied` derivation, truth in every natural environment and type formation.

The normalization observation is checked for semantic equivalence, not for
normality. Execution/export provenance remains outside the pure theorem. The
checker does not assume general normalizer correctness, source typing soundness
or unrestricted Beta conversion consistency. It also does not derive general
`Beta.HasType` for the applied proof term; its semantic evidence judgment is
explicitly `Applied`.

Existing graph, byte, token and depth limits apply to every observation. Before
constructing the substituted formula, an additional conservative product guard
requires `(body size + 1) * (argument size + 1) <= 8192` and a combined depth at
most 128. Repeated occurrences are charged. A regression has individually valid
bounded trees but fails this product guard even with an unused argument. These
are executable resource defenses, not a formal time/memory cost theorem.

The compositional model is broader than this single-application artifact checker: it
requires its function term to pass the prior principal profile, so a
function that is itself an application is rejected. Applications under an open
outer context, arbitrary higher-order functions, proof arguments, subtraction,
runtime traps/effects and general compiler refinement remain outside the
executable validation profile. Partial applications returning natural-quantified
evidence and wide ghost-natural arguments are covered by actual-core tests.


## Retained application spines

`CheckedApplicationSpine.lean` closes the single-application checker's rejection
of a function that is itself an application. The exporter first walks the
selected application spine back to its base function. It obtains one principal
inference observation, then normalizes the saved current type and infers the
next selected application, proceeding from the innermost call outward. These
are explicit actual Core calls, not instrumentation of Core's internal trace.
The returned roots are retained unchanged. All observations are serialized only
after the last call, against one complete frozen arena. Repeated inference can
allocate equivalent but distinct type nodes; the new result root is retained,
not replaced with the earlier result from the initial whole-program check.

A proof-carrying state contains the exact previous snapshot, decoded term and
formula, remaining work budget, and an `Applied` derivation. Only the base is
seeded from `Principal`. Each link checks the complete graph, the normalization
observation's term root, and the exact previous term ID in the next `App` node.
Coefficient conversion justifies the observed Pi type, and capture-avoiding
substitution must equal the next inferred type structurally. The resulting
`Applied` derivation and exact output snapshot become the next state. No
intermediate output typing premise or independent principal certificate is
assumed. The final requested type follows by proved coefficient conversion.
`validate_sound` derives this chain and truth of the final formula for every
natural environment. `validateBytes_sound` binds all retained canonical
snapshot bytes to the same result; it does not establish their source provenance.

The public validator accepts 1–16 links. Each snapshot retains the existing
whole-graph, expanded-tree and depth bounds, and each substitution retains the
8192 product / 128 depth guard. An additional budget of 32768 charges
`(body size + 1) * (argument size + 1)` **before** every substitution, including
unused arguments and repeated graph references. The state deducts this charge
and carries the remainder to the next link; `Chain.remaining_le` proves that
successful chains cannot increase it. The CLI limits the total input to 8 MiB
and at most 34 snapshots before parsing individual snapshots. These conservative
bounds are executable defenses, not an asymptotic cost or completeness theorem.

Actual-Core tests cover curried calls with two and three arguments, remaining
dependent binders, symbolic conversion, wide ghost sums and the 16-link boundary.
Graph-valid tamper tests have repaired passing controls. A repeated-reference
fixture passes each substitution in isolation and a seven-link prefix, while
its eight-link chain fails the cumulative budget. Failed source checks, nonzero
exporter exits with valid stdout, and failed validation prevent publication,
including with Python assertions disabled.

This is a per-artifact extension of the closed, first-order natural-index
profile. Higher-order/proof arguments, subtraction, open-context applications,
runtime evaluation, ownership and traps remain excluded. Observed normalization
is checked for semantic equivalence, not normality. The parser, exporter,
compilation and execution/IO association are tested boundaries. General
`Beta.HasType`, unrestricted conversion consistency, completeness of the actual
checker and full compiler soundness are neither assumed nor established.


## Closed propositions with higher-order proof assumptions

`PropositionalEvidence.lean` adds a separate evidence judgment for functions of
proofs. Its types are closed formulas from the linear-natural profile and
arbitrarily nested proof arrows. Thus `(P -> Q) -> P -> Q` and composition of
proof functions are expressible, including natural-quantified premises. Every
arrow binder is erased. Contexts contain proof assumptions only; they are not
mixed natural/proof telescopes. Closed principal evidence can be used under any
proof context, and a quantified proof function can be applied to a closed
linear-natural argument.

`Derives.sound` requires semantic validity of every assumption in the context.
Proof-variable lookup uses its exact de Bruijn position; implication introduction
extends that context and elimination consumes evidence for the domain. Proved
coefficient conversion extends recursively to proof arrows. Empty-context
soundness follows without assumptions. The examples deliberately derive a false
proposition from a false hypothesis, and prove `False -> False`, while separately
proving that no closed derivation inhabits `Eq 0 1`. These distinctions prevent
silently treating arbitrary open contexts as semantically valid.

`Ty.subst_closed` proves that every admitted type is unchanged by **any** raw
substitution. In particular, the codomain of a proof arrow cannot depend on the
proof as a natural index. Applying a natural-quantified premise instead uses the
existing proved capture-avoiding index substitution. `Ty.proposition` and `Ty.formed` also prove proposition classification and type
formation in the existing Beta model, in any surrounding raw context. These do
not imply term typing or semantic soundness of general Beta conversion. The
model does not assume unrestricted Beta conversion or general `Beta.HasType` consistency.

The executable inference function returns its derivation, remaining budget and
a proof that the budget did not increase. It counts visits and charges natural
substitution before expansion, with 128 recursive fuel, an initial budget of
32768, the existing 8192 substitution-product / 128 depth guard, and an 8192
size cap on newly formed arrow types. The artifact checker applies the existing
whole-graph/tree limits before inference. These are conservative resource
defenses, not a universal normalization or complexity theorem.

`CheckedPropositionalEvidence.lean` checks the unchanged actual-Core `both`
exporter's retained requested/inferred snapshots. Complete graphs and selected
roots must agree; the actual inferred type must equal the modeled inferred type
**structurally**. Only the requested type may differ by proved conversion.
Canonical-byte soundness supplies a closed evidence derivation and truth of its
requested proposition, which may itself be a higher-order implication. No output
typing premise is supplied by the producer.

Actual-Core regressions cover identity, weakening, modus ponens, higher-order
composition and application, quantified hypotheses, false hypotheses, wide ghost
sums and converted proof arguments. Graph-valid tests distinguish two different
hypothesis slots and require a repaired output type to restore acceptance.
Individual substitutions and a seven-call prefix pass where an eight-call chain
exceeds its cumulative budget. Failed source checking, failed exporter exits with
valid stdout, and failed validation cannot publish a result, including under
Python optimization.

This is an extension of the semantic evidence fragment, not general higher-order
dependent type soundness. Mixed scalar/proof contexts, scalar lambdas whose body
uses a surrounding proof hypothesis, erased natural-index binders, runtime
function arguments, global definitions, induction and subtraction remain outside
this profile. Core can normalize a Pi before application and return a structurally
different inferred type; such a run is conservatively rejected here even when its
result is convertible. The application-spine profile separately validates explicit
normalization observations for its supported scalar calls. Export provenance,
compilation, runtime/ownership behavior and full checker refinement remain
unverified. The source compiler and its acceptance rules are unchanged.


## Closed local-array and subtraction safety

`CorePrimitiveSafety.lean` connects higher-order closed typing to two primitive
safety consequences. A closed array producer reaches an `Elements` constructor
by the existing head-beta normalization theorem. For a typed `Index` with a
natural literal index, closed less-than consistency derives its actual bounds,
a selected entry exists, and that entry has the original, possibly converted,
result type. For `USub` with literal operands, typing derives non-underflow,
a representable result and result typing. Neither theorem assumes normalization
of evidence or a true bound from its caller.

This batch extends `Raw.Beta.HasType` with the executable core's `ZeroLe` rule.
Renaming, substitution, beta and bounded-add preservation, simple erasure, closed
head normalization and literal consistency all cover this added rule.
Church–Rosser proves that an arbitrary raw successor `a + 1` cannot convert to
zero; no semantic interpretation of arbitrary higher-order arguments is assumed.
The subtraction proof handles the maximum word separately using operand bounds,
so it does not truncate or assume representability of the ghost bound `MAX + 1`.

`ArrayRead` specifies selection after head-beta preparation; it is not a new
`Core.normal` reduction rule. The evaluated-operand corollaries require explicit
finite contextual beta/add/subtract evaluations. These results do not prove universal
arithmetic normalization, heap/borrow safety, quantity soundness, or
erasure/lowering adequacy. Contextual local-array read preservation is added below.
They cover the stated `Raw.Beta` fragment, not the whole specified calculus.
Existing certificate formats and their admitted rules are unchanged.

`CorePrimitiveExamples.lean` packages closed typing derivations with examples
containing a higher-order proof application, a computed array producer and index,
subtraction and a maximum-word erased bound. `EmitPrimitiveSafety.lean` serializes
their exact terms; `check.sh` compares the output with the committed core fixture.
The serializer and textual parser are tested boundaries, not verified translations.
`tests/core_primitive_safety.py` checks the fixture with the actual kernel and
preservation checker, compiles both object targets at O0/O2, executes host results,
and checks paired invalid programs against working controls and intended type
diagnostics. It also distinguishes an erased overflowing bound from a runtime
addition that traps. These finite tests support correspondence with the trusted
implementation; they do not establish compiler refinement.


### Contextual literal subtraction and dependent conversion

`CoreSubtraction.lean` strengthens the same primitive-safety development with
actual subtraction traces. `Beta.Conv`, parallel reduction and `Computation.Step`
now contract `usub a b p` to `a - b` for literal operands when `b ≤ a` and
`a < 2^64`. The proof term is erased by this pure contraction. The untyped
relation does not require its typing; the typed closed endpoint derives both
guards from the existing typing derivation and closed bound consistency.

The extended parallel reduction has complete developments and Church–Rosser,
including the critical pair between reducing the proof operand and contracting
subtraction. Renaming, capture-avoiding substitution, rigid-head injectivity,
formation and fixed-type contextual preservation are rechecked for the extended
conversion. Closed false-bound and false-equality exclusion therefore continue
to hold with this stronger conversion, rather than being assumed for it.
Underflowing and oversized literal subtractions cannot convert to any numeral;
valid literal subtraction has a unique numeral result, even allowing arbitrary
untyped beta expansion.

`HasType.closed_sub_computes` derives a contraction and its original type;
`HasType.evaluated_sub_computes` composes finite operand traces with that
contraction. Lean-generated examples exercise nested subtraction, an array index,
an equality proof domain and contextual reduction of a lambda annotation while
preserving its original dependent function type. Native tests check eight results
at O0/O2, both object targets and paired negative controls including a wrong
subtracted equality. The maximum-word case retains its erased `MAX + 1` bound.

This models pure bounded literal subtraction already performed by `Core.normal`;
it does not change the production compiler. Symbolic cancellation, `Strict`,
effects, borrowed pointers, heap semantics and native lowering remain outside
this result. No universal normalization or whole-language soundness is claimed.
The historical beta-only `Beta.Step` and executable certificate admission rules
remain unchanged; their narrower evaluators need not find all conversions now
admitted by the declarative relation. The generated fixture checks are finite
implementation correspondence tests, not a verified parser or compiler refinement.


### Contextual local-array reads

`CoreArrayReduction.lean` closes a gap between the existing selection theorem
and the contextual computation semantics. A successful literal-index lookup in
`elements xs` now contracts to the selected term in `Beta.Conv` and
`Computation.Step`. Parallel read reduction also reduces the selected term, so
complete developments join reading before or after array-element reduction.
Church–Rosser, substitution, formation and fixed-type preservation are rechecked
for this expanded relation; closed false-proposition exclusion remains proved.

The preservation rule works in arbitrary contexts and at the original type,
including under lambdas. `HasType.closed_index_computes` turns a closed typing
derivation and a finite index evaluation into an actual read trace and a typed
result. Array head preparation, the in-range bound and proof truth are derived,
not additional premises. The result may itself need evaluation: no universal
normalization for the expanded read relation is asserted. Invalid empty or
out-of-range reads cannot convert to an integer; successful selection of an
integer has a unique integer result even through untyped beta expansion.

The generated Core fixture adds nested reads and a function taking a runtime
index plus an erased bound proof. Its Lean trace theorem gives exactly the
selected array entry after both applications. Foreign exports cannot require
erased evidence. A separately tested Core wrapper uses `if-lt` to supply that evidence to the generated helper; this wrapper
is outside the Lean syntax. Native tests check three valid reads and two rejected
indices returning a fallback at O0/O2, in addition to nine closed results, both
object targets and seven paired negative controls. No out-of-range read executes.

This is a pure **abstract read semantics**, not a claim that `Core.normal`
performs this contraction. Its `Index` branch normalizes operands but retains
the read; `compiler/core_lower.jh` lowers a local array read to a MIR indexed
place, omitting proof storage. These implementation connections are tested,
not formally refined. The abstract contraction can discard unselected entries;
it does not model the production compiler's eager evaluation, traps or effects.
No heap, borrowed-pointer, ownership, native memory or whole-language theorem
is claimed. Existing certificate admission and the historical beta-only `Step`
remain unchanged and narrower than the extended declarative conversion.


## Quantity control and partial executions

`QuantityControl.lean` starts the runtime quantity obligation with a control-flow
semantics, separate from ghost typing and pure conversion. It does not impose a
new accepted source profile. Resource events record uses of individual outer
owners. Sequential execution adds demands; nondeterministic branches must agree
for each owner separately. A known once-called continuation executes its body.
Reusable closures and repeated code must have zero outer demand. Erased code
executes no resource events. A local `bind` shifts outer resource indices and
requires demand one for its own resource before hiding its events at scope exit.
This allows each iteration to consume a new local owner while rejecting capture
of an outer owner by repeated code. Demand counts are mathematical naturals. The
checker is conservative, not complete: it also checks syntactically present code
that a particular execution might never reach.

`Finishes` describes successful finite executions. `Prefix` independently
describes partial executions, including paths ending in a trap and finite
prefixes of infinite repetition. A prefix need not extend to a successful run.
The checked-demand theorems establish:

- Every successful run has exactly the checked count for each resource.
- Every finite prefix has at most the checked count, even if it traps.
- Each local binder is consumed once on successful exit and at most once before
  interruption; discharging its scope preserves all outer resource counts.
- Demand one gives independent linear guarantees for a set of owners, and demand
  zero excludes runtime use even on partial runs.

The distinction between completion and interruption is essential: a well-checked
control can trap before using an owner. An exactly-once assertion for all partial
runs would be false. `QuantityExamples.lean` supplies that counterexample, traces
showing why branch agreement and repeated-capture checks are necessary, and
nested-binder/iteration examples. The semantics does not define a use as a free:
a move or return also uses an owner. Heap conservation and eventual deallocation
require an additional ownership semantics.

`tests/core_quantities.py` rebuilds a small probe against the checkout's actual
`compiler/core.jh`. It compares `runtime_uses` counts and kernel acceptance for
single use, duplication, discarding, balanced branches, immediate calls,
accumulator passing and trapping arithmetic. Rejected unequal branches,
escaping closures and repeated capture have successful repaired counterparts.
This is finite correspondence evidence for manually paired control patterns,
not a verified Core-to-control translation or a new certificate interface.

### Obligations connecting quantities to the whole core

The following are required before the quantity release gate is discharged:

1. Define a total, scope-preserving projection of the specified runtime terms
   into resource controls. It must follow erased argument classification,
   application saturation, constructor fields, elimination/view cases,
   continuations and dependent lends. No caller may simply label arbitrary
   code as erased, once-called or capture-free.
2. Prove that the specified quantity judgment implies control-demand acceptance.
   Resolve `uses_function`, `uses_under`, case binders and recursive accumulators,
   including the distinction between an outer owner and a newly bound one.
   Testing the trusted executable checker does not substitute for this theorem.
   Relate the implementation's bounded counters and resource limits separately;
   the natural-number model alone establishes no machine-counter invariant.
3. Give runtime operational semantics and prove every concrete finite execution
   projects to `Prefix`, and every successful execution to `Finishes`. Include
   arithmetic/allocation traps and the evaluation order retained by `Strict`.
   The current control semantics is not a model of `Core.normal` or lowering.
4. Connect resource events to unique heap ownership and moves. Add borrow leases,
   lend return and non-escape invariants; prove allocation/free conservation and
   that borrowers cannot access an owner after its lifetime. Current controls
   contain neither heaps nor borrowed pointers, so no borrow theorem is claimed.
5. Establish erasure/runtime-normalization and lowering correspondence separately.
   Pure beta preservation cannot justify duplicating effects or owned resources.

Whole-specified-core consistency/preservation, quantity/borrow soundness and
lowering correspondence remain open. This milestone supplies the path-sensitive
accounting lemmas for the second and third obligations; it does not replace them
with an assumption advertised as a completed compiler theorem.


## Mixed binders and owner aliases

The quantity control foundation now distinguishes `linear`, `erased`,
`unrestricted` and `borrowed` scope modes. `Control.bind` remains an abbreviation
for a fresh linear scope. All modes occupy a de Bruijn slot and shift outer
owners, as proved for arbitrary mixed telescopes by `scopes_outer`. Linear
locals require demand one, erased locals require zero, and unrestricted or
borrowed locals impose no local-demand check. In particular, demanding even a
*defined* local count for unrestricted binders would incorrectly reject different
use counts on different branches. The original completion and prefix accounting
theorems are re-proved for all four modes. Erased local uses are excluded even
from partial runs before a trap.

`QuantityAliases.lean` separates a variable slot from its owner identity through
scope-preserving renaming. The map may identify multiple slots; lifting it under
a scope fixes the fresh local slot and shifts every outer identity. Renaming
obeys identity and composition and transports both successful executions and
finite prefixes, without an injectivity assumption. `openOwner` identifies a
returned-owner slot with an existing outer owner and removes the slot. Its
count theorem adds that slot's uses to the chosen original owner's uses.

`AliasLinear` checks demand **after** identification. A branch that consumes the
original name on one side and the returned name on the other then has demand
one. Consuming both names sequentially has demand two and fails a linear
obligation. Summing independently checked demands would miss this distinction:
individual slot demands can be undefined on branches even though the combined
owner demand is exactly one. The mapped-trace equality and prefix bounds also
hold below nested mixed scopes.

The mapping's authenticity is an explicit remaining obligation. Arbitrarily
identifying two distinct physical owners can hide the omission of one of them;
renaming algebra alone does not authorize that identification. A future typed
projection must obtain modes from checked binder classifications and aliases
from validated dependent-lend structure. These results concern identification of
use events, **not** substitution of arbitrary effectful arguments. Borrowed mode
is unrestricted only for quantity counting and proves no borrow lease, non-escape
or lifetime invariant. No claim of whole-core quantity soundness is added.

`QuantityAliasExamples.lean` checks unequal unrestricted branch counts, mixed
scope shifts, erased use, alternate/doubled owner aliases, nested scopes and
capture rejection. It also demonstrates why an unauthenticated alias map can
hide a missing distinct owner. The actual-Core quantity probe tests checked
mixed telescopes, erased-runtime rejection, dependent lends using either owner
name, branches between names, duplicate/discarded aliases, repeated/unequal
borrow reads, and borrow escape. A separate distinct-owner rejection and its
repaired control ensure that these tests do not treat arbitrary owners as aliases.
These are manually paired finite regression cases, not a proved translation of
Core terms. The full projection, operational simulation, machine-counter,
heap/borrow and lowering obligations in the preceding section remain open.


## Binder capabilities from checked domain observations

`QuantityBinderProjection.lean` replaces consumer-chosen binder modes with a
classification of normalized domain summaries and the binder's erased flag.
Lendability here means static type eligibility, not a proof that a runtime lease
is available or that a particular live heap object is currently owned.
It distinguishes quantity mode from lend permission: `Back` is linear but not
lendable, a runtime buffer or boxed data is linear and lendable, and erased boxed
data is neither a runtime owner nor lendable. Propositions require erasure;
erasure of a non-proposition permits only U64 indices and data. Borrow domains
are unrestricted for use counting but retain their separate borrowed mode.

The executable classifier is sound and complete for an independently enumerated
`Permitted` relation. Scope and telescope projection reconstruct their modes
from those capabilities, with a theorem preserving the outer-resource offset
through every projected binder. Alias projection first checks permission for every binding in its context,
including unselected entries, and requires an in-range existing
non-erased buffer/boxed-data binding. It rejects Back, borrows, erased data and
unrestricted domains as alias-owner capabilities and composes with the existing
mapped-trace completion/prefix theorems. No consumer can override a projected
mode or turn a merely linear Back capability into a lend permission.

**Precisely conditional boundary:** these theorems take normalized-domain
summaries as inputs. They do not prove those summaries authentic, prove Core
formation or normalization, or identify the owner selected by a source Lend.
Authenticating the context and source owner remains necessary. In particular,
`other` includes neutral type expressions, functions and universes; classifying
such a binder as unrestricted is not a theorem that every possible type
instantiation is owner-free. The kernel's first-order type-argument restriction
and its stability under substitution still need a formal account. This is a
capability projection conditional on checked observations, not the completed
typed whole-Core projection or a borrow-lifetime theorem.

The test-only `core_binder_probe.jh` first runs actual `Core.check` on the complete
program, then walks the original lambda telescope. It obtains each original
annotation's sort with `Core.infer`, normalizes that sort and domain, and reads
family data/boxed classification from the checked Core state. Each binder is
added to the original contextual telescope before observing the next. Inputs
supply no mode or family flags. Invalid programs produce no observations. The
probe additionally calls actual `Core.owned`; its results are compared with the
Lean-derived lend capabilities and actual rejection of discarded linear values.

`EmitBinderClassification.lean` produces the exhaustive 18-row classifier table;
`check.sh` checks its exact committed fixture. This is a test oracle, not a new
certificate format or accepted source profile. Tests cover proof/index/scalar,
flat and recursive or heap-field data, Buffer, Back, Ref, function and universe
domains; both erasure flags; a beta-normalized Buffer annotation; dependent and
neutral telescopes; linear discard and Back lend rejection; and a runtime
first-order type-argument positive/negative pair. An invalid later binder
produces no observations from an otherwise valid telescope prefix; its repaired
control is accepted. The exporter,
constructor-summary association and trusted checker remain finite tested
boundaries, with no theorem equating arbitrary Core execution to this model.


## Rooted context and Lend owner provenance

`QuantityContextProjection.lean` adds structural provenance to the capability
layer. A bounded walk starts at one root in an immutable syntax view and an
empty context. Each original lambda supplies its domain ID, erased flag and
body ID; a contextual observer receives that exact domain ID and the preceding
raw context. The observer's classification must pass the binder permission check
before the new entry is appended. No descriptor list, mode vector or owner
index is accepted from the caller of this rooted operation.

`walk_sound` proves a path judgment retaining every original lambda edge and
contextual observation. `rooted_authentic` proves that every entry was produced
by those observations with permitted erasure. Here **authentic means provenance
relative to the supplied view and observer**, not a proof of kernel typing.
`lookup_core` identifies reverse-list lookup with Core's bounds-checked
`ctx[ctx.length - 1 - k]`; fresh/outer lookup lemmas prove that entering any
binder, including an erased binder, shifts every existing de Bruijn slot once.
Telescopes remain stored outermost first, while owner lookup is innermost first.

At the endpoint the projector requires an actual Lend view, follows its original
owner node, and requires a Var view there. The alias uses that exact variable
index and original binding, after checking the complete context's permissions
and the selected owner's lend capability. Distinct owners with equal types keep
distinct identities. `rooted_alias_origin` combines these structural facts with
the capability evidence; finished/prefix corollaries apply the existing single
alias-slot trace accounting to the supplied control body.

**Remaining boundary:** the syntax view must faithfully expose the retained Core
nodes, and the observer must correctly implement contextual formation, sort and
domain normalization and family classification. This development does not prove
those interfaces correct. The test driver performs whole-program Core.check
before observing them. No translation of a Lend reader or continuation is added:
the control body in the trace corollaries is still supplied independently. In
particular the result binder and returned-owner binder of a real continuation
must be handled separately before those corollaries describe its execution.
Non-variable owners, nested execution paths beyond the leading lambda telescope,
first-order substitution stability, heap identity, leases and borrow lifetime,
and erasure/lowering correspondence remain open. Fuel exhaustion rejects rather
than returning a partially authenticated context; no completeness is claimed.

Lean regression examples change original annotation IDs, erased flags, lambda
edges, owner nodes and indices; exercise equal-typed distinct owners; and reject
cycles, insufficient fuel and non-variable owners. The existing real-Core probe
has a `context` observation mode that retains original node IDs and checks the
exact Lend owner selection. Seven accepted dependent/mixed/multiple-owner programs move a
buffer across erased and unrestricted slots and select either of two equal-typed
owners, including a Buffer(n) annotation depending on an earlier index. Tests verify every lambda body link, selected original domain ID and
forward/de Bruijn position. Valid non-variable-owner and non-Lend programs pass
the ordinary checker observation mode but fail this projection mode with the
intended diagnostic and no partial output. These are regression evidence for
the trusted interfaces, not a mechanized implementation refinement or a new
certificate admission profile.


## Scoped Lend reader and continuation projection

`QuantityLendProjection.lean` extends rooted context provenance to a structural
execution fragment: integer/natural literals, variables, variable borrows,
ordered primitive operand sequences, and nested dependent Lends with an original
variable owner and explicit runtime lambdas. `rootedProject` derives the ambient
context from the original leading lambda telescope. It then recursively derives
reader and continuation controls from their original body nodes; callers no
longer supply those controls. `project_sound` proves the resulting `Projects`
source/control judgment, whose Lend case explicitly retains the checked
contextual preparation operation. The immutable syntax view and contextual
domain observer remain parameters.

Preparation follows the actual owner, reader, result and returned-owner nodes.
It observes the reader annotation in the ambient context, the result annotation
in that same context, and the returned-owner annotation after adding the result.
The reader must classify as borrowed, the result as a known non-borrow-holding
class, and the returned owner as the original owner's lendable class. Exact
conversion of those annotations to Ref(owner), the inferred reader result and
the shifted owner type is still supplied by whole-Core typing, not inferred
from equality of these coarse classifications.

The derived control is `seq (scope borrowed reader)
(scope resultMode (alias (owner + 1) continuation))`. The `+ 1` is essential:
returned-owner slot 0 is opened while result slot 1 is still in scope. The result
is a fresh value, with its own linear obligation when owned. It is never merged
with the lent owner. Before accepting a Lend the projector checks zero owner
consumption by the reader and exactly one by the continuation. Completion and
prefix theorems give exact-once/at-most-once owner use in the abstract control
semantics. The body-trace theorem accounts separately for reader outer slots,
continuation outer slots, and returned-owner slot 0. These events count variable
uses, not heap allocation/free operations.

Projection has both a recursion-depth bound and a threaded total-visit budget.
Sequential children share the remaining budget; repeated graph references are
charged repeatedly. Lend preparation charges the owner and three lambda
inspections in addition to the Lend node; borrow charges its owner inspection.
`project_budget_decreases` proves successful calls strictly reduce the remaining
budget. The leading telescope is separately depth-bounded. Context observation,
normalization and permission traversal have their own interface costs; this
budget is not a theorem about machine instructions or kernel normalization time.
Failures return no partial control.

The test-only native adapter first runs complete `Core.check`, retains the
original graph, and derives the structural control encoding. The Python test
checks its scopes/aliases and compares outer-owner counts with actual
`Core.runtime_uses`. Seven accepted programs exercise original/returned names,
explicit and repeated borrow reads, nested Lend, an owned reader result, and two
distinct equal-typed owners. Six programs also check exact and one-short visit
budgets. Seven invalid programs assert intended diagnostics and no output,
including reader consumption, owner duplication/discard, discarded fresh result,
and all three annotation mismatches. Valid branch and computed-owner programs
are positive checker controls for explicit projection exclusions. Lean examples
independently check source-shaped graphs, nested/result scopes, altered nodes,
erasure, malformed domains, duplicate/missing owners, shared references, cycles
and exhausted budgets. These comparisons are finite test evidence, not a proved
native-adapter refinement.

**Remaining obligations:** faithful syntax/domain observation, whole-Core typing
and the conversion checks above, and semantic correspondence with the kernel's
`dependent_lend` substitutions are assumptions/boundaries. The structural
`Projects` judgment is not Core's typing judgment. General applications,
first-class readers/continuations, non-variable owners, branches, loops,
closures and inductive eliminators are not admitted by this projector. No new
compiler source restriction is imposed: this is a proof/test component, not a
production admission gate or certificate interface. The abstract execution
semantics has not been simulated by the runtime; heap identity, lease/lifetime
safety, first-order substitution stability and erasure/lowering correctness
remain open. This is progress on scoped quantity correspondence, not whole-core
ownership or borrow soundness.


## Lend substitution and ownership projection

`QuantitySubstitution.lean` proves the substitution/projection algebra that the
scoped Lend model previously left conditional. A quantity-annotated source
`Expr` retains variable and borrow-owner identities, ordered operands, invoked
scopes and nested Lends. Its binder modes are retained annotations, whose typing
justification and stability are still required. `Represents` connects these
expressions to original graph nodes and contextual preparation;
`projects_represents` derives one from every successful existing graph projection.
`rooted_substitution_source` additionally retains the original lambda path and
authentic observer context, so this bridge does not take an unrelated control or
source expression from the caller.

Substitution replaces a variable by either another variable or a borrow of a
variable, lifting under every binder. Borrow/Lend owner positions must remain
variables; unsupported replacements fail rather than inventing an owner.
`substitution_projection` proves that successful substitution commutes with
ownership-event projection, including nested Lends. A borrow replacement removes
an ownership-use event, while a variable replacement renames it. This is not a
law for substituting arbitrary effectful expressions. In particular allocating,
freeing or duplicating a computation is outside the substitution algebra.

Partial event relabeling preserves completed and prefix traces by `filterMap`.
The unique-preimage demand theorem preserves the full checker result, including
failure from local linear/erased obligations, capture checks and branch agreement.
For reader substitution `r := Borrow(x)`, that relabeling is precisely discharge
of slot 0: every outer resource has the same demand as the original borrowed
scope. For continuation substitution `returned := shift(x, 1)`, it is precisely
`alias(owner + 1)`, leaving the fresh result distinct. The combined
`lend_demand_correspondence` theorem proves equality of quantity-check results
for every outer resource before/after both source substitutions. The substituted
completion/prefix endpoints retain exact-once/at-most-once owner accounting from
a checked scoped Lend. They range over all abstract transformed traces, not just
one test execution.

The native probe now calls the actual `Core.substitute` twice and `Core.shift`
exactly as `dependent_lend` does, after complete Core.check. It also runs
`infer_reading` and contextual `infer` on the transformed bodies. Nine checked
programs compare original and transformed quantity-annotated source trees,
projected controls and all contextual `Core.runtime_uses` counts. Cases include
explicit/repeated borrow reads, an owned result, nested Lend using both returned
and original outer names, equal-typed distinct owners, and dependent Buffer(n)
annotations with an erased proof slot. The test encoding retains borrow-owner
indices before event erasure: two different borrowed pointers have the same
quantity projection, so counts alone cannot authenticate replacement identity.
Invalid input and explicit source exclusions produce no partial output in both
observation modes. All four body projections share the existing visit budget;
native substitution and inference retain the kernel's own limits.

The comparison uses the total annotated source projection, not the conservative
guarded graph admission check. A valid nested continuation using an original
outer owner name may require its enclosing alias substitution before a local
nested-owner check can succeed. This change proves the substitution algebra and
tests that case; it does not claim that the earlier guarded graph projector is
complete or change compiler admission.

**Precise remaining boundary:** source-algebra commutation is proved, but a
mechanized refinement of native `Core.transform/substitute`, the native view
exporter and domain observer is not. Literal values and type/proof operands are
abstracted by the quantity source view; the theorem is not semantic equality of
arbitrary Core values or typing preservation. Mode stability and typed annotation
conversion under substitution remain obligations. Branches, loops and closures
are covered by the general control relabeling lemmas, but are not newly admitted
by the annotated source/graph projector. This work does not establish heap object
identity, borrow validity/lifetimes, machine execution simulation or lowering
correctness, and creates no certificate or production admission profile.


## Runtime family kinds and the mode-stability obligation

Investigating mode preservation exposed a concrete counterexample to the old
native admission rule. An identity family `F : Type -> Type` passed the plain
normal-form scan, while an abstract `F(Buffer 1)` domain was treated as
unrestricted. Instantiating F revealed a Buffer. A checked program using a
callback twice had original owner demand 1 but runtime-normalized demand 2;
re-inference of that normalized program rejected duplicate ownership use. A
single-callback control retained demand 1. No reproducer was executed.

The executable checker now additionally restricts runtime type-family expected
kinds to U64-index telescopes ending in a universe, including erased U64 indices.
This applies to variable arguments too, so forwarding an opaque higher-kinded
family cannot bypass a lambda-only inspection. The existing first-order value
scan is still required and rejects Buffer/function-producing U64 families.
Scanning lambda annotations alone would not fix the identity-family example:
Type 0 and its variable body both pass the old plain scan.

The restriction intentionally rejects some harmless families over non-U64
indices and higher kinds. Ghost type calculations, monomorphic type arguments,
normalized U64 index domains, multiple indices and variable forwarding of valid
U64 families are regression-tested as preserved. The native safety suite checks
whole-program acceptance, owner use 1 before and after runtime normalization,
re-inference, and successful object emission for positive controls. Invalid
programs must produce the intended diagnostic at both checking and O0/O2 object
emission, with no object left behind. Neither accepted nor rejected test inputs
are executed by this suite.

This is a conservative executable/specification repair, not an unconditional
Lean mode-preservation theorem. The previous observer, typed-mode stability and
normalization/substitution correspondence obligations remain explicit. Proving
that first-order kind/value admission is stable under all permitted typed
substitutions is still required for the full ownership argument.


## Mixed natural and proof telescopes

`MixedTelescope.lean` extends the finite `Indexed` calculus with an explicit
mixed telescope. `Telescope.natural` introduces a natural index;
`Telescope.proof` introduces a proof of an equality, strict inequality, or
universal quantification over naturals. Constructors add binders after the
existing telescope. A proof type must be scoped over the natural indices
already present. Proofs cannot occur in indices, and proof binders do not
increment the natural namespace. A new natural binder shifts every earlier
proof type. Proof and scalar variables have separate de Bruijn namespaces;
this is not the executable Core's unified variable representation.

`WellFormed.scoped` establishes the finite scope of all projected assumptions.
`Valid` builds environments in binder order: a natural extends the valuation,
while a proof requires a realization of its assumption at that valuation.
`Valid.valuation` derives the environment premise required by the existing
`HasType.realize` theorem. `Derives.sound` therefore establishes truth of a
derivable proposition in every valid environment, without assuming truth of
the conclusion. An inconsistent assumption context need not have a valid
environment; the theorem does not claim otherwise.

`Derives.substitution` combines capture-avoiding scalar and proof substitution.
Its `Substitutes` premise requires a scoped scalar mapping and a syntactically
typed replacement for each actual source proof, at the scalar-substituted type.
The target telescope must be well formed. There is no premise requiring the
substituted conclusion to be true or typed. `finite_value_substitution` removes
the earlier total-context substitution obligation: entries beyond the finite
source context use a harmless natural default, inaccessible to scoped terms.
`natural_instantiation` and `proof_instantiation` discharge the newest binder
of each kind. The underlying substitution shifts inserted proofs beneath
natural lambdas and value binders. Closed false strict bounds and unequal
literal equalities have no derivation in the empty telescope.

`MixedTelescopeExamples.lean` checks interleaved natural/proof/natural/proof
contexts, rejects forward references and missing proof variables, and composes
proof discharge with scalar discharge beneath a retained natural lambda.
`tests/core_mixed_telescope.py` independently exercises the actual checker on
seven accepted controls (both `check` and `preserves`) and seven rejected
variants with specific expected diagnostics. These include incorrect capture,
incorrect proof endpoints, unbound references and false propositions. The test
runs no input program and emits no runtime artifact. CI runs it against the
built compiler. These tests are correspondence evidence, not a parser, checker,
or normalization refinement theorem.

The theorem concerns the existing `Indexed` typing and conversion relations.
Natural indices are mathematical `Nat`, not bounded machine words. Universal
proofs quantify over naturals; arbitrary type domains and proof-dependent types
are excluded. This milestone does not add proof-domain lambdas to `Indexed`,
model arbitrary higher-order Core conversion, or prove whole-language
consistency. It makes no runtime, ownership, borrowing, erasure or lowering
claim. The pre-existing realization theorem uses Lean's standard classical
choice; the axiom audit continues to reject admitted or additional axioms.

### Constructing the unified Core context

`MixedTelescopeBridge.lean` connects representable mixed telescopes to the
existing `CoreBridge.SourceTyping` judgment. Its telescope uses the bridge's
bounded-literal `Index` and annotated `Ty` syntax. Erasure maps it into the
semantic telescope above. `erase_proofs` proves that weakening each previous
proof type across natural binders commutes with this erasure.

The unified `Raw.Context` is constructed recursively, using `Context.extend`
for both binder sorts. `context_match` proves all required lookup facts; callers
no longer have to posit a matching target context. The index and proof maps are
proved equal to the existing mixed-layout `slot` functions, and in-scope
variables from different namespaces cannot alias. `translate` then obtains
`Raw.HasType` from the source derivation. Independently, `erase_derivation`
obtains the semantic mixed-telescope judgment, and `semantic_sound` establishes
its conclusion in every valid environment. No premise assumes target typing or
truth of the conclusion.

`close_typed` wraps a typed body in lambdas for the whole telescope. Each
annotation is encoded in its original prefix scope, rather than the final
scope after later binders. `closed_translation` consequently produces a closed
Raw typing derivation from the same source witness. This construction handles
interleaved natural and proof binders, including proof assumptions universally
quantified over naturals, without adding proof-domain lambda syntax to Indexed.

`MixedTelescopeBridgeExamples.lean` packages every generated example with its
well-formed telescope, proposition formation and source typing derivation.
`EmitMixedTelescope.lean` serializes three such declarations: selecting an earlier
equality proof across later binders, selecting the newest strict-bound proof,
and instantiating a universally quantified proof across a later natural binder.
The Lean check regenerates `tests/core_preserves/lean-mixed-telescope.jhc` and
compares it byte for byte. Nix includes both the emitter and fixture explicitly.
The actual checker tests the generated declarations and closed instantiations,
as well as four single-location mutations for scalar capture, proof swapping,
reversed bound annotations and universal-proof capture. Mutation locations are
checked for uniqueness. Together with the earlier tests this gives nine
accepted check/preservation controls and eleven diagnostic-specific rejections.

This bridge is deliberately narrower than arbitrary `Indexed.Derives`:
`SourceTyping` has exact type matching, no general conversion rule and no
`zeroLe` rule. Literals must be representable; subtraction is only the existing
closed, certified bridge form. The semantic interpretation still uses
mathematical naturals and makes no claim about runtime word overflow. The target
is the existing universe-free, ghost declarative `Raw.HasType`, not
`Core.infer`, and no arbitrary successful checker run is reflected into a source
derivation. The serializer/parser correspondence is tested, not proved. These
are forward typing and semantic results for witnessed source programs, not
whole-language consistency, executable-checker soundness or runtime/ownership
soundness.

### Executable inference for the restricted bridge language

`MixedInference.lean` implements `Checked.infer`, a structurally recursive,
proof-producing Lean checker over the existing annotated `CoreBridge.Term`
syntax. A successful result contains an inferred type and a `SourceTyping`
derivation. The caller does not provide that derivation. Variable lookup checks
the selected context entry's scope; natural expressions and annotations are
scope-checked; application requires a natural Pi; indexing checks exact proof
endpoints; lets check their annotation against the inferred value type. Lambda
inference shifts existing context types across the newly bound natural.

`infer_complete` proves that every `SourceTyping` derivation is accepted with
its exact type. `inferType_iff` combines this with soundness. `rejected_iff`
characterizes inference failure as the absence of any derivable type, and
`source_type_unique` proves type uniqueness in this judgment. `check_iff`
characterizes exact checking against a supplied annotation; annotation rejection
can also mean the term has a different type, rather than inference failure.
These results are about `SourceTyping`, not the full jihoo type checker.

`accepted_raw` and `accepted_closed` connect computed acceptance to the unified
Raw context and closed typing theorem from the previous section. `accepted_true`
connects acceptance to proposition truth given a well-formed mixed telescope,
proposition formation, and validity of the telescope's assumptions. The checker
does not itself certify arbitrary telescope well-formedness, and unused context
entries are not globally validated. `accepted_closed_bound` and
`accepted_closed_equality` need no supplied environment or derivation: a closed
accepted literal strict-bound/equality proposition is true. False literal
propositions therefore cannot be accepted by this checker.

`MixedInferenceExamples.lean` computes verdicts on sixteen cases without storing
source typing witnesses. It covers all admitted term constructors and exercises
mixed variable lookup, proof lets, scalar application, exact endpoint checking,
and intentional exclusions. `model_verdicts` is checked by Lean's kernel with
`decide`, not an assumed test result. Four additional Lean tests cover missing
variables, out-of-scope indices, a malformed accessed context entry and applying
a nonfunction. The emitter serializes model and expected actual-Core verdicts
separately into `tests/core_mixed_inference.tsv`. The full proof check regenerates
that file byte for byte. Actual Core tests require the stated verdict and
specific diagnostic, and run preservation checks on accepted cases. The two
intentional differences are `zeroLe` and a converted let annotation: jihoo accepts
both, while this model correctly rejects them. The harness checks that no other
scope difference is introduced. The combined mixed suite has twenty-two
accepted controls and fourteen rejected cases and also runs under `python -O`.

This is an executable decision procedure for the existing restricted bridge
judgment. It is not a decoder of arbitrary Core graphs or source files and does
not establish acceptance reflection for `Core.infer`. Numeric certificates in
`Index` and `Term` constructors are part of the admitted input syntax, including
representable literals and closed subtraction/comparison premises. No general
conversion or `zeroLe` rule has been added. Recursion is structurally terminating,
but no complexity bound or untrusted-input service is claimed: substitutions
can expand syntax, and this checker does not reproduce Core's fuel limits.
Semantic indices remain mathematical naturals; none of the new theorems claims
runtime, ownership, borrow, lowering or whole-language soundness.

### Admission from actual Core snapshots

`MixedRawAdmission.lean` removes the need to supply bridge syntax to the
restricted checker. It reconstructs candidate `Index`, `Ty` and `Term` values
from unified `Raw` trees, recovering the two variable namespaces from the
binder layout. Candidate reconstruction is not a trusted correctness assumption:
`admit` runs proved inference and requires exact structural equality between the
re-encoded term and the supplied term, and between its inferred type and the
supplied type. Erasure flags and binder annotations participate in that equality.
There is no conversion or normalization used to hide a representation mismatch.

A successful `Accepted` value contains source typing and both equalities.
`Accepted.raw_typed` establishes independent ghost `Raw.HasType` for the exact
input trees, and `Accepted.type_formed` establishes formation of the exact input
type. `Accepted.realizes` establishes realization of the inferred source
type's mathematical interpretation. `GraphAccepted.sound` composes this with
the existing graph decoder: the exact supplied graph and term/type roots
represent those typed trees. Every graph node, including unreachable nodes,
passes the graph validator. This endpoint checks the supplied snapshot itself;
it neither accepts a separate certificate nor establishes provenance from a
particular compiler invocation. A different valid snapshot can legitimately pass
its own check.

`CheckMixedRaw.lean` reads one bounded canonical snapshot using the existing
read-once `TypingInput` path. The existing graph limits (4,096 nodes, depth 128,
and bounded expanded-tree work including repeated references) apply before
candidate reconstruction. A separate saturating tree-cost pass limits each
term/type tree to 512 nodes, with candidate recursion fuel 32. Scalar function
applications admit only variable or literal arguments, so their substitution
does not expand index trees; non-atomic application is conservatively rejected.
These are defensive implementation limits, not a proved end-to-end complexity
or memory bound. The canonical byte parser, file IO and exporter remain trusted
and tested infrastructure, outside the typing theorem.

The decoder supports natural lambdas, atomic natural application, annotated
value/proof lets encoded as immediate lambda applications, literal arrays,
indexing with exact endpoints, equality reflexivity and true literal bounds.
It excludes standalone proof-domain lambdas, arbitrary function domains,
`zeroLe`, subtraction and general conversion. The immediate U64-lambda case
is treated as natural application; there is no claim that all bridge terms have
a successful round trip. Acceptance is sound for the admitted fragment, not a
completeness theorem for this decoder or for jihoo's full checker.

`tests/core_mixed_raw.py` builds the actual-Core snapshot exporter from this
checkout and checks 26 retained snapshots from both `infer` and `require`:
18 admitted snapshots and eight intentional unsupported cases. It also checks
wrong roots, invalid unreachable nodes, payload overflow, trailing/truncated
input, an independent valid snapshot, repeated-reference expansion, and separate
depth/tree budgets. Resource negatives have matching type shapes, so an unrelated
type mismatch does not explain rejection. The suite checks rejection exit status
and absence of success output, uses runtime guards under `python -O`, and executes
no input program. Lean examples independently check exact-type rejection,
erasure mismatch, namespace recovery and defensive limits. No theorem here
asserts that arbitrary successful `Core.infer` calls are sound, or adds a runtime,
ownership, borrow, lowering or whole-language result.

### Natural and proof-domain functions in one judgment

`MixedProofFunctions.lean` supplies a separate, restricted evidence calculus
where natural-index universal quantification and proof implication can nest in
either order. Earlier Indexed syntax had natural lambdas and proof-valued lets,
while the closed propositional-evidence profile had proof functions over closed
propositions. Here an implication's domain and codomain can refer to surrounding
natural indices, and a universally quantified body can itself contain proof
functions. This is a foundational logical judgment, not an extension of the
snapshot admission checker described above.

`Formula` consists of natural equality, strict bounds, universal quantification
over naturals, and implication. `Term` explicitly distinguishes natural lambda/
application from proof lambda/application. Natural and proof variables occupy
separate namespaces. The finite `Derives` judgment checks hypothesis lookup and
natural scope, with rules for reflexivity, true literal bounds and `zeroLe`.
There is no general conversion rule. Proofs never occur in index expressions or
in types, so proof implication is nondependent in its proof argument while its
propositions may depend on natural indices.

`Derives.scalar_substitution` preserves typing while shifting scalar replacements
under natural binders and substituting proof annotations. `Derives.renaming`
and `Derives.proof_substitution` preserve typing for finite proof contexts.
Proof substitution shifts inserted proofs' natural indices under natural lambdas
and renames their proof variables under proof lambdas. Replacement premises
require syntactically typed proofs at the source assumption types, not validity
of the result. `natural_beta` and `proof_beta` derive typing for the two explicit
beta substitutions. The latter additionally requires all remaining context
entries to be naturally scoped; this is stated rather than inferred from unused
hypotheses. These are typed beta rules, not a theorem about the entire Core
reduction relation or a claim of normalization.

`Formula.Holds` interprets implication as logical implication and natural
quantification as universal quantification over mathematical naturals.
`Formula.holds_subst` proves capture-safe scalar substitution preserves this
meaning. `Derives.sound` shows that a derivation's conclusion holds whenever
all its hypotheses hold in the same natural valuation. Validity of assumptions
is explicit and does not assume the conclusion. Closed false strict bounds and
unequal literal equalities therefore have no derivations, even with nested
proof functions and natural applications.

The Lean examples include a proof retained across a later natural binder,
higher-order proof-function application, a universally quantified proof used
under a natural binder, composed proof/scalar beta substitution, and proof
capture avoidance beneath another proof lambda. Missing hypotheses and forward
scalar references are excluded. `tests/core_proof_functions.py` independently
checks eight corresponding actual-Core programs with both `check` and
`preserves`, and seven negative controls with specific diagnostics. It also runs
under `python -O` and executes no input program.

The logical judgment itself does not reflect arbitrary successful Core checks or
broaden existing admission endpoints. The following section supplies a forward
Raw typing translation under explicit representability conditions. Arithmetic
expressions in this source judgment retain mathematical natural addition and
truncated subtraction; machine word bounds/overflow are not modeled here.
Arbitrary type domains, proof-dependent indices, universes, general conversion,
recursion, runtime, ownership, borrowing and lowering are outside the judgment.


### Translating mixed proof functions into Raw typing

`MixedProofTranslation.lean` proves the missing forward typing bridge for the
mixed natural/proof function judgment. `translate` maps a source derivation to
the existing, independently defined ghost `Raw.Beta.HasType` judgment. Its
premises are the source derivation, syntactic representability of the term, and
lookup correspondence for the two source namespaces in a single target context.
No premise assumes target typing. `translate_closed` discharges context
correspondence for a closed source derivation, using the empty target context.
The open theorem does not claim that arbitrary assumed contexts are globally
well formed; `formula_formed` separately proves formation for scoped,
representable proposition annotations.

Natural lambda/application encode as non-erased U64 Pi/Lam/application. Proof
lambda/application encode as erased proposition Pi/Lam/application. Encoding a
proof arrow shifts the codomain's natural-variable map even though the source
proof binder introduces no natural variable. `formula_subst` proves agreement
between capture-safe source scalar substitution and unified Raw substitution.
`formula_instantiate` justifies natural application;
`formula_drop_proof` proves that substituting an evidence argument into the
shifted codomain recovers its original encoding. Both context-extension lemmas
construct the lookup correspondence beneath their respective binder sorts.
`formula_proposition` proves the erasure classification rather than assuming it.

Admission requires every numeric literal carried in terms and proof annotations
to be below `2^64`, and excludes subtraction expressions. Literal bound evidence
also requires both endpoints to be representable; source typing already requires
the strict inequality. Addition and `zeroLe` are supported by the target ghost
judgment. This is not a runtime arithmetic safety assertion: variable values
remain mathematical naturals in the source semantics, and addition may overflow
if executed as a machine operation. The total encoding helper has a syntactic
checked-subtraction branch for substitution algebra, but the admission predicate
rejects every source subtraction; no typing or semantic guarantee is offered
for that branch or any other unadmitted term. The admitted theorem does not
manufacture a subtraction certificate.

`MixedProofTranslationExamples.lean` stores each generated declaration together
with its source typing and admission proofs. Six cases cover all term rules:
retaining evidence across a natural binder, higher-order proof application,
a universally quantified proof argument, nested natural/proof application,
`zeroLe`, and true literal inequality. Every example has both a source truth
theorem and a closed Raw typing theorem. Subtraction and oversized literals have
explicit exclusion proofs. `EmitMixedProofTranslation.lean` emits the fixture
that `proofs/check.sh` regenerates and compares byte for byte; Nix packages the
emitter and fixture explicitly.

Actual Core checks every generated declaration and its preservation behavior.
Six unique-location mutations test scalar capture, returning a function instead
of evidence, universal-index capture, the wrong proof argument, false bounds,
and a non-erased proof binder. Together with the existing controls, the suite
contains fourteen accepted and thirteen diagnostic-specific rejected cases and
runs under `python -O`. These tests exercise the serializer/parser and executable
checker boundary, whose general correctness is not established by the theorem.
No input program is executed.

This closes the forward Raw typing gap for the admitted mixed proof-function
fragment. It does not extend the existing snapshot admission checker, prove a
converse from arbitrary Raw derivations, establish soundness of all Raw beta
conversion, or reflect arbitrary `Core.infer` acceptance. The source semantic
soundness theorem is proved independently; the bridge does not assume semantic
soundness of the whole Raw judgment. Whole-language, runtime, ownership,
borrowing, erasure and lowering results remain outside its claim.

### Independent semantic admission of mixed proof snapshots

`MixedProofInference.lean` implements executable, proof-producing inference for
the mixed natural/proof function judgment. It handles both lambda/application
pairs, exact proposition matching, finite hypothesis lookup, natural scope,
reflexivity, literal decisions and `zeroLe`. `inferType_iff` proves soundness and
completeness for this restricted judgment, including higher-order proof
arguments. `rejected_iff` characterizes absence of any source derivation. These
are statements about the independent Lean checker, not about `Core.infer`.

`MixedProofAdmission.lean` connects this inference to supplied actual-Core
snapshots. It reconstructs both the term and its expected proposition from
unified Raw syntax, using the binder layout to distinguish natural indices and
proof variables. It checks the inferred proposition against that parsed input
proposition, verifies representability, and requires exact re-encoding of both
input trees. A successful `Accepted` result contains all this evidence; the
caller supplies neither a source derivation nor a semantic truth premise.
Standalone proof lambdas, proof applications, interleaved natural binders and
`zeroLe` are supported here, unlike the older restricted mixed admission path.
The older endpoint remains unchanged.

`Accepted.raw_typed` and `Accepted.type_formed` establish the independent ghost
Raw judgments for the exact inputs. `Accepted.parsed_truth` establishes truth
of whichever proposition is returned by the input type parser, using uniqueness
of its deterministic result and the independently proved source semantics.
`GraphAccepted.input_truth` connects that result to the selected type root of
the supplied graph. Thus the theorem is about the actual retained type tree,
not a producer's claimed type or merely a convertible alternative. The whole
graph and both roots are parameters of the admitted evidence. Every node,
including unreachable nodes, is checked by the existing graph decoder.
`false_bound_excluded` and `false_equality_excluded` rule out admission of any
term paired with a representable closed false literal proposition.

`CheckMixedProof.lean` is a standalone verifier over the canonical, bounded,
read-once snapshot input path. It reuses the prior graph/expanded-tree limits,
512-node term/type guards and candidate recursion fuel 32. Natural application
arguments are restricted to atomic variables/literals, preventing index-tree
expansion during substitution; proof application does not substitute proofs
into index expressions. No end-to-end complexity bound is proved. Subtraction,
general conversion, erased natural binders, proof-dependent indices and arbitrary
non-proposition function domains remain excluded. Non-atomic natural application
is deliberately incomplete even when both source and actual Core accept it.

`tests/core_mixed_proof_admission.py` builds the current checkout's actual-Core
snapshot exporter and checks fifteen source programs in both `infer` and
`require` modes, including all six proof-backed generated translations. Thirty
snapshots plus an independently valid input pass. Fifteen cases are rejected:
three actually Core-accepted scope exclusions, and twelve root/type/erasure,
malformed-input and resource variants. False literal formulas are also tested
as graph-valid payloads. Graph-changing tests use earlier valid references where
appropriate; depth/shared-expansion tests carry matching type shapes. Rejection
must have nonzero status, a rejection diagnostic and no success output. The
suite also runs under `python -O`, and executes no input program. Lean examples
check proof-lambda admission, namespace separation, forward-reference rejection,
wrong erasure, inference computation and false-formula exclusion.

This is a semantic guarantee for snapshots that pass the independent admission
checker. Actual `Core.infer` or `Core.require` success alone is not a theorem
premise sufficient for truth; the production compiler does not automatically
invoke this verifier. The association between exported snapshots and actual
compiler calls, canonical parser/IO behavior and serialization fidelity remain
trusted and tested boundaries. The theorem neither assumes nor proves semantic
soundness of arbitrary Raw beta conversion. It makes no whole-language,
normalization, runtime arithmetic, ownership, borrow, erasure or lowering claim.

### Ownership accounting through ghost-slot erasure

`QuantityErasure.lean` advances the quantity/erasure release obligation in the
existing control semantics. `erase` deletes ghost computations and removes an
erased scope's slot by capture-avoiding partial relabeling. It retains linear,
unrestricted and borrowed scopes. It transforms branches, arbitrary finite
repetitions, immediately invoked bodies and latent closures recursively; it does
not select a convenient branch or assume termination.

`demand_preserved` proves that every successful original resource query has the
same result after erasure. `finishes_forward` and `prefix_forward` preserve the
exact outer event trace, including prefixes ending in a trap and finite prefixes
of divergence. More strongly, `finished_count` and `prefix_count` apply to **all**
executions of the transformed control, without requiring a source execution as a
premise. The simultaneous linear-resource endpoints therefore retain exact-once
use on completion and at-most-once use on every finite prefix. A trap can still
abandon an owner; the theorem deliberately does not require exact-once prefixes.

`erase_relabel` proves commutation with capture-avoiding partial replacement of
outer resource names. `substitution_erasure` composes this with the existing
annotated-source substitution theorem, including variable-to-borrow replacement.
It does not extend substitution to effectful computations or establish stability
of native inferred binder modes.

Checking must precede erasure. `target_check_not_source_check` exhibits an erased
scope that uses its ghost slot: the source query rejects it, while the transformed
query succeeds after that event is removed. Consequently this pass is neither a
replacement for source checking nor a backwards admission theorem. This initial result proves forward execution simulation. The following
reflection development establishes the finite-trace converse, but not a
backwards admission theorem or whole-program operational equivalence.

Kernel-checked examples cover two erased slots around a fresh linear owner,
retained borrowed/unrestricted slots, repeated fresh owners, traps, duplication
and forbidden capture. Seven additional actual-Core quantity regressions cover
nested erased proof applications, local ownership, branches and traps, with
specific rejection diagnostics for duplication and local discard. They extend
`tests/core_quantities.py`, which observes `Core.runtime_uses` and complete
`Core.check`; it does not execute any input program. Their association with the
control examples is manually selected regression evidence, not a proved parser
or source projection.

This remains a theorem about ownership-use traces, not values or heap events.
The native Core-to-control projection, mode authenticity/stability, native ghost
argument erasure and MIR lowering are **not** mechanized by this increment.
Borrowed slots retain their identity but no lifetime, lease or heap-alias safety
follows. The whole-specified-core consistency/preservation and native erasure
release gates remain open. No certificate interface or compiler acceptance rule
is added or weakened.

### Erasure reflects finite observations and preserves slot identity

`QuantityErasureReflection.lean` closes the converse finite-trace obligation left
by the first control-erasure milestone. `finishes_relabel_reflect` and
`prefix_relabel_reflect` recover an original completed execution or finite prefix
from any execution after partial relabeling; the original trace filters to the
observed trace. Reconstruction is existential. Deleting resource events can map
distinct histories to the same observation, as an explicit checked counterexample
shows. No injectivity of erased histories is assumed.

`finishes_reflect` and `prefix_reflect` lift those results through ghost scope
removal, branches, repetitions, immediately invoked bodies and latent closures.
Combined with the forward theorems, `finishes_iff` and `prefix_iff` establish exact
equality of the sets of completed and finite-prefix **outer ownership-use traces**
before and after erasure. No source typing or quantity-check premise is needed
for this semantic statement. `may_terminate_iff` additionally preserves and
reflects existence of a completed execution. These results do not equate infinite
runs, fairness, divergence productivity, values, heaps, or machine executions.
Unchecked controls are allowed by these operational judgments; the previous
source-check-before-erasure requirement still applies to ownership safety.

`QuantityRuntimeSlots.lean` supplies a separate value-parametric environment
lemma matching the lowering representation of ghost slots as `None`.
`Slots.lookup` proves that a surviving compacted position resolves to the exact
original value. `position_injective` proves that two distinct source slots cannot
be conflated even if their payloads happen to be equal. `missing` proves that
neither erased nor out-of-range slots become readable. The formal lists are
newest-binder first; native `core_lower.jh` uses the opposite list orientation and
looks up `env[env.len - 1 - k]`. The capture-layout development below proves the guarded Nat/list reversal
rule. Correspondence of native arrays and actual lowering environments to
these lists remains an implementation obligation. This is not a proof about native pointer or heap identity.

The implementation regression `tests/core_erasure_traces.py` compares complete
MIR from seven runtime-only/ghost-annotated Core pairs: identity, a branch, nested
local ownership, trapping arithmetic before or after free, a loop, and a discarded
erased scalar overflow expression. Both x86_64 and aarch64 are covered with O0/O2
flags (28 MIR comparisons), and each twin is emitted as an object with its ELF
architecture checked (56 objects). Four negative controls require the intended
diagnostic and no partial MIR: foreign erased-proof parameters, erased runtime
use, owner duplication and owner discard. A changed runtime expression must
produce different MIR, guarding against vacuous equality. The subprocess guards
also run under Python optimization. No generated input program is executed.

These tests exercise actual checking, runtime normalization and lowering together;
they do not authenticate a projection into the formal control model or identify
which pass performs each simplification. Native lowering retains `None` slots in
its environment while excluding erased arguments from runtime operand lists;
the abstract control transformation compacts resource names. Consequently the
finite-trace theorem is not yet a native Core-to-MIR erasure theorem. Mode
justification, native source projection, value semantics, borrow lifetimes and
the remaining whole-specified-core release obligations remain open. No new
certificate or production acceptance rule is introduced.

### Generated-recursion capture environments

`LoweringEnvironment.lean` models the capture-layout portion of
`core_lower.jh`'s generated recursion functions. Native lowering retains an
oldest-binder-first environment with ghost holes. A normal value contributes one
call operand, but an enclosing recursion's hypothesis contributes its node and
all of its extra captured operands. The callee rebuilds the hypothesis using
fresh parameter references. Treating that hypothesis as one scalar slot, or
compacting all holes without retaining source binder positions, would lose this
structure.

The formal `Slot` therefore distinguishes `ghost`, `value`, and a nonempty
`hypothesis node extra` block. `layout` records the block boundaries and widths;
`pack` emits the operands in native environment order. `rebuild_pack` proves
exact reconstruction while retaining an arbitrary suffix, so explicitly applied
arguments are not consumed as captures. `rebuild_sound` proves that every
successful reconstruction consumes exactly its reported payload and preserves
the supplied layout. `decode_iff` characterizes complete-frame decoding, rejecting
truncated and trailing operands. `operand_count` and `decode_count` establish the
frame arity, including each hypothesis node. `call_frame` separates the new
recursion's own leading node from its captured environment and applied suffix.
This decoder is a mathematical specification component, not a newly deployed
native guard or certificate interface.

`callee_environment` supplies the value-level conditional bridge: if fresh
parameter references decode with the original layout, and positional parameter
assignment evaluates their operand list to the caller's packed operands, then
interpreting the reconstructed callee slots recovers the **entire** caller
environment. `callee_lookup` consequently preserves every original binder
lookup. The premises concern the layout and operand assignment, not a caller
supplied assertion that both environments are already equal. Actual MIR call
semantics and fresh-local allocation must still establish these premises.

`native_lookup_reverse` proves the guarded `length - 1 - k` list lookup agrees
with newest-first de Bruijn lookup. Appending a new native slot yields the new
binder at zero and shifts every outer binder by one. The guard matters: a
checked example shows that saturating subtraction without a range check could
read the oldest slot for an out-of-range index. These are unbounded Nat/list
results; native array bounds, signed conversions and integer limits remain
implementation obligations.

The layout is essential. Equal packed operand lists can describe different
environments (two values versus one hypothesis block), and a same-arity operand
permutation can decode successfully to the wrong values. Kernel-checked
counterexamples prevent interpreting roundtrip as authenticity. Other examples
cover multiple hypothesis blocks, ghost holes, duplicate scalar payloads,
zero-extra hypotheses, missing nodes, truncated blocks, trailing operands and
retention of applied arguments.

`tests/core_capture_environment.py` exercises the actual elaborator, Core
checker and lowerer with two- and three-level recursive programs. The deepest
case captures two enclosing function-valued hypotheses together with distinct
scalar values and ghost arguments. Plain and ghost-annotated variants must
produce identical complete MIR with at least five generated recursive functions.
Both variants emit x86_64 and aarch64 objects at O0 and O2 (eight objects). On the
host, bounded subprocesses compare 720 function results against independent
Python recurrences and check allocation/free balance per call. Distinct and
equal scalar payloads exercise ordering and equal-typed slots; separate controls
ensure the reference models detect a scalar permutation. Normal and optimized
Python modes, including native worker subprocesses, run in CI.

This is a correctness theorem for the stated capture-layout algorithm plus
native regression evidence. It does not prove that native `Hypothesis.types`,
`node`, `extra`, function IDs, erased masks or return types always satisfy the
layout invariant, or that native recursion terminates. Heap identity, borrow
validity, ownership preservation across MIR calls, value semantics of the full
runtime fragment and whole-specified-core consistency/preservation remain open.
No production compiler acceptance rule or lowering behavior changes here.

### Integrated ownership, erasure and call-frame argument

`OwnershipLowering.lean` connects the existing quantity checker, ghost erasure,
finite-trace correspondence and capture reconstruction into one conditional
endpoint, `checked_owner_pipeline`. The connecting map is computed from the
capture layout, not supplied as an arbitrary correspondence. `scalarPosition`
counts the full node-plus-extra width of every hypothesis block; `resourceMap`
converts guarded newest-first source indices into oldest-first packed operand
positions. Ghost and hypothesis slots do not designate scalar resources.

`scalar_injective` and `resource_injective` prove that two surviving resource
slots cannot map to the same operand position. `resource_payload` additionally
proves that every designated scalar slot survives and retains its original
value. Equal payload values do not identify their resource positions. These
facts discharge the unique-preimage premise of the existing quantity relabeling
theorem; simply reusing source indices would not work after hypothesis expansion.

`lowerControl` composes ghost erasure and that computed resource relabeling.
`demand_preserved` transports the complete successful demand result.
`finishes_iff` and `prefix_iff` recover the original completed/prefix trace from
any transformed trace and characterize the latter as the filtered original.
They compose the existing erasure reflection and relabeling results rather than
introducing another independent operational semantics.

Given a designated scalar slot, original demand one, a callee frame decoded with
the caller layout, and positional parameter assignment, `checked_owner_pipeline`
derives one runtime operand position with all of these guarantees together:

- the operand evaluates to the original value;
- the interpreted callee environment resolves the original binder to that value;
- every completed transformed-control trace uses the operand exactly once;
- every finite transformed-control prefix uses it at most once.

The completion/prefix conclusions quantify over all transformed-control runs;
there is no selected runtime execution premise. Examples instantiate the whole
endpoint with two erased positions/contexts, a three-operand hypothesis and two
scalar resources, and provide an actual completed trace. A separate counterexample
shows why source checking alone is insufficient if the purported owner slot is
really ghost. Traps retain prefix observations but do not gain completion.

The native capture regression now also threads an owned buffer as an explicit
argument through recursive hypotheses while computing updates in a nested
borrowed recursion. Its final buffer value is checked against an independent
model; each native call must balance allocations and frees. Together with the
existing two-/three-level scalar captures this gives 720 native comparisons per
Python mode, eight O0/O2 target objects and exact plain/ghost MIR equality. A
mutation that both frees and passes the same owner must receive the intended
`an owned value is used more than once` diagnostic and produce no object. The
invalid program is never executed. These are implementation regressions, not
proofs that native executions instantiate the formal trace relation.

The original 0.6 obligations can now be separated without conflating the models:

| Obligation | Mechanized result available | Remaining release premise |
| --- | --- | --- |
| Selected Raw logical consistency and preservation | Closed literal consistency, contextual beta/bounded-add preservation | All specified constructors, reductions and runtime modes are not represented by this Raw fragment |
| Source ownership accounting | Quantity checking bounds all completed/prefix traces | Authentic typed-Core projection, alias resolution and mode stability |
| Ghost erasure and operand naming | Finite trace correspondence and the computed injective resource map | Native Core/MIR traces must implement these controls |
| Call-frame values | Capture reconstruction, sequential numbering and constructed positional entry | Native descriptor fidelity, machine bounds and execution of the stated entry rule |
| Heap and borrow safety | No full theorem | Heap identity, lease/lifetime semantics and their simulation remain open |

The resource slot premise classifies a scalar slot, not its native linear type or
heap object. Interpreting it as an owned value requires the typed projection and
alias invariants in the table. In particular, equal scalar payloads do not prove
distinct heap ownership, nor does parameter-value equality prove safe borrowing.
The two formal branches (Raw logical typing and ownership control) are not yet
proved to describe every same accepted native Core program. Thus this composed
result is a coherent partial release argument, not a whole-language soundness
or Core-to-MIR theorem. No production rule, new certificate endpoint, or native
runtime behavior changes in this increment.

### Constructed parameter allocation and call entry

`CallEntry.lean` removes two caller-supplied premises from the integrated model:
the callee decoding witness and positional value-assignment equality.
`numberSlot`/`number` implement sequential fresh parameter allocation from a
starting local index: ghosts allocate nothing, scalar slots allocate one local,
and a hypothesis allocates its node followed by each extra operand. `number_layout`
and `number_pack` prove preservation of layout and an exact contiguous reference
range. `number_append` proves that separate capture/applied-argument allocation
phases agree with allocation over the combined layout. `number_decode` therefore
constructs the successful frame decoding rather than assuming it.

`entry` specifies a callee-local store containing an existing reserved prefix
(such as the return slot), its own recursion node, then the positional caller
operands. `references_distinct` and `references_fresh` prove generated parameters
are distinct and overlap neither reserved locals nor the node.
`reference_initialized` proves every generated reference has a value, and
`reserved_unchanged` proves the existing prefix is preserved. `entry_assignment`
derives the operand-value equality from this store construction. Its total
lookup uses a fallback only for definitional convenience: the equality holds
for every fallback and every generated reference is separately proved in range.
The model does not treat a missing actual argument as silently initialized.

`constructed_owner_pipeline` instantiates the preceding integrated theorem with
this generated callee and store. No decoded-frame or value-assignment witness is
an input. Source resource-slot designation and demand one remain its safety
premises; the conclusions retain the original value and exact-once/at-most-once
accounting for all transformed control executions. Examples instantiate that
result directly, cover hypothesis expansion and two-phase allocation, and show
that an incorrect base index could otherwise read a reserved value.

The connection to native construction is now checked before LLVM as well as by
execution. `tests/core_call_entry_probe.jh` builds the current loader, elaborator,
Core and lowerer modules, then inspects their actual `mir.Program`. For generated
recursion functions it verifies return-local placement, a nonempty node-bearing
parameter prefix, agreement of signature/pass/argument counts, contiguous `Arg`
locals at indices `1..arg_count`, each local's signature type, absence of later
`Arg` locals, and direct recursive call arities. It does not infer operand-value
agreement from arity. For the current regression corpus, four inspections
(plain/ghost variants and two targets) each observe eight generated recursive
functions, nineteen recursive calls and 139 parameter locals. Invalid erased
runtime use and a valid nonrecursive input must both reject without partial
success output, ruling out vacuous observation.

The native corpus additionally uses two explicitly applied scalar parameters
with a ghost argument between them. A noncommutative result and an independent
reference recurrence detect argument swaps or accidental ghost-slot offsets.
Together with nested hypotheses and owned-buffer threading this yields 720
native value/allocation comparisons per Python mode and eight O0/O2 target
objects. The new MIR inspection is wired into CI; its helper is rebuilt from
current compiler modules. Native worker processes remain bounded and the
invalid ownership mutation is never executed.

**Precise boundary:** this proves a concrete list/Nat entry algorithm and its
composition with the existing control semantics. It does not prove the native
imperative implementation refines that algorithm, or that every MIR/LLVM call
implements the stipulated positional entry store. The probe and executions are
regression evidence for those obligations, not proof certificates. Native u32
local-index bounds, descriptor authenticity, typed source/control projection,
heap/borrow interpretation and whole-specified-core coverage remain open. The
reserved prefix belongs to the callee-local model, not shared caller heap state;
no stack separation or lifetime theorem follows.

### Production call-frame validation

`core_lower.compile` now runs `core_mir.validate` before publishing its MIR.
The validator checks all generated and exported bodies, not only the recursion
fixtures: signature/pass arity, nonvariadic signatures, nonnegative argument
counts, a correctly typed return local at zero, a contiguous and correctly
typed parameter prefix, and absence of later argument/return locals. Every call
must be direct with an in-range function ID and exact argument count; its
unprojected destination must exist and have the callee result type, and its
continuation block must exist. Foreign declarations also have their signature
shape checked. These are internal lowering diagnostics; they do not extend the
accepted Core language or replace Core checking before normalization/erasure.

The fresh-module probe mutates actual generated MIR one invariant at a time and
requires the corresponding production diagnostic, with no successful output.
Unmodified plain/ghost, both-target programs remain positive controls. CI runs
this same probe, so a malformed frame cannot silently pass its structural gate.

This is a trusted, tested compiler guard, not a new Lean refinement theorem.
It enforces structural prerequisites of `CallEntry`; it does not establish
positional operand-value correspondence, source-slot
provenance, initialization along control-flow paths, heap ownership, or LLVM
semantics. In particular, swapping two same-typed operands still requires the
independent execution regressions and the remaining implementation refinement
obligation. The validator is specific to dependent Core's direct, nonvariadic
MIR subset, not the legacy compiler's general MIR or closure ABI.


### Typed Core MIR body validation

The same production gate now checks every body in the emitted Core subset,
including unreachable blocks, before returning the program to downstream code.
A linear pass over the interned type table marks well-formed runtime types;
composite types must refer to already validated children. This handles repeated
references without expansion; any referenced forward/cyclic type is rejected.
Canonical bool,
unit, signed-i64 and unsigned-u64 entries are checked explicitly. Signatures and
all local declarations must use valid runtime types.

Place checking follows tuple fields, array indices and pointer dereferences,
checking local/field bounds and requiring a U64 index local. Operand checking
validates integer constant kinds/ranges and local references. Assignment results,
integer operations, numeric casts, pointer offsets, arrays and tuple aggregates
must have consistent types and arities. Every direct call's operand types must
match its signature. Unsupported MIR forms fail closed: this is an intentionally
explicit account of what `core_lower` emits, not the legacy language's full MIR.

Control-flow checks cover entry-block existence, goto/switch/assert targets,
switch scrutinee/case kinds and ranges, duplicate switch cases, boolean assertions,
and unfinished terminators. They complement the existing call-frame checks.
Fresh-current-module mutation tests preserve the original graph except for the
selected fault and require a specific diagnostic; unmodified generated programs
remain positive controls. Native regressions exercise both targets, optimization
levels, arrays, recursive nodes and owned buffers.

**Boundary:** these checks establish tested static shape/type invariants, not a
Lean theorem about this implementation. They do not prove definite initialization,
array index bounds, valid/live heap pointers, move discipline, source-to-MIR value
preservation, or backend semantics. A same-typed argument permutation still passes
static checking. Neither successful validation nor the existing restricted models
close the original whole-specified-core preservation/consistency and borrow gates.


### Definite local initialization at the Core MIR boundary

After structural and type validation, `core_init.validate` performs a bounded
forward must-analysis from block zero. The entry facts contain parameter locals
and the unit return local (which has no bytes). A block's first incoming edge
establishes its input facts; later edges intersect them and requeue the block
when a fact is lost. Backedges participate in the same fixed point. A later
loop-body assignment cannot justify an earlier first-iteration read.

Each reachable assignment reads its operands before marking an unprojected
destination initialized. Projected stores instead require initialized base and
index locals, without marking the whole aggregate or pointed-to memory initialized.
Reads of aggregate operands, pointer bases, array-index locals, switch/assert
conditions and call arguments are checked. Calls read arguments before setting
the result initialized on their normal-return edge. Non-unit returns require
initialized local zero. Structurally disconnected blocks are excluded from this
analysis but still undergo the preceding type/shape checks; this accommodates
the lowerer's disconnected code after `Absurd`/`Unreachable`.

The implementation caps potential block/local facts at 4,000,000 per function
before allocating analysis state, and charges state copies/intersections,
statement/operand/projection visits and edge propagation against 64,000,000 work
units. Exhaustion is an explicit diagnostic, never successful partial validation.
The finite bitsets only lose facts after first reach; queued flags bound the
worklist to at most one entry per block. No constant-condition pruning is assumed.

The fresh-module tests retain a real generated function's signature/frame while
replacing its body with well-typed diagnostic CFGs. Controls pair initialized and
uninitialized straight-line reads, index reads, joins, loops and calls, and accept
disconnected uninitialized reads. The missing-write join deliberately visits the
apparently valid predecessor first, requiring a later predecessor to invalidate
and revisit the join. A call regression uses its own result local as an argument,
ensuring the result write cannot justify that argument read. Other failures cover
self-assignment, return values, pointer bases, aggregates and analysis-state limits.
A separate many-edge/small-state fixture exhausts the work budget, paired with
an accepted smaller-edge control so the two resource guards are isolated.
These fixtures validate MIR only; potentially invalid machine code is not executed.

**Boundary:** this is a trusted, tested local-storage analysis, not a formal Lean
proof or a heap/borrow theorem. Normal call returns are modeled as writing their
result; external ABI behavior and backend implementation remain trusted. Copy and
Move both read stored bytes here: move discipline and ownership are separate.
Initialized pointers need not be live, allocated or point to initialized memory.
Whole-aggregate initialization is conservative, and runtime array bounds remain
outside this pass. This narrows a concrete lowering gap without establishing
whole-specified-core consistency, preservation or value correspondence.


### Checked initialization invariants and all-path read safety

`Initialization.lean` proves soundness of an executable invariant checker for
finite local-read/write CFGs. Its `Reach` relation follows arbitrary CFG edges,
including backedges, and applies writes without assuming reads are safe. The
main theorem `accepted_reads_safe` derives read safety for every reachable block
from `check = true`; it does not take successful execution or read safety as a
premise. Within each action, reads precede writes, so assigning a call result
cannot justify reading that result as an argument to the same call.

The certificate supplies optional incoming facts per block. The checker requires
entry facts to be contained in the initial set, checks each claimed-reachable
block's reads and transfers, and requires each successor to exist, have facts,
and receive only facts established by the predecessor. A `none` fact entry may
hide a disconnected block, but cannot hide a reachable successor. `run_sound`
relates abstract facts to every concrete initialized-local set covering them;
`reachable_covered` propagates this invariant through all finite paths. The proof
is independent of the producer's iteration order, termination strategy or budget.
Examples check cycles, late/missing predecessor facts, read-before-write,
invented entry facts and unreachable code. All new results are in the axiom audit.

The production solver now consumes an explicit read/write projection built by
`core_init`, rather than interpreting MIR reads separately from the observer.
The same returned graph, initial set and computed facts are exported by the
fresh-module test probe. The probe re-runs shared analysis on the retained,
already validated MIR; it does not intercept the earlier validation invocation.
This removes a duplicate test-only event interpretation.
Projection traversal has an additional 1,000,000-work-unit cap before retaining
the graph; this cost is also charged to the existing total analysis budget.

`tests/core_initialization_proof.py` reads four actual exports (plain/ghost and
both targets), requires identical projections/facts, and generates Lean theorems
for each native function by applying `accepted_reads_safe`. The concrete checker
premises are discharged by kernel reduction (`decide`), not an unchecked native
oracle. The current corpus yields 13 functions and 112 blocks. Four additional
kernel-checked rejections cover missing entry facts, invented initial facts,
hidden successors and a fresh read/write in the same action. The bounded export
parser generates only numeric/list syntax; generated theorem dependencies are
audited. Both Python modes run in the graph-certificates CI check.

**Exact trust boundary:** these are genuine all-path theorems about the exported
local-event graphs, plus implementation-linked regression evidence. They are not
a proof that every native compiler acceptance produces an accepted Lean invariant,
or that native MIR-to-event projection preserves all reads/writes. Production
compilation does not invoke Lean. The shared projection, exporter/parser, native
compiler, external call ABI and backend remain trusted for the implementation
connection. The exports are test observations, not authenticated certificates for
arbitrary retained MIR snapshots. Heap initialization, live pointers, bounds,
move/borrow discipline, runtime value preservation and whole-core consistency
remain separate obligations. No full 0.6 soundness claim follows from this bridge.


### Concrete local stores and by-value entry

`InitializationStore.lean` connects the initialized-fact checker to a value-level
partial local store (`Nat → Option α`). `readMany` looks up actual values in read
order; `writeMany` writes the supplied result values in destination order and
rejects a result-vector arity mismatch. `execute` distinguishes normal completion,
uninitialized-local lookup, operation traps and malformed results. Reads happen
before writes, including when a call argument and result use the same local.

Operation choices are indexed by instruction position and may differ on every
block execution. Thus the result does not assume that heap-dependent operations
are pure, or that two equal read/write footprints compute the same value. Normal
block steps define `ValueReach`; a reachable next block is allowed to fail.
`accepted_no_uninitialized` proves its failure cannot be an uninitialized-local
lookup when the graph checker accepts. This is not the tautology that a completed
execution has already succeeded. `execution_sound` additionally preserves coverage
of the outgoing facts on normal results. Traps and malformed-result outcomes remain
possible, and explicit examples preserve that distinction.

`enter` constructs a by-value callee store with its optional return value at zero,
parameters at `1..n`, and absent locals elsewhere. `enter_covers` derives entry
coverage from that construction; `accepted_frame_no_uninitialized` combines it
with the concrete execution theorem without an assumed entry-coverage witness.
`call_entry_lookup` relates this store to the earlier `CallEntry` packed node and
capture layout. The store model describes distinct local cells, not disjoint heap
objects: copied pointer values may alias the same allocation.

The production MIR gate now explicitly rejects `Borrow`/`Owned` parameter-passing
flags and reference-result metadata. `core_lower` emits only `ParamPass.Value` and
`returns_ref = false`. This matters because the LLVM backend gives borrow modes
special attributes and may use an owned aggregate's incoming storage directly,
whereas the local-store model uses by-value local cells. The new regressions change
only those descriptors while retaining valid types, counts and layouts. Source
owned buffers and lists remain supported: this path implements their ownership
through Core checking and explicit operations, not legacy MIR `Owned` flags.

The real-Core bridge now also kernel-checks a concrete no-local-read-fault theorem
for each exported graph, universally quantified over entry values and operation
choices. The observer also records the retained MIR frame's argument count and
unit-return flag; the parser requires the initial facts to agree exactly with
those descriptors. Each generated theorem uses `enter` with an argument list of
that length, deriving coverage rather than assuming initialized storage.
Both the earlier graph theorem and the new concrete theorem are dependency-audited
for each of the 13 functions/112 blocks, in both Python modes. Operational examples
cover absent reads, read ordering, repeated writes, position-sensitive operations,
packed captures and loops, and demonstrate that traps and bad result arities are
not ruled out by initialization checking.

**Boundary:** this proves exclusion of the specific `None` local-lookup fault in
the stated partial-store semantics. Opaque values may still represent invalid
pointers or other semantically invalid values; no LLVM poison/undef, heap, bounds,
borrow, arithmetic or general value-validity theorem follows. The native ABI-mode
guard is tested implementation evidence, not a proof of LLVM frame copying. Native
MIR/event projection, native checker refinement and whole-core consistency remain
unproved. The theorem does not assert that execution terminates or avoids traps.

### Interprocedural initialization and suspended callers

`InitializationCalls.lean` extends the concrete partial-store result with an
explicit call stack. A call reads its whole-local and opaque-constant arguments
in order, saves the caller's memory and continuation, and constructs the callee's
fresh `enter` frame. Returning reads callee local zero, restores the saved caller,
and writes only its destination. Callee locals cannot accidentally replace the
caller's same-numbered locals. Pointer values may still alias heap storage; this
is a local-frame property, not separation of allocations.

Each instruction projects to the existing read/write graph. `validate` checks
all function certificates plus internal call target existence and argument
counts. `validated_call_ready` derives a call transition from accepted metadata
and covered current storage: argument lookup and arity are not assumed safe.
`call_continuation` derives coverage of the suspended continuation for **every**
possible return value. `preservation` maintains both the active frame and all
suspended callers. `no_uninitialized` excludes the uninitialized-local fault
through every finite interprocedural trace from a constructed entry frame,
including recursive calls and repeated invocations. It assumes neither a bound
on stack depth nor that the callee returns. It does not prove termination or
global progress. Traps and malformed operation results remain terminal outcomes.

`tests/core_call_machine.py` observes the same real Core capture programs on both
targets, with and without ghost binders. The observer now reports each internal
call's native function ID, ordered whole-local/constant arguments, destination,
and continuation; returns are distinguished too. The harness splits native
blocks into instruction nodes, retaining the solver's incoming facts and deriving
intermediate facts by writes. It requires call/return metadata to match the native
read/write action and successor, and requires callee arity to agree. It then
kernel-checks the complete function table and instantiates the recursive-stack
safety theorem: 13 functions, 24 internal calls and 442 instruction nodes in the
current fixture, including placeholders for external function IDs. Four handoff
metadata mutations reject; Lean examples independently reject missing callees,
wrong arities, uninitialized caller locals and absent return values. Concrete
call/return examples distinguish saved caller values from callee-local values.
Both Python modes run in `graph-certificates` CI with explicit failures, bounds
on observed/expanded work and an axiom audit. Expansion additionally charges a
global 500,000-cell budget before each incoming-fact copy or write concatenation.
The budget counts repeated snapshots, including empty-write copies, across all
functions; an instruction-count bound alone would permit quadratic retained facts.
Serialization independently preflights the same cumulative cell limit before
constructing Lean strings.
Regression controls test the exact boundary, cross-function accumulation, repeated
references and rejection before allocation.

**Boundary:** this is an interprocedural safety theorem for the stated machine,
not a native MIR simulation proof. The observer rejects projected call arguments;
whole-local arguments and constants are the admitted observation interface.
Constants are intentionally opaque (each observed occurrence receives its own
token, interpreted by an arbitrary value map), so no claim of numeric value
correspondence follows. External calls and ordinary
instructions remain arbitrary operations with declared local reads/writes; heap
and foreign-call effects are not formalized. Native projection, block splitting,
constant abstraction and the association with the observed compiler run remain
trusted. No type preservation, ownership/borrow theorem, LLVM poison/undef theorem,
or whole-language 0.6 soundness claim follows. The native regression suite also
executes the capture programs and checks results and balanced allocations; those
are separate implementation tests, not premises discharged by the Lean model.
