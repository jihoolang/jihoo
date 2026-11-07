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
axiom dependencies of eighty-three selected public guarantees in `Audit.lean`. Only Lean's
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

## Remaining obligations

There is no map from accepted core programs to either `Derives` or `HasType` with
a proved correctness theorem. Full soundness requires the remaining term syntax, universes, ghost/code
positions, dependent functions, families and elimination, followed by preservation
and full consistency. Quantity rules need an execution model of ownership and
scoped borrows. Erasure and runtime normalization must be related to the pure model,
with traps specified, before lowering can be connected to a semantics of MIR.

Finite rejection, preservation and differential tests remain implementation
regressions. They are not replaced by these proofs, and they do not discharge the
missing correspondence. The [roadmap](roadmap.md#the-050-release-gate-for-the-native-core)
continues to distinguish these obligations and their trusted implementation boundary.
