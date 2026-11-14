# Full native syntax and the remaining kernel proof

The native work uses one shared `Jihoo.NativeKernel` syntax for every one of
`compiler/core.jh`'s **54** `Term` constructors. This extends beyond the older
universe-free `CoreBridge.Raw` checker. Complete syntax coverage is distinct
from complete typing-rule coverage and native implementation refinement.

## Mechanized results

`NativeSyntax` records all scalar payloads, vector lengths, child order and
implicit binding edges. `NativeSubstitution` proves simultaneous renaming and
substitution algebra, identity/composition, both interchange laws, dependent
instantiation and finite-scope/arity preservation for this entire vocabulary.
Pi/Lam bind in their second child; IfLt/IfEq bind evidence only in their true
branch. Functions stored in other fields contain explicit lambda binders.

`NativeArena` defines an independent graph representation relation and a
fuel-bounded decoder. It proves decoder soundness, eventual completeness and
uniqueness, preservation of existing meanings under arena extension, fresh
allocation, tree emission, backward references and capture-avoiding arena
renaming/substitution. The arena transformation currently decodes, transforms
the tree and emits the result. Its allocation order and work budget are not
asserted equal to the native mutable implementation.

`NativePartialRenaming` and `NativeArenaPartial` add checked removal of arbitrary
variable blocks, inverse reweakening, scope/arity preservation and native-style
no-removal rewrite. References into removed blocks explicitly fail; replacement
terms are shifted only under actual binding edges. Direct native mutable
execution and machine-cast behavior remain separate obligations.

`NativeTransform` and `NativeReplacementTransform` also traverse arena references
directly, without decoding into a tree or calling the emitter. Their successful
shift/substitute/rewrite results have the proved tree meaning and preserve every
existing node. Depth, visit and allocation budgets, u32 result bounds and signed
arithmetic side conditions are explicit. Failure-state equivalence and exact
native allocation-order/source execution remain separate obligations.

`NativeTyping` independently specifies the supported pure dependent rules with
universes, Prop, ghost/code positions and pre-binder context annotations.
`NativeCheckerSoundness` proves acceptance soundness of the actual executable
`NativeChecker`, including independent checking of type sorts. Supported rules
include:

- Universe levels below 32, Prop/U64/I64 sorts, dependent type abstraction,
  maximum universe levels for Pi and impredicative Prop codomains.
- Erased U64 indices and proposition binders, and rejection of erased variables
  in code. The earlier erased-U64 Raw discrepancy has positive native-syntax
  regressions.
- All older Raw pure operations, signed arithmetic and Strict, arithmetic
  evidence combinators, proposition-only transport and refinements.
- Verified conversion at comparisons and type-head exposure, normalized Decide
  operands, and the conservative native first-order gate for code type arguments.
  Unknown inductive-family representation is rejected by that gate.
- Evidence-binding IfLt/IfEq branches and Absurd. The true branch's inferred
  result is lowered with checked binder removal, so evidence cannot escape its
  scope. Executable code Absurd enforces the native non-function result
  restriction; code neutral application heads remain conservatively rejected.
  Ghost function results are admitted and remain stable under type substitution.
- I64 Fold and dependent Loop with Prop or Type0 motives, including scalar and
  refinement accumulators and genuine Nat induction using its induction
  hypothesis. The exact three-binder telescopes have proved renaming/substitution
  laws. Code admission conservatively rejects explicit memory/family operations
  in the body and owned accumulators; it does not certify their resource use.

`NativeConversion` proves renaming/substitution closure and soundness of the
bounded executable converter. It traverses every native child, even when that
operator has no typing rule yet. Root computation covers beta, bounded
addition/subtraction, local reads, refinement and borrow/deref projections,
literal IfLt/IfEq selection with evidence substitution, and Transport along
reflexivity. `NativeNormalization` independently defines forward computation
and proves the exact computed result is reachable. Bounded residuals need not
be normal forms, and a failed comparison is inconclusive.

`NativeModeSafety` proves mode promotion to ghost, exclusion of erased runtime
variables, constructor arity and finite-context scope of every typed term.
`NativeGhostMetatheory` proves typed renaming, weakening, simultaneous
substitution and genuine dependent instantiation for every currently supported
rule, including universe type arguments. Results are in ghost mode; this is
not an unconditional code-substitution theorem.

`NativeConfluence` proves parallel reduction's diamond property and Church–Rosser
for the selected complete-syntax conversion relation, including overlapping
borrow/deref projections. Pi, sort, equality, array and refinement injectivity
and rigid-constructor separation follow. `NativeTypeUniqueness` proves uniqueness
modulo this conversion for every current rule, even across code/ghost modes,
and derives universe limits and rejection of Type-in-Type.

`NativeContextConversion`, `NativeInversion` and `NativeRootPreservation` supply
lookup-based context transport, conversion-aware inversion and each executable
root's preservation. `NativePreservation` proves contextual ghost preservation
at the exact original type, finite-step preservation and preservation by the
actual `Conversion.normalize` implementation. This applies to all current
pure typing rules; it is not a runtime ownership preservation theorem.
Fold/Loop remain neutral computations, as in native conversion; preservation
covers reductions in their count, motive, initial value and body. In particular,
changing a dependent count preserves the original result type by conversion.

`NativeSchema` / `NativeWire` provide a canonical version-4 full-graph envelope.
Round-trip, encoding injectivity and exact-byte decoding are proved. Whole-graph
validation checks unused nodes too, with proved backward-reference, payload,
arity and graph-count consequences. A measurement pass precedes root expansion
and caps expanded tree size/depth separately from graph size.

`NativeAdmission` checks raw snapshot bytes without derivation certificates.
Acceptance implies exact input re-encoding, whole-graph validity, graph meaning
and well-formed arities for both roots, closed typing in the recorded mode, and
independent ghost typing of the requested type at an inferred sort.

`NativeDefinitions` derives a closed declaration's body mode from its type's
inferred sort, independently of the snapshot's observation-mode flag. Its pure
checker and exact-byte admission prove formation and body typing in that derived
mode. A synthetic erased data identity is accepted as a ghost observation but
rejected as an executable declaration; forging its mode flag cannot authorize
runtime access to its erased parameter.

`NativeGlobalEnvironment` checks ordered whole programs through an independent
transparent-global expansion relation. Both annotation and body expand against
the previously checked prefix, then pass the same sort-derived declaration
checker. Every interpreted entry is typed, locally closed, arity-correct and
global-free; raw references precede their declaration, earlier entries retain
their interpretation, and checked global bodies have unique types modulo
conversion. Expansion precharges repeated body occurrences and bounds output
size/depth. This conservative interpretation can reject opaque code uses of
ghost globals that native inference accepts; it is not a proof of the native
Global inference branch.

`NativeProgramWire` and `NativeProgramAdmission` bind that checked environment
to a canonical version-5 envelope containing all declaration roots and the full
shared graph. Modes are absent from the format. Acceptance proves exact bytes,
graph meanings, declaration formation/body typing, local closure, and exclusion
of forward/self references. Aggregate root expansion is checked before decoding
any declaration, with separate declaration/node/expanded-occurrence bounds.

`NativeAffineSum` implements native-shaped affine canonicalization for the
full-syntax Var/Natural/UAdd profile: sorted variable occurrences, one natural
constant and balanced oversized ghost constants with valid U64 leaves. Equality
is sound and complete for all U64-valued valuations over mathematical naturals;
the U128 collector bound, renaming/substitution compatibility and idempotence are
proved. `NativeAffineTyping` proves exact-original-type preservation in the same
input mode. Its equations now embed into full `ACU.Conv`, which is used by the unified
environment checker. The earlier pure checker retains its selected converter. Runtime folding refusal for oversized constants is explicit;
the typing theorem does not establish runtime overflow or evaluation behavior.

`NativeIrrelevanceBoundary` proves why native proof-irrelevant comparison cannot
be inserted as an unconditional untyped Pack equation: together with Proof
congruence and projection it would equate all raw terms. A faithful integration
requires formation-aware irrelevance.

`NativeFamilyEnvironment` independently checks raw constructor telescopes and
computes their signatures and layouts. Its soundness includes strict positivity,
closed and well-formed telescopes, checked U64 indices, normalized domain/result
formation, unchanged leading parameters, and recursive-field erasure policy.
The mixed program checker interleaves families at their recorded global boundary;
each accepted family has an actual earlier checked program history. It scans
original Pi/Ind structure before normalization. Earlier-family fields, buffers
and family term introduction/elimination are handled by the unified layer below.

`NativeFamilyWire` / `NativeFamilyAdmission` bind those results to exact version-6
bytes containing all definition roots, raw constructor roots, metadata and the
complete shared graph. No external signatures or computed layout bits enter
admission. All definition and constructor occurrences share the pre-expansion
budget. Acceptance derives the independent mixed program judgment and positivity,
closure and arity of every stored raw constructor type.

`NativeQuantity` projects the complete constructor vocabulary into the proved
resource-control semantics. It enforces balanced branches, exact local linear
use, erased locals, closure restrictions, repeat-body capture restrictions and
once-only continuations. Known syntactic lambda spines visit relevant arguments
once outside the consumed scopes and the body under its complete telescope.
Successful checks imply exact completed use, at-most-once prefix use and erased
unreachability in projected traces. Full-native renaming and Var/Borrow(Var)
substitution commute with the concrete projection, including dependent-reader
opening and continuation aliasing. A fresh query checks local scopes even when
the outer owner list is empty. The standalone projection takes outer owner/erased lists; `NativeOwnership`
and the unified admission layer derive them from actual types and checked family
metadata. Unknown call signatures, unresolved binder domains and alias-sensitive
Lend remain rejected. Native heap execution and u32 counter equivalence remain
separate obligations.

`NativeACU` explicitly extends conversion by UAdd associativity, commutativity
and zero, with full binding-aware renaming/substitution. `NativeACUAffine` derives
affine canonical forms through actual finite ACU and bounded literal-add
equations, without oversized invalid literals or semantic-reflection assumptions.
The separate pure `Theory` has a genuine full-syntax bag characterization,
rigid/Pi injectivity and forward Church–Rosser. Its forward reduction eliminates
zero without arbitrary unit insertion. This does not yet prove Church–Rosser or
injectivity for the combined relation at that stage. `NativeACUFullConfluence` and
`NativeACUForwardConfluence` now prove full `ACU.Conv` injectivity and an actual
common finite forward `MixedRed` reduct, including beta and every legacy
observing contraction. Zero is only eliminated; no reverse legacy contraction
is introduced. The original pure checker retains its established converter;
the unified checker uses the concrete bounded full-ACU normalizer/comparator in
all conversion, head-exposure and representation-policy slots.
The arithmetic extension additionally has a proved bag characterization,
natural/rigid/Pi injectivity and independent forward Church–Rosser. Valid literal
addition is included, while invalid oversized literals remain distinct atoms.
The proof-only unit expansion is handled symbolically; it is not the executable
native normalizer. Full beta/observation transport and contextual composition are supplied by the
subsequent transport, parallel and forward-confluence modules.
`NativeACULegacyTransport` now constructs forward mixed reductions transporting
every non-add legacy root across arithmetic equivalence, including hidden
lambda/elements/pack/borrow/reflexivity heads and dependent branch substitution.
This supplies root transport; full contextual parallel rewriting and actual combined
Church–Rosser are supplied by the subsequent full and forward confluence modules.

`NativeResourceSyntax` proves the actual Buffer/ref operation telescopes commute
with binding transformations, including checked Load-result binder removal.
`NativeOwnership` derives owner and erased positions from the concrete context,
proves agreement with weakened lookup annotations, and connects checks directly
to lookup-based trace accounting. Closed checking uses depth zero and empty
outer position lists. This removes caller-supplied resource lists at that gate;
resource typing and closed declaration admission are supplied by the unified layer.

## Actual native correspondence tests

The exhaustive writer `compiler/core_native_snapshot.jh` calls the actual native
parser/checker/inference and serializes all 54 constructors. It performs no
additional Core call during serialization. The version-4 CLI runs the same pure
admission function whose soundness is proved, after bounded input scanning.

`tests/native_kernel_schema.py` compares the Lean metadata with the actual native
Term declaration and four binder-sensitive transform cases. An exhaustive native
writer fixture also matches the proved Lean encoder for all constructors at
vector lengths 0, 1 and 3: **162 exact byte comparisons**.

`tests/core_native_kernel_correspondence.py` retains actual sources, full
snapshots, hashes and labelled synthetic mutations. Its native cases include
universes, high impredicative Prop, polymorphism in both modes, erased indices,
transport/refinement projections, evidence-binding branches, absurdity,
arithmetic evidence, scalar iteration, refinement iteration and Nat induction.
There are 89 source fixtures and 31 additional checks. This legacy pure path
retains owned/effectful-iteration gaps; the unified gate below now checks those
forms with authentic representation and quantity conditions.
Native code rejection of erased proof variables is also checked.

The production shift/substitute/rewrite routines are also exercised directly
on every constructor, three vector lengths and four operations, with an extra
free-variable case: **660 actual Core calls**. Independent before/after snapshots
preserve old-prefix comparisons; expected results come from the proved Lean
binding transformations, including explicit negative-shift rejection.

These comparisons are regression evidence. Native parser/exporter behavior,
source execution, process association and IO are outside the pure theorems.

The whole-program suite also checks 15 actual source programs, one constructed
Core API opaque-proof case and 14 labelled mutations. The affine suite compares
90 actual Core.normal results across variable/literal counts and three tree
groupings, including oversized constants; five mutations check rejection of
wrong results, prefix changes, unsupported atoms and incomplete coverage.

The family suite checks 20 actual source programs and 18 labelled mutations.
Quantity observations retain each complete arena, context references/erasure
flags and queried variable: 32 count/rejection agreements, seven deliberately
stricter invalid-local-scope checks and one unknown-callee boundary. Six
mutations test its comparison adapter. Bare native runtime_uses does not itself
validate all local scopes, so the stricter cases are not equivalence claims.

## Completion obligations

The full native kernel is verified only when the following remaining obligations
are discharged, rather than replaced with more passing fixtures:

1. Extend the proved contextual ghost preservation and typed substitution to the
   remaining typing/computation rules. Code substitution additionally needs
   preservation of mode and representation restrictions.
2. A consistency/normalization argument for the universe-aware judgment, beyond
   forward reachability of a bounded untyped simplifier.
3. The remaining typing rules: Lend and active-loan runtime Borrow,
   together with exact native opaque-global behavior. Owned/effectful iteration,
   checked families, dependent constructors, proposition/data elimination,
   Case/Drop, borrowed View, owned Ref and Back/Give/Take already share the unified judgment.
   Their remaining native computation equations still require integration.
4. Runtime ownership, quantities, borrow/continuation boundaries and first-order
   representation, connected to the same complete native judgment. Existing
   restricted resource proofs do not automatically supply this connection.
5. The remaining native conversion equations and formation-aware
   proof-irrelevant comparison, and refinement of native graph operations,
   normalization/comparison, inference,
   family declaration and whole-program checking by their actual implementation
   semantics. A Lean port or syntactic interface audit alone does not discharge it.

The existing top-level proof goal remains active until these native-kernel
obligations are actually completed. LLVM/compiler backend verification is a
separate task.

## Reproduction

With Lean 4.34.1 and the native development toolchain:

```sh
cd proofs
bash check.sh
../scripts/proof-limits.sh lake env lean -M 4096 -j 1 -DwarningAsError=true CheckNativeInference.lean
cd ..
scripts/proof-limits.sh python3 tests/core_native_kernel_correspondence.py --output out/native-kernel-correspondence
scripts/proof-limits.sh python3 tests/core_native_program_correspondence.py --output out/native-program-correspondence
scripts/proof-limits.sh python3 tests/core_native_affine_correspondence.py --output out/native-affine-correspondence
scripts/proof-limits.sh python3 tests/core_native_family_correspondence.py --output out/native-family-correspondence
scripts/proof-limits.sh python3 tests/core_native_quantity_correspondence.py --output out/native-quantity-correspondence
scripts/proof-limits.sh python3 tests/core_native_ownership_correspondence.py --output out/native-ownership-correspondence
scripts/proof-limits.sh python3 tests/core_native_unified_correspondence.py --output out/native-unified-correspondence
scripts/proof-limits.sh python3 tests/core_native_back_correspondence.py --output out/native-back-correspondence
scripts/proof-limits.sh python3 tests/core_native_acu_normalizer_correspondence.py --output out/native-acu-normalizer-correspondence
scripts/proof-limits.sh python3 tests/core_native_delta_correspondence.py --output out/native-delta-correspondence
scripts/proof-limits.sh python3 tests/core_native_data_correspondence.py --output out/native-data-correspondence
scripts/proof-limits.sh python3 tests/core_native_owned_loop_correspondence.py --output out/native-owned-loop-correspondence
```

The aggregate imports the native modules and examples; every public theorem is
included in the exact-count axiom audit. The graph-certificates flake check
builds the admission dependencies and runs the actual native correspondence
suite, including the exhaustive schema/serialization checks.


## Unified typed environments and resource admission

`NativeKernelEnvironment` holds syntax-only global/family records shared by
signature checking and the environment-indexed kernel. `NativeEnvironmentTyping`
and its concrete checker use one mutual judgment for all earlier pure rules,
Global, Ind, dependent Con, proposition Elim, Buffer allocation/store/free/load,
Ref formation, ghost Borrow/Deref, borrowed Index and Back/Give/Take. Acceptance soundness,
actual-term arity/scope and environment-extension transport are proved. This is
a genuine extension of the earlier calculus; its old metatheorems are not
silently asserted for the added rules.

`NativeOwnershipAdmission` derives declaration mode from the inferred sort and
requires the closed quantity gate for code, independent of the observation flag.
All leading function lambdas share one telescope, matching Core.uses_function;
callbacks open the exact prefix and reclose any remaining function. This admits
owner-before-index functions while preserving real closure-capture rejection.
The source suite checks 22 programs and 21 exact-byte comparisons/mutations.

`NativeUnifiedFamilies`, `NativeUnifiedProgram` and `NativeUnifiedAdmission`
remove the earlier pure-prefix restriction. Ordinary fields, earlier families,
dependent Buffer fields and family/resource-valued globals use the same unified
checker. Independent history, recomputed positivity/parameters/layout, exact
bytes, authenticated resource projection and environment/formal-signature scope
invariants are proved. Native Lend/active-loan rules, runtime substitution
and universe consistency remain completion work. Ghost substitution, type uniqueness and exact-original-type forward
preservation are proved for every rule in this checkpoint.
The integrated source suite checks 49 mixed programs and 41 exact-byte checks,
including dependent Buffer fields, earlier flat/boxed families, constructor-valued
globals, resource leaks/duplication and malformed unused graph nodes.

`NativeACUBoundedNormalizer` supplies a concrete full-Term NormalizerKit, with
compact arbitrary-atom collection/sorting and balanced valid constant leaves.
Both actual ACU conversion soundness and exact finite forward output reachability
are proved. It preserves Option failure at fuel/work/depth limits and retains
all proof and Strict children. Of 204 actual Core.normal comparisons, 202 match
exactly; selected array-read and proof-slot-ordering boundaries are explicit,
and all outputs pass the proved comparator. Eight mutations reject.

The native runtime-only function-result guards had a real ghost preservation
bug: both added ghost Load/Absurd fixtures checked successfully but their beta
normal forms were rejected. Core now applies those capture guards only to code;
the model's executable ghost policies agree. Actual Core unit tests and all 18
preservation fixtures pass after the fix. This does not by itself discharge the
remaining source-semantics refinement or full-calculus consistency obligations.

`NativeEnvironmentConversion` connects every unified conversion and head-exposure
slot to actual `ACU.Conv` and `ACU.Bounded.kit`. Its code representation gates
conservatively reject unresolved Global aliases; ghost embedding of the earlier
pure judgment is proved without casting code policies from a smaller conversion
relation. Back/Give/Take include owned and erased results, dependent motives,
checked two-binder result removal and metadata-derived ownership. Their suite
checks 37 actual source fixtures and 28 exact-byte checks. The aggregate axiom
audit currently covers 5,670 declarations using only Lean's standard logical
axioms, with warnings treated as errors.

`NativeEnvironmentOperationalRoots` proves original-type ghost preservation for
additional pure value equations: signed literal arithmetic within I64 bounds,
Strict's result, pure Free and empty Fold/Loop. Its bounded root-only evaluator
has exact finite reachability, decreasing node count and eventual root normality;
overflow remains uncontracted. These equations are not silently inserted into
`ACU.Conv`: contextual preservation/confluence of the combined theory remains
open. The three new source fixtures bring actual Core preservation regressions
to 21, including both signed bounds, overflow and unused trapping loop bodies.

`NativeEnvironmentGhostMetatheory` and `NativeEnvironmentContextConversion`
establish mode promotion, typed ghost renaming/weakening, simultaneous
substitution, dependent instantiation and context conversion for the current
unified judgment, now comprising 60 HasType constructors plus Binder formation
and five mutual judgments. The required environment premise contains
closed global types and scoped formal constructor signatures; mixed checked
history proves that premise. It is not an arbitrary well-formed-environment
assumption supplied by a certificate. Binding algebra covers captured motives,
recursive proposition cases and two-binder Load/Take removal. These are ghost
results; runtime substitution remains a separate obligation. Full contextual
ghost preservation for the current ACU relation is supplied below.

`NativeEnvironmentInversion`, `NativeEnvironmentTypeUniqueness` and
`NativeEnvironmentContextualPreservation` now establish principal inversion,
cross-mode type uniqueness and exact-original-type ghost preservation for every
current unified rule under actual full ACU conversion. The forward theorem
covers the actual `MixedRed` relation and concrete bounded normalizer, with
environment closure supplied by checked history. It handles dependent
constructor fields, captured proposition motives, Ref/Buffer shapes and the
actual leading-lambda shape of Take. No preservation under arbitrary symmetric
untyped conversion is assumed.

`NativeEnvironmentDelta` derives closed/global-free interpreted entries from
the same mixed history and proves binding-natural, idempotent global expansion.
`NativeEnvironmentDeltaConversion` combines it with actual ACU: delta and node
congruence, substitution, Pi/sort injectivity, genuine finite forward confluence
and conversion iff forward join. `NativeEnvironmentDeltaBounded` precharges
repeated bodies against a shared allowance before ACU normalization, propagates
unknown/malformed-global and budget failure, and proves exact forward results,
sound comparison and output bounds. The delta root preserves the original type
in the existing unified judgment using its actual stored body typing.
`NativeEnvironmentConversionBasis` now installs an environment-indexed
inductive delta/ACU relation into the same typing constructors and executable
checker. The executable normalizer, comparison, inferred-head exposure and
runtime domain checks use the actual environment. Acceptance soundness does
not assume admissibility: every successful bounded operation yields an actual
finite forward derivation in the inductive relation. Admissibility is used
where needed for confluence and rigid/Pi/sort injectivity, and closed stored
bodies are used for renaming and substitution. Mixed checked history derives
both invariants; callers do not supply a validity oracle.

Full contextual delta preservation now uses actual checked history to obtain
the stored body's typing. `GhostTransform` carries the actual combined
`EnvironmentDelta.Forward` path; its child theorem retains the original type
under every existing binding/resource/elimination rule. Successful concrete
normalization therefore retains an independently derived original type,
including a type which still contains global aliases. The ACU-only forward
preservation theorem continues to need only the closed/transparent world.
No preservation of arbitrary symmetric conversion representatives is asserted.

The delta source suite checks 19 actual programs and 22 exact-byte comparisons
and mutations, binding checked version-6 metadata and before/after arenas to the
same original root and unchanged prefix. It retains a genuine native-accepted
generic-quantity gap: authentic abstract kind/representation contexts and
unknown-callee signature replay are still needed. Parser/export/IO execution
refinement, all native equations and universe consistency remain open.

Owned Fold/Loop, data Elim/Case/Drop and generic owned Ref/Borrow/Deref now
extend that same checker and all its ghost metatheory. The exact iteration
telescope retains the original bound; Buffer and boxed accumulators permit
memory under their three leading callback lambdas. Other function expressions
retain the native effect gate. Data branches are generated from checked
parameters, fields, recursive hypotheses and actual motive; positivity,
scoping and binding/motive naturality are proved. The five mutual judgments
have cross-mode uniqueness and original-type forward normalization preservation.
Case quantities enforce equal branch use and zero recursive outer captures;
closed admission computes metadata and normalizes binder annotations itself.

The joint tests pass 23 native data programs/22 byte checks, 28 owned iteration
programs/26 byte checks, and all prior Back/ownership/mixed-program regressions.
Thirty-five data, 24 iteration and seven expanded-metatheory Lean regressions
also pass. An accepted ghost Drop equality remains an explicit rejected-model
boundary because Drop computation has not been inserted into ACU. Existing
proved Borrow/Deref inverse equations are retained. These results do not prove
native heap execution, active-loan semantics or machine counter fidelity.

`NativeViewSyntax` derives borrowed View branch telescopes from the same checked
constructor signatures. Its field plan is computed before parameter substitution;
recursive boxed fields receive borrowed arguments and runtime recursive results.
Dependent field reads preserve every binder and dereference earlier borrowed
fields. Scoping, arbitrary outer substitution/renaming, prefix extension and
motive conversion are proved for the concrete successful builder. Unknown field
layouts reject. Dependent code motives enforce the native fixed representation gate;
ghost motives remain closed under typed substitution.

View now shares the environment-indexed delta checker and all 60-rule ghost,
context, uniqueness and actual forward-preservation proofs. Forty typing,
resource, program and direct-global regressions and 17 telescope regressions
pass. The native suite covers 33 source programs and 28 exact-byte checks,
including typed recursive-result leaks/duplication and code dereference mutations.
Two native-accepted equalities remain explicit gate rejections because View iota
has not been added. Neither active loans nor runtime heap preservation is assumed.

`NativeClosedTerm` now supplies generic closed-term algebra independently of
typing. Delta algebra/conversion/bounded search use only that lower layer;
`NativeEnvironmentDeltaChecked` authenticates it from mixed history afterward.
This permits installation of delta into typing without import cycles. Prefix
metadata (`NativeEnvironmentPrefix`) is also independent of typing. The code
nonfunction condition is now a positive conversion-to-head witness, so adding
a later definition preserves an earlier certificate. Its exclusion of Pi uses
the authenticated world. The raw declarative application policy permits
conversion representatives; only actual executable application checking
provides a computed normal form for runtime kind safety.

`NativeEnvironmentPlainSeparation` proves that an actually plain type cannot
convert under the current ACU theory to Buffer, Ref, Pi, Back or a boxed family.
The proof uses raw Boolean forward invariants and genuine Church–Rosser; it
does not assume symmetric preservation of plainness or typing. Seven regressions
include the explicit failure of reverse-beta plainness invariance. Authentic
abstract kinds and typed-index representation interpretations remain work.


`NativeEnvironmentDeltaCAPIExamples` exercises the installed same-judgment
checker with global type aliases, global functions, aliases in binders,
global/beta normalization, exact-original-alias-type preservation, and
unknown/malformed-alias refusal. `NativeEnvironmentConversionBoundary`
mechanically demonstrates why closed stored bodies matter: a raw table whose
body is an open variable collapses delta/beta conversion between all terms.
Such a table cannot satisfy the world invariant derived from checked history.
The native delta adapter also checks original source bodies and observed normal
outputs with this installed typing checker, in addition to exact graph/prefix
and combined-conversion checks. Native parser/export/IO refinement remains open.


`NativeFiniteUniverses`, `NativeFinitePi`, and the contextual universe model/code
modules construct a finite Tarski hierarchy, dependent Pi closure, contextual
substitution, and concrete encode/decode equations for the native universe range
and administrative top. Three text generators reproduce the checked modules
exactly; they supply no logical axioms. This host model is not a total
interpretation of all native typing derivations.

`NativeFunctionFundamental` now reconstructs a concrete U64/nondependent-function
expression from actual unified `HasType` and syntax-only recognition. Its
contextual realization is derived for every realizing closing substitution;
source membership or normalization is not an input. Arbitrary raw result
conversions remain allowed. `NativeTypeFormationBoundary` verifies that raw
result-type regularity fails: a natural value may be assigned `UAdd U64 0`, even
though that type has no sort. `NativeQuotientTypingBoundary` separately verifies
that symmetric arithmetic quotient steps need not preserve term typing. Neither
false property is used by the semantic development.

`NativeNumeralForward` proves that conversion to a valid numeral in an
admissible world gives a genuine finite delta/ACU forward path to that numeral.
Forward descendants of literals remain numeric trees; symbolic contraction
handles arbitrary valid totals without allocating unary expansions of large
constants. `NativeFunctionNormalization` applies this to actual recognized
U64/function source typing, retaining the original independently checked type
under real checked history and proving unique numeral results. This establishes
weak normalization of that fragment, including arbitrary-depth identity chains;
it does not assert termination of commutative reduction or completeness of the
bounded executable search.

The candidate/atomic observation modules additionally derive truth for their
explicit supported proof trace. Actual checked global reflexivity is supported
after delta unfolding; opaque Load stays conservatively rejected. Full dependent
universe/family/resource/iteration fundamental lemmas, full consistency, source
execution refinement, and native loan obligations remain open.


`NativeDependentFormulaSemantics` and `NativeDependentProofFundamental` extend
actual source reconstruction to Refl, U64 lambdas and applications with
variable/literal indices and genuinely dependent proposition codomains. The
semantic families include equality, order and impredicative U64 Pi; substitution
and conversion coherence hold for every natural assignment. Actual `HasType`
and syntax-only recognition derive truth of the raw result conversion class,
including authentic global aliases and unformed raw proposition representatives.
False closed equality and order atoms are excluded throughout that grammar.
This is a dependent source fundamental theorem for the stated grammar, not a
fundamental lemma for arbitrary universe-polymorphic terms or native resources.
