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
  scope. Executable Absurd enforces the native non-function result restriction;
  neutral application heads remain conservatively rejected.
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
input mode. This standalone canonicalizer does not yet extend the current Conv
relation or checker. Runtime folding refusal for oversized constants is explicit;
the typing theorem does not establish runtime overflow or evaluation behavior.

`NativeIrrelevanceBoundary` proves why native proof-irrelevant comparison cannot
be inserted as an unconditional untyped Pack equation: together with Proof
congruence and projection it would equate all raw terms. A faithful integration
requires formation-aware irrelevance.

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
There are 87 source fixtures and 31 additional checks. Owned accumulators and
effectful iteration bodies remain explicit admitted-native/rejected-Lean fixtures.
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

## Completion obligations

The full native kernel is verified only when the following remaining obligations
are discharged, rather than replaced with more passing fixtures:

1. Extend the proved contextual ghost preservation and typed substitution to the
   remaining typing/computation rules. Code substitution additionally needs
   preservation of mode and representation restrictions.
2. A consistency/normalization argument for the universe-aware judgment, beyond
   forward reachability of a bounded untyped simplifier.
3. The remaining typing/computation rules: owned/effectful folds and loops,
   native opaque global inference, checked inductive/data family environments
   and elimination.
4. Runtime ownership, quantities, borrow/continuation boundaries and first-order
   representation, connected to the same complete native judgment. Existing
   restricted resource proofs do not automatically supply this connection.
5. Integration of the standalone affine results into full conversion, all other
   native equations and typed proof-irrelevant comparison, and refinement of native graph operations,
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
lake env lean -DwarningAsError=true CheckNativeInference.lean
cd ..
python3 tests/core_native_kernel_correspondence.py --output out/native-kernel-correspondence
python3 tests/core_native_program_correspondence.py --output out/native-program-correspondence
python3 tests/core_native_affine_correspondence.py --output out/native-affine-correspondence
```

The aggregate imports the native modules and examples; every public theorem is
included in the exact-count axiom audit. The graph-certificates flake check
builds the admission dependencies and runs the actual native correspondence
suite, including the exhaustive schema/serialization checks.
