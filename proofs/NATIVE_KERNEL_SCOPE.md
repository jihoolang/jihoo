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

`NativeConversion` proves renaming/substitution closure and soundness of the
bounded executable converter. It traverses every native child, even when that
operator has no typing rule yet. Root computation covers beta, bounded
addition/subtraction, local reads, refinement projections and borrow/deref
projections. `NativeNormalization` independently defines forward computation
and proves the exact computed result is reachable. Bounded residuals need not
be normal forms, and a failed comparison is inconclusive.

`NativeModeSafety` proves mode promotion to ghost, exclusion of erased runtime
variables, constructor arity and finite-context scope of every typed term.
`NativeGhostMetatheory` proves typed renaming, weakening, simultaneous
substitution and genuine dependent instantiation for every currently supported
rule, including universe type arguments. Results are in ghost mode; this is
not an unconditional code-substitution theorem.

`NativeSchema` / `NativeWire` provide a canonical version-4 full-graph envelope.
Round-trip, encoding injectivity and exact-byte decoding are proved. Whole-graph
validation checks unused nodes too, with proved backward-reference, payload,
arity and graph-count consequences. A measurement pass precedes root expansion
and caps expanded tree size/depth separately from graph size.

`NativeAdmission` checks raw snapshot bytes without derivation certificates.
Acceptance implies exact input re-encoding, whole-graph validity, graph meaning
and well-formed arities for both roots, closed typing in the recorded mode, and
independent ghost typing of the requested type at an inferred sort.

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
transport/refinement projections and arithmetic evidence. Unsupported ownership,
branch and fold rules remain explicit admitted-native/rejected-Lean fixtures.
Native code rejection of erased proof variables is also checked.

These comparisons are regression evidence. Native parser/exporter behavior,
source execution, process association and IO are outside the pure theorems.

## Completion obligations

The full native kernel is verified only when the following remaining obligations
are discharged, rather than replaced with more passing fixtures:

1. Contextual preservation for the universe-aware judgment, including context
   conversion and binder changes. Typed ghost substitution is proved. Code substitution
   additionally needs preservation of mode and representation restrictions.
2. A consistency/normalization argument for the universe-aware judgment, beyond
   forward reachability of a bounded untyped simplifier.
3. The remaining typing/computation rules: evidence-binding branches, folds/loops,
   absurdity, globals, checked inductive/data family environments and elimination.
4. Runtime ownership, quantities, borrow/continuation boundaries and first-order
   representation, connected to the same complete native judgment. Existing
   restricted resource proofs do not automatically supply this connection.
5. Refinement of native graph operations, normalization/comparison, inference,
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
```

The aggregate imports the native modules and examples; every public theorem is
included in the exact-count axiom audit. The graph-certificates flake check
builds the admission dependencies and runs the actual native correspondence
suite, including the exhaustive schema/serialization checks.
