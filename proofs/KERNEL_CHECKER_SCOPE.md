# Executable dependent kernel: verified scope

The executable `Jihoo.KernelChecker` infers and checks raw terms without an
input derivation, typing certificate, or reduction trace. Its acceptance theorem
uses the existing independently defined `CoreBridge.Raw.Beta.HasType` and
`IsType` judgments. It covers the complete universe-free, ghost-mode `Raw`
syntax. Native `compiler/core.jh` has additional syntax and rules; its
implementation has not been proved equivalent to this checker.

## Executable checking and conversion

| Operation | Supported behavior |
| --- | --- |
| `infer fuel ctx term` | Variables, bounded unsigned/signed literals, addition, proof-checked subtraction, signed arrays, literal ordering evidence, reflexivity, zero bounds, proof-checked indexing, dependent lambdas and application |
| `isType fuel ctx ty` | U64, I64, arrays with typed length indices, equality and ordering with typed indices, and dependent Pi formation |
| `check fuel ctx term expected` | Independent expected-type formation and conversion of the inferred type to the requested type |
| `KernelConversion.normalize fuel term` | Every Raw child position, including annotations and proof fields; capture-avoiding beta contraction, nonoverflowing literal addition, nonunderflowing literal subtraction, and finite local-array selection |
| `KernelConversion.equal fuel a b` | Structural equality of the two computed residuals; success proves conversion and a common forward reduct |
| `KernelAdmission.checkBytes fuel bytes` | Exact canonical version-3 snapshot decoding, bounded whole-graph validation, and closed checking of the selected roots |

Contexts are newest first. Each stored annotation is in its pre-binder scope;
lookup performs weakening. Pi and lambda require the erased flag to equal the
domain's proposition classification. `decide` accepts literal natural endpoints
with independently checked word bounds and strict comparison. An empty array
has length zero. Application and indexing normalize the inferred type before
inspecting its Pi or array constructor. Arguments and bounds witnesses are
checked by verified conversion, including conversion inside dependent indices.

Checker fuel zero rejects. Normalizer fuel zero returns the input unchanged.
The normalizer returns a convertible residual when its budget is exhausted;
it does not report that residual as a complete normal form. Comparison failure
is inconclusive. Fuel bounds recursive depth, not total allocation, execution
time or tree traversal. Beta contraction and dependent application use the
existing `Typing.substitutionSafe` size/depth guard before substitution.

An addition can have type U64 while its runtime execution would overflow.
Typing is not a trap-freedom theorem. Literal folding leaves overflow and
underflow neutral. Closed proof truth is guaranteed only for closed contexts;
an arbitrary supplied open context may contain false assumptions. `infer`
therefore does not by itself promise formation of its returned type under an
arbitrary context. `check` independently establishes the expected type's
formation.

## Mechanized guarantees

- `KernelConversion.normalize_sound` and `equal_sound` construct conversion
  derivations for the actual executable results, on every Raw input.
- `KernelNormalization.normalize_steps` proves that the exact computed
  residual is reachable by forward beta/arithmetic/read computation. Its
  preservation theorems retain the original raw type, preserve formation,
  and permit independent normalization of a term and its result type.
- `KernelChecker.infer_sound`, `isType_sound` and `check_sound` prove acceptance
  soundness together by induction on the concrete checker budget.
  `check_isType` proves independent formation and `infer_instantiate` proves
  capture-avoiding dependent instantiation.
- `Beta.HasType.unique` proves type uniqueness modulo conversion for every
  derivation of the existing declarative judgment, including arbitrary fixed
  contexts. Consequences retain function binder modes and codomains, equality
  indices and concrete array lengths, and rule out scalar type confusion.
- `KernelAdmission.checkBytes_sound` binds closed typing and formation to the
  exact original bytes and complete graph. `checkBytes_represents` also gives
  the graph representation relation for both roots. No typing certificate is
  supplied or replayed.
- `KernelAdmission.checkBytes_normalizes` connects admitted bytes to the
  existing unconditional closed head-normalization theorem.
  `checkSnapshot_preservation` retains the declared type through contextual
  beta sequences. Literal equality and ordering truth follow from admitted
  evidence, and false closed equality/bound snapshots are rejected.

All these proofs are checked by Lean 4.34.1. They use no `sorry`, new axioms,
`native_decide`, assumed checker-soundness premise, or proof-bearing input.
The aggregate axiom audit permits only Lean's standard logical axioms.

## Native correspondence and remaining boundary

`tests/core_kernel_correspondence.py` compiles the existing snapshot exporter
against this checkout's actual `compiler/core.jh`. Accepted native sources feed
their exact retained snapshot bytes to `CheckKernelInference.lean`, which runs
the proved `KernelAdmission.checkBytes` function after bounded IO preflight.
The runner retains sources, snapshots, hashes, observed outcomes and adversarial
payloads in its output directory.

The suite covers arithmetic and beta conversion, computed array lengths and
indices, dependent array application, a dependent reader with three
applications, subtraction and index proof checking, literal boundaries and
capture avoidance. It also rejects malformed transport, incorrect roots,
false equality/ordering mutations and an invalid unreachable graph node.
Native erased U64 binders remain an explicit accepted-native/rejected-Raw case.
These comparisons are regression evidence, not a native refinement theorem.

Native parser/exporter fidelity, build and process association, code generation
and IO remain trusted. Universes, Prop as a term, globals, inductive families,
additional arithmetic/evidence rules, runtime quantities, ownership, effects
and LLVM are outside Raw. Native normalization also has additional equations.
Completeness, native `Core.infer` / `Core.normal` equivalence, full contextual
normalization and whole-compiler correctness are not claimed.

## Reproduction

With pinned Lean and the repository's native development environment:

```sh
cd proofs
lake build --wfail
bash check.sh
lake env lean -DwarningAsError=true CheckKernelInference.lean
cd ..
python3 tests/core_kernel_correspondence.py --output out/kernel-correspondence
```

`Jihoo.lean` imports all kernel modules and examples. `Audit.lean` checks every
public theorem in the new conversion, normalization, checker, uniqueness and
admission modules and all their named examples. `check.sh` verifies the exact
aggregate audit count and allowed axiom dependencies. The existing
`lean-proofs` and `graph-certificates` flake checks retain this integration.
