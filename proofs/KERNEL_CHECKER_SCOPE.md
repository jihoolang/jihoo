# Raw checker scope and native correspondence

`Jihoo.KernelChecker` takes raw terms, not derivation certificates. Its
acceptance-soundness target is the existing `CoreBridge.Raw.Beta.HasType` /
`IsType` judgment under `GraphCertificates.Typing.context`. This is a
universe-free, ghost-mode fragment. It is not a proof of native `Core.infer`,
completeness, native equivalence, or whole-kernel correctness.

The interface is `infer fuel ctx term : Option Raw` and
`isType fuel ctx ty : Bool`. Contexts are newest first; each stored annotation
is in its pre-binder scope and lookup weakens it. Context well-formedness is
not assumed, matching the existing declarative variable rule. Consequently,
`infer` success alone does not promise that its output type passes `isType`
for an arbitrary caller-provided context. The snapshot regression adapter
checks both on closed terms.

## Checked implementation rules

The following line references are to `compiler/core.jh` at main
`644ccf1280c7e88bd0fbdf1d561d44bd903a2975`.

| Native rule | Raw checker relationship |
| --- | --- |
| `infer`, 2138–2186: variables, literal types, Eq and Refl | Lookup reverses native's oldest-first context. Eq/Refl require U64 operands; literal bounds are explicit in Raw because its payloads are unbounded Nat/Int. Native payloads are u64/i64. |
| `infer`, 2284–2288: UAdd | Both operands must have U64 type. Neither inference rule promises the sum fits in u64. |
| `binder`, 1591–1615; Pi/Lam, 2769–2795 | Raw requires `erased = domain.proposition`. Native also permits erased u64/data binders; those additional cases are intentionally rejected. Runtime linearity is outside Raw. |
| App, 2796–2828 | Infer a Pi, check the argument against its domain, substitute the argument into the codomain. Raw requires a syntactic Pi and structural argument-type equality. |
| `transform`, 270–307; `shift`/`substitute`, 512–524 | Native shifts free occurrences below binders and decrements indices above the removed binder. Raw uses existing `subst (single argument)` and context weakening. The nested regression checks capture avoidance. |
| `require`/`equal`, 1576–1580 and 1618–1629 | Native normalizes both types before structural comparison. Raw performs no normalization or conversion search. |
| `normal`, 551 onward, and UAdd at 887–891 | Native beta/arithmetic normalization is additional behavior, not refined by this checker. |
| `tick`, 263 onward; `DEPTH`, 12 | Native depth/work budgets and Raw fuel are different mechanisms. No one-to-one budget or termination-cost equivalence is claimed. |

Formation supports U64, I64, Eq and dependent Pi. Inference supports variables,
bounded natural/integer literals, UAdd, Refl, Lam and App. All other Raw
constructors reject. Universes, Prop and globals have no Raw constructor;
unreachable native sort nodes may remain in the existing graph envelope, but
cannot be selected as a Raw term or type. Arrays, Lt, elements, indexing and
subtraction are intentionally unsupported in this iteration. Runtime ownership,
inductives, universes, native normalization refinement and LLVM are outside scope.

Fuel zero rejects. Fuel bounds recursive checker depth, not total work in context
lookup, equality or raw-tree traversal. Application additionally reuses
`TypingCertificates.substitutionSafe` (tree size/depth product guards). This is
not a general denial-of-service or total resource bound on arbitrary Raw inputs.
The existing snapshot adapter adds its own bounded byte/graph decoding.

## Regression evidence and trust boundary

`Jihoo/KernelCheckerExamples.lean` proves concrete outcomes by kernel-checked
simplification/reduction of the implementation. It covers dependent application,
free-variable capture beneath a returned lambda, telescope lookup, false equality
evidence, wrong argument types, literal bounds, unsupported constructors, binder
flags, structural conversion rejection and fuel exhaustion. No `native_decide`,
axiom, admitted proof or derivation-certificate input is used.

`tests/core_kernel_correspondence.py` builds the existing
`tests/core_typing_snapshots.jh` against this checkout's `compiler/core.jh`.
The production exporter `compiler/core_snapshot.jh:71–96` parses and checks the
one-definition source, calls native ghost-mode inference, and retains declared
or actual inferred roots. Lines 175 onward serialize the complete resulting
arena without another Core call. `CheckKernelInference.lean` uses existing
`TypingInput.canonicalSnapshot` and `GraphCertificates.decode`, then invokes the
raw checker on those decoded roots. No alternate codec or proof producer is added.

Matching snapshots are regression evidence, not a formal translation theorem.
The association of source, compiled exporter, native calls, graph serialization,
process output and executed Lean code remains trusted. Kernel-checked theorems
concern the Lean definitions; executing a Lean IO adapter also trusts code
generation/runtime. The runner retains original sources and exact snapshot bytes
and writes a manifest with source hashes and observed outcomes when `--output`
is supplied. It does not authenticate an arbitrary external snapshot's origin.

The conversion-gap fixture is accepted natively and rejected structurally.
The array fixture is accepted natively and rejected as unsupported. Invalid
argument and false-equality fixtures fail native checking before any snapshot
exists; corresponding Raw rejections are checked separately in the Lean examples.
The runner also checks actual inferred roots for dependent/capture cases, fuel
0/1, a mutated selected type root and malformed transport. It never changes the
native checker to force outcomes to agree.

## Reproduction and integration dependencies

With the repository's native development shell and pinned Lean 4.34.1:

```sh
cd proofs
lake build Jihoo.KernelChecker Jihoo.TypingInput
lake env lean -DwarningAsError=true Jihoo/KernelCheckerExamples.lean
lake env lean -DwarningAsError=true CheckKernelInference.lean
cd ..
python3 tests/core_kernel_correspondence.py --output out/kernel-correspondence
```

The aggregate `Jihoo.lean` imports the concrete checker soundness proofs and all
31 reduction examples. `Audit.lean` audits the four public soundness theorems,
the two exhaustion helpers and the two named dependent/capture examples;
`check.sh` enforces the updated exact audit count and existing axiom allowlist.
The existing `lean-proofs` flake check runs this aggregate. The existing
`graph-certificates` check builds the checker alongside its existing validator
imports and runs the native correspondence suite once. No additional CI job or
redundant optimized-Python run is added; the suite uses explicit `require`
checks rather than Python assertions. Existing coverage and security checks
are retained.

## Worker C validation record

Checked against A commit `232cf0db47650603ce78b33b5ee0178d292afde9`;
`KernelChecker.lean` SHA-256
`3a664a869f96a1ae4af64430c63d6a04d461fb11ba3b9c389a0081dfc0f44d55`.
All 31 Lean examples and the snapshot adapter passed Lean 4.34.1 with
`-DwarningAsError=true`. The named `dependent_application` and `nested_capture`
proofs report only `propext` and `Quot.sound` in their elaborated axiom lists.
The 12 native fixtures and seven additional snapshot/fuel checks passed using
LLVM 21.1.8 and the repository's pinned seed to compile the actual core exporter.
The native cases include both signed/unsigned boundaries and the erased-u64
binder difference. Full repository-wide Lean aggregate/audit and all CI checks
remain integration responsibilities; this record does not claim they ran.
