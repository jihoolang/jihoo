# Worker A checker contract

Frozen implementation API: `Jihoo.KernelChecker.infer : Nat → List CoreBridge.Raw → CoreBridge.Raw → Option CoreBridge.Raw` and `Jihoo.KernelChecker.isType : Nat → List CoreBridge.Raw → CoreBridge.Raw → Bool`.

Import `Jihoo.KernelChecker`. Context semantics are exactly `Jihoo.GraphCertificates.Typing.context`: newest first, annotations in pre-binder scope, weakening at lookup. No context well-formedness assumption is imposed (matching the existing declarative variable rule).

Both functions recurse mutually on fuel. Zero rejects. Every recursive call in a successor equation uses predecessor fuel. Definitions are public and unfold with `simp only [infer, isType]`; public simp lemmas `infer_zero` and `isType_zero` expose exhaustion.

Inference supports var, bounded natural/integer literals, UAdd, Refl, Lam, App. Formation supports U64/I64, Eq (U64 operands), Pi. All other constructors explicitly fall through to rejection. Lam/Pi require `e = A.proposition`. Lam forms its domain and infers its body under `A :: ctx`. App requires a syntactic Pi, structural argument-type equality, and the existing `substitutionSafe` guard, then returns `B.subst (single a)`. No normalization, conversion search, universe, runtime ownership, or derivation certificate input.

`Jihoo.KernelCheckerSoundness` proves the following targets against this exact implementation:

```
infer_sound : infer fuel ctx term = some ty →
  CoreBridge.Raw.Beta.HasType (GraphCertificates.Typing.context ctx) term ty
isType_sound : isType fuel ctx ty = true →
  CoreBridge.Raw.Beta.IsType (GraphCertificates.Typing.context ctx) ty
```

The proof establishes these together by induction on fuel. The imported certificate module supplies only the existing context, decidable structural equality, and substitution resource guard; this checker never calls certificate replay. No scaffolding, parameterized soundness assumption, axiom, sorry, or unsafe proof is introduced. Fuel is a recursion-depth budget, not a total resource/complexity bound. Acceptance completeness and native Core.infer equivalence are not claimed. The aggregate imports, axiom audit and native regression CI wiring are described in `KERNEL_CHECKER_SCOPE.md`.

Worker A validation: `lake build Jihoo.KernelChecker --wfail` passed on the required Lean 4.34.1 (17 jobs). Sixteen temporary kernel-checked smoke assertions passed for dependent inference/formation, application substitution, bounds, wrong flags/types, unsupported syntax, structural-only comparison, and exhaustion. The temporary file uses a shared simplification list with unused-simp-argument lint disabled locally; no repository lint settings were changed. `#print axioms` on both zero-fuel helpers reports only `propext` and `Quot.sound`. The full aggregate audit/native suites remain integration/C responsibilities.
