# Executable kernel API

All functions consume raw syntax or snapshot bytes, without proof inputs.
Import `Jihoo.KernelChecker` for execution and
`Jihoo.KernelCheckerSoundness` for acceptance soundness.

```lean
Jihoo.KernelChecker.infer : Nat → List CoreBridge.Raw → CoreBridge.Raw → Option CoreBridge.Raw
Jihoo.KernelChecker.isType : Nat → List CoreBridge.Raw → CoreBridge.Raw → Bool
Jihoo.KernelChecker.check : Nat → List CoreBridge.Raw → CoreBridge.Raw → CoreBridge.Raw → Bool
Jihoo.KernelConversion.normalize : Nat → CoreBridge.Raw → CoreBridge.Raw
Jihoo.KernelConversion.equal : Nat → CoreBridge.Raw → CoreBridge.Raw → Bool
Jihoo.KernelAdmission.checkSnapshot : Nat → GraphCertificates.Typing.Wire.Snapshot → Bool
Jihoo.KernelAdmission.checkBytes : Nat → ByteArray → Bool
```

The context is exactly `GraphCertificates.Typing.context`: newest annotation
first, stored before its binder, with weakening at lookup. No context
well-formedness assumption is imposed. `check` establishes formation of the
requested type separately; `infer` alone does not do so for arbitrary contexts.

`infer_sound` produces `Raw.Beta.HasType (context ctx) term inferred`.
`isType_sound` produces `Raw.Beta.IsType (context ctx) ty`.
`check_sound` and `check_isType` establish these judgments for the exact
requested type, including conversion. The private mutual proof follows the
checker recursion and uses `KernelConversion.equal_sound` at comparisons.

`KernelNormalization.normalize_steps` proves forward computational reachability
of the exact executable residual. `normalize_preserves_type` retains the
original type; `normalize_preserves_formation` preserves type formation.
`Beta.HasType.unique` in `Jihoo.KernelTypeUniqueness` proves that any second
typing derivation has a convertible result type.

`KernelAdmission.checkBytes_sound` returns an existential snapshot whose
canonical encoding equals the exact input bytes and whose roots have closed
typing and formation derivations. Its consistency and preservation results use
the existing declarative metatheory. Import `Jihoo.KernelAdmission` for these.

All Raw term constructors are supported; type nodes use `isType` because this
universe-free syntax has no type-of-types term. Checker exhaustion rejects;
normalizer exhaustion returns a residual. Neither acceptance completeness nor
native implementation refinement is part of this API. See
[KERNEL_CHECKER_SCOPE.md](KERNEL_CHECKER_SCOPE.md) for rules, trust boundaries,
regression coverage and reproduction commands.
