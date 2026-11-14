import Jihoo.KernelChecker

/-! Acceptance soundness for the concrete, fuel-bounded raw-term checker.
This is a ghost-mode, universe-free subset theorem, not correctness of native
Core.infer, completeness, or a normalization refinement. -/
namespace Jihoo.KernelChecker
open CoreBridge
open CoreBridge.Raw
open GraphCertificates.Typing (context)

/-- Lookup includes the weakening in the existing pre-binder context convention. -/
theorem lookup_sound {ctx : List Raw} {x : Nat} {A : Raw}
    (h : context ctx x = some A) : Beta.HasType (context ctx) (.var x) A :=
  .var h

/-- Joint induction follows the checker's decreasing depth budget. -/
private theorem sound_mutual (fuel : Nat) :
    (∀ ctx term ty, infer fuel ctx term = some ty →
      Beta.HasType (context ctx) term ty) ∧
    (∀ ctx ty, isType fuel ctx ty = true → Beta.IsType (context ctx) ty) := by
  induction fuel with
  | zero =>
      constructor
      · intro ctx term ty h; simp [infer] at h
      · intro ctx ty h; simp [isType] at h
  | succ fuel ih =>
      rcases ih with ⟨hi, ht⟩
      constructor
      · intro ctx term ty h
        cases term <;> simp only [infer] at h
        all_goals first | contradiction | skip
        case var x => exact lookup_sound h
        case natural n =>
          split at h
          · cases h; exact .natural ‹_›
          · contradiction
        case integer n =>
          split at h
          · cases h; exact .integer ‹_ ∧ _›.1 ‹_ ∧ _›.2
          · contradiction
        case uadd a b =>
          split at h
          · rename_i hab
            cases h
            exact .uadd (hi ctx a .u64 hab.1) (hi ctx b .u64 hab.2)
          · contradiction
        case refl a =>
          split at h
          · rename_i ha
            cases h
            exact .refl (hi ctx a .u64 ha)
          · contradiction
        case lam e A body =>
          split at h
          · rename_i hA
            split at h
            · rename_i B hb
              cases h
              exact .lam (ht ctx A hA.2) hA.1 (hi (A :: ctx) body B hb)
            · contradiction
          · contradiction
        case app f a =>
          split at h
          · rename_i e A B hf
            split at h
            · rename_i ha
              cases h
              exact .app (hi ctx f (.pi e A B) hf) (hi ctx a A ha.1)
            · contradiction
          · contradiction
      · intro ctx ty h
        cases ty <;> simp only [isType] at h
        all_goals first | contradiction | skip
        case u64 => exact .u64
        case i64 => exact .i64
        case eq a b =>
          have hab := of_decide_eq_true h
          exact .eq (hi ctx a .u64 hab.1) (hi ctx b .u64 hab.2)
        case pi e A B =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact .pi (ht ctx A h.1.2) h.1.1 (ht (A :: ctx) B h.2)

/-- Every accepted inferred type has a derivation in the existing Beta judgment. -/
theorem infer_sound {fuel : Nat} {ctx : List Raw} {term ty : Raw}
    (h : infer fuel ctx term = some ty) : Beta.HasType (context ctx) term ty :=
  (sound_mutual fuel).1 ctx term ty h

/-- Every accepted formation check has a derivation in the existing Beta judgment. -/
theorem isType_sound {fuel : Nat} {ctx : List Raw} {ty : Raw}
    (h : isType fuel ctx ty = true) : Beta.IsType (context ctx) ty :=
  (sound_mutual fuel).2 ctx ty h

/-- Instantiating an accepted body preserves its inferred dependent type.
The substitution result comes from the existing declarative substitution theorem. -/
theorem infer_instantiate {fuelBody fuelArg : Nat} {ctx : List Raw} {A body B a : Raw}
    (hb : infer fuelBody (A :: ctx) body = some B)
    (ha : infer fuelArg ctx a = some A) :
    Beta.HasType (context ctx) (body.subst (single a)) (B.subst (single a)) :=
  (infer_sound hb).instantiate (infer_sound ha)

end Jihoo.KernelChecker
