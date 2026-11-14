import Jihoo.KernelChecker

/-! Acceptance soundness for the concrete, conversion-aware raw-term checker.
All inferred premises are obtained recursively from raw syntax; neither typing
nor conversion evidence is supplied by the caller. -/
namespace Jihoo.KernelChecker
open CoreBridge
open CoreBridge.Raw
open GraphCertificates.Typing (context)

/-- Lookup includes weakening in the existing pre-binder context convention. -/
theorem lookup_sound {ctx : List Raw} {x : Nat} {A : Raw}
    (h : context ctx x = some A) : Beta.HasType (context ctx) (.var x) A :=
  .var h

/-- Successful comparison identifies an actual inferred type and a proved
conversion to the expected type. Inference failure cannot produce this witness. -/
theorem checksType_elim {fuel : Nat} {inferred : Option Raw} {expected : Raw}
    (h : checksType fuel inferred expected = true) :
    ∃ actual, inferred = some actual ∧ Beta.Conv actual expected := by
  cases inferred with
  | none => simp [checksType] at h
  | some actual => exact ⟨actual, rfl, KernelConversion.equal_sound h⟩

/-- Joint induction follows the decreasing checker budget. -/
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
      have hc : ∀ ctx t A, checksType fuel (infer fuel ctx t) A = true →
          Beta.HasType (context ctx) t A := by
        intro ctx t A h
        obtain ⟨B, hb, conv⟩ := checksType_elim h
        exact .convert (hi ctx t B hb) conv
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
            have hab := Bool.and_eq_true_iff.mp hab
            exact .uadd (hc ctx a .u64 hab.1) (hc ctx b .u64 hab.2)
          · contradiction
        case usub a b p =>
          split at h
          · rename_i habp
            cases h
            rcases Bool.and_eq_true_iff.mp habp with ⟨hab, hp⟩
            rcases Bool.and_eq_true_iff.mp hab with ⟨ha, hb⟩
            exact .usub (hc ctx a .u64 ha) (hc ctx b .u64 hb) (hc ctx p _ hp)
          · contradiction
        case elements xs =>
          split at h
          · rename_i hxs
            cases h
            exact .elements (fun x hx => hc ctx x .i64 ((List.all_eq_true.mp hxs.2) x hx)) hxs.1
          · contradiction
        case decide a b =>
          split at h
          · rename_i a' b' ha hb
            split at h
            · rename_i hab
              cases h
              exact .decide hab.1 hab.2.1 hab.2.2
            · contradiction
          · contradiction
        case refl a =>
          split at h
          · rename_i ha
            cases h
            exact .refl (hc ctx a .u64 ha)
          · contradiction
        case zeroLe a =>
          split at h
          · rename_i ha
            cases h
            exact .zeroLe (hc ctx a .u64 ha)
          · contradiction
        case index a i p =>
          split at h
          · rename_i T ha
            split at h
            · rename_i n hn
              split at h
              · rename_i hip
                cases h
                have ha' := (hi ctx a T ha).convert (KernelConversion.normalize_sound fuel T)
                rw [hn] at ha'
                have hip := Bool.and_eq_true_iff.mp hip
                exact .index ha' (hc ctx i .u64 hip.1) (hc ctx p _ hip.2)
              · contradiction
            · contradiction
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
          · rename_i T hf
            split at h
            · rename_i e A B hn
              split at h
              · rename_i ha
                cases h
                have hf' := (hi ctx f T hf).convert (KernelConversion.normalize_sound fuel T)
                rw [hn] at hf'
                exact .app hf' (hc ctx a A (Bool.and_eq_true_iff.mp ha).1)
              · contradiction
            · contradiction
          · contradiction
      · intro ctx ty h
        cases ty <;> simp only [isType] at h
        all_goals first | contradiction | skip
        case u64 => exact .u64
        case i64 => exact .i64
        case array n => exact .array (hc ctx n .u64 h)
        case lt a b =>
          have hab := Bool.and_eq_true_iff.mp h
          exact .lt (hc ctx a .u64 hab.1) (hc ctx b .u64 hab.2)
        case eq a b =>
          have hab := Bool.and_eq_true_iff.mp h
          exact .eq (hc ctx a .u64 hab.1) (hc ctx b .u64 hab.2)
        case pi e A B =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact .pi (ht ctx A h.1.2) h.1.1 (ht (A :: ctx) B h.2)

/-- Every successful inference derives the returned type in the Beta calculus. -/
theorem infer_sound {fuel : Nat} {ctx : List Raw} {term ty : Raw}
    (h : infer fuel ctx term = some ty) : Beta.HasType (context ctx) term ty :=
  (sound_mutual fuel).1 ctx term ty h

/-- Every accepted formation check derives a formed type. -/
theorem isType_sound {fuel : Nat} {ctx : List Raw} {ty : Raw}
    (h : isType fuel ctx ty = true) : Beta.IsType (context ctx) ty :=
  (sound_mutual fuel).2 ctx ty h

/-- Checking derives exactly the caller's requested type, including conversion. -/
theorem check_sound {fuel : Nat} {ctx : List Raw} {term expected : Raw}
    (h : check fuel ctx term expected = true) :
    Beta.HasType (context ctx) term expected := by
  obtain ⟨actual, hi, conv⟩ := checksType_elim (Bool.and_eq_true_iff.mp h).2
  exact .convert (infer_sound hi) conv

/-- Checking also establishes independent formation of the expected type. -/
theorem check_isType {fuel : Nat} {ctx : List Raw} {term expected : Raw}
    (h : check fuel ctx term expected = true) : Beta.IsType (context ctx) expected :=
  isType_sound (Bool.and_eq_true_iff.mp h).1

/-- Instantiating an accepted body preserves its inferred dependent type. -/
theorem infer_instantiate {fuelBody fuelArg : Nat} {ctx : List Raw} {A body B a : Raw}
    (hb : infer fuelBody (A :: ctx) body = some B)
    (ha : infer fuelArg ctx a = some A) :
    Beta.HasType (context ctx) (body.subst (single a)) (B.subst (single a)) :=
  (infer_sound hb).instantiate (infer_sound ha)

end Jihoo.KernelChecker
