import Jihoo.NativeConversion

/-! Pointwise conversion transport through simultaneous substitution, including
the independently lifted substitutions at every native binding edge. -/
namespace Jihoo.NativeKernel.Conversion

theorem liftSub_congr {σ τ : Nat → Term} (n : Nat) (h : ∀ x, Conv (σ x) (τ x)) :
    ∀ x, Conv (liftSub n σ x) (liftSub n τ x) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro x
      cases x with
      | zero => exact .refl _
      | succ x => exact (ih x).renaming Nat.succ

theorem Conv.subst_congr (t : Term) {σ τ : Nat → Term} (h : ∀ x, Conv (σ x) (τ x)) :
    Conv (t.subst σ) (t.subst τ) := by
  revert h
  induction t using Term.rec
    (motive_2 := fun xs => ∀ op offset σ τ, (∀ x, Conv (σ x) (τ x)) →
      ListRel Conv (substArgs op σ offset xs) (substArgs op τ offset xs)) generalizing σ τ with
  | var x => intro h; simpa only [Term.subst] using h x
  | node op xs ih => intro h; simpa only [Term.subst] using Conv.node op (ih op 0 σ τ h)
  | nil => simp only [substArgs]; exact .nil
  | cons x xs ihx ihxs =>
      rename_i op offset σ τ h
      simp only [substArgs]
      exact .cons (ihx (liftSub_congr _ h)) (ihxs op (offset+1) σ τ h)

theorem Conv.instantiate_congr {body a b : Term} (h : Conv a b) :
    Conv (body.subst (single a)) (body.subst (single b)) := by
  apply Conv.subst_congr
  intro x
  cases x with
  | zero => exact h
  | succ x => exact .refl _

end Jihoo.NativeKernel.Conversion
