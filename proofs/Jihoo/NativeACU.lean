import Jihoo.NativeConversion

/-! An independent explicit ACU extension of the existing native conversion.
This relation is not installed in the shared typing judgment or executable
checker. Its full confluence and rigid injectivity require separate proofs. -/
namespace Jihoo.NativeKernel.ACU

open Conversion (ListRel)

/-- Existing conversion, plus the three natural-additive-monoid equations.
Literal folding remains the existing bounded, valid-leaf operation. -/
inductive Conv : Term → Term → Prop where
  | legacy : Conversion.Conv a b → Conv a b
  | refl (t : Term) : Conv t t
  | symm : Conv a b → Conv b a
  | trans : Conv a b → Conv b c → Conv a c
  | node (op : Op) : ListRel Conv xs ys → Conv (.node op xs) (.node op ys)
  | assoc (a b c : Term) :
      Conv (.node .uadd [.node .uadd [a,b],c]) (.node .uadd [a,.node .uadd [b,c]])
  | comm (a b : Term) : Conv (.node .uadd [a,b]) (.node .uadd [b,a])
  | zero (a : Term) : Conv (.node .uadd [a,.node (.natural 0) []]) a

theorem Conv.renaming (h : Conv a b) (ρ : Nat → Nat) : Conv (a.rename ρ) (b.rename ρ) := by
  induction h using Conv.rec
    (motive_2 := fun xs ys _ => ∀ op offset ρ,
      ListRel Conv (renameArgs op ρ offset xs) (renameArgs op ρ offset ys)) generalizing ρ with
  | legacy h => exact .legacy (h.renaming ρ)
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih ρ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ ρ) (ih₂ ρ)
  | node op _ ih => simpa only [Term.rename] using Conv.node op (ih op 0 ρ)
  | assoc a b c =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
        Conv.assoc (a.rename ρ) (b.rename ρ) (c.rename ρ)
  | comm a b =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using Conv.comm (a.rename ρ) (b.rename ρ)
  | zero a =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using Conv.zero (a.rename ρ)
  | nil => simp [renameArgs]; exact .nil
  | cons _ _ ihx ihxs =>
      rename_i op offset ρ
      simp only [renameArgs]
      exact .cons (ihx _) (ihxs op (offset+1) ρ)

theorem Conv.substitution (h : Conv a b) (σ : Nat → Term) : Conv (a.subst σ) (b.subst σ) := by
  induction h using Conv.rec
    (motive_2 := fun xs ys _ => ∀ op offset σ,
      ListRel Conv (substArgs op σ offset xs) (substArgs op σ offset ys)) generalizing σ with
  | legacy h => exact .legacy (h.substitution σ)
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih σ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ σ) (ih₂ σ)
  | node op _ ih => simpa only [Term.subst] using Conv.node op (ih op 0 σ)
  | assoc a b c =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using
        Conv.assoc (a.subst σ) (b.subst σ) (c.subst σ)
  | comm a b =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using Conv.comm (a.subst σ) (b.subst σ)
  | zero a =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using Conv.zero (a.subst σ)
  | nil => simp [substArgs]; exact .nil
  | cons _ _ ihx ihxs =>
      rename_i op offset σ
      simp only [substArgs]
      exact .cons (ihx _) (ihxs op (offset+1) σ)

theorem Conv.addCong (ha : Conv a a') (hb : Conv b b') :
    Conv (.node .uadd [a,b]) (.node .uadd [a',b']) :=
  .node .uadd (.cons ha (.cons hb .nil))

theorem Conv.zero_left (a : Term) : Conv (.node .uadd [.node (.natural 0) [],a]) a :=
  (Conv.comm _ _).trans (.zero a)

private theorem lift_related {σ τ : Nat → Term} (h : ∀ x, Conv (σ x) (τ x)) (n : Nat) :
    ∀ x, Conv (liftSub n σ x) (liftSub n τ x) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro x
      cases x with
      | zero => exact .refl _
      | succ x => exact (ih x).renaming Nat.succ

/-- Arbitrary pointwise-related full native substitutions, including replacements
outside the affine fragment. Binding edges use the common capture-safe lift. -/
theorem Conv.subst_congr {σ τ : Nat → Term} (hσ : ∀ x, Conv (σ x) (τ x)) (t : Term) :
    Conv (t.subst σ) (t.subst τ) := by
  induction t using Term.rec
    (motive_2 := fun xs => ∀ op offset σ τ, (∀ x, Conv (σ x) (τ x)) →
      ListRel Conv (substArgs op σ offset xs) (substArgs op τ offset xs)) generalizing σ τ with
  | var x => simp only [Term.subst]; exact hσ x
  | node op xs ih => simpa only [Term.subst] using Conv.node op (ih op 0 σ τ hσ)
  | nil => intros; simp [substArgs]; exact .nil
  | cons x xs ihx ihxs =>
      rename_i op offset σ τ h
      simp only [substArgs]
      exact .cons (ihx (lift_related h (op.binders offset))) (ihxs op (offset+1) σ τ h)

theorem Conv.instantiate_congr (body : Term) (h : Conv a b) :
    Conv (body.subst (single a)) (body.subst (single b)) := by
  apply Conv.subst_congr
  intro x
  cases x with
  | zero => exact h
  | succ n => exact .refl _

end Jihoo.NativeKernel.ACU
