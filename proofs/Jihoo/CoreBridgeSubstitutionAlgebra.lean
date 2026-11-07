import Jihoo.CoreBridgeTyping

/-! Capture-avoiding renaming and substitution algebra for unified `Raw` syntax.
Both index and value binders use the same lifted operations. The nested-list
motives prove the corresponding map identities for the children of `elements`.
-/

namespace Jihoo.CoreBridge.Raw
open Indexed (liftRenaming)

private theorem liftRenaming_id : liftRenaming id = id := by
  funext x; cases x <;> rfl

private theorem liftRenaming_comp (ρ τ : Nat → Nat) :
    (fun x => liftRenaming τ (liftRenaming ρ x)) = liftRenaming (fun x => τ (ρ x)) := by
  funext x; cases x <;> rfl

@[simp] theorem rename_id (t : Raw) : t.rename id = t := by
  induction t using Raw.rec (motive_2 := fun xs => xs.map (rename id) = xs) <;>
    simp_all [rename, liftRenaming_id]

theorem rename_comp (t : Raw) (ρ τ : Nat → Nat) :
    (t.rename ρ).rename τ = t.rename (fun x => τ (ρ x)) := by
  induction t using Raw.rec
      (motive_2 := fun xs => ∀ ρ τ,
        (xs.map (rename ρ)).map (rename τ) = xs.map (rename (fun x => τ (ρ x))))
      generalizing ρ τ <;>
    simp_all [rename, List.map_map, Function.comp_def, liftRenaming_comp]

private theorem liftSub_var : liftSub Raw.var = Raw.var := by
  funext x; cases x <;> simp [liftSub, rename]

@[simp] theorem subst_id (t : Raw) : t.subst Raw.var = t := by
  induction t using Raw.rec (motive_2 := fun xs => xs.map (subst Raw.var) = xs) <;>
    simp_all [subst, liftSub_var]

private theorem liftSub_rename (ρ : Nat → Nat) (σ : Nat → Raw) :
    (fun x => liftSub σ (liftRenaming ρ x)) = liftSub (fun x => σ (ρ x)) := by
  funext x; cases x <;> rfl

theorem subst_rename (t : Raw) (ρ : Nat → Nat) (σ : Nat → Raw) :
    (t.rename ρ).subst σ = t.subst (fun x => σ (ρ x)) := by
  induction t using Raw.rec
      (motive_2 := fun xs => ∀ ρ σ,
        (xs.map (rename ρ)).map (subst σ) = xs.map (subst (fun x => σ (ρ x))))
      generalizing ρ σ <;>
    simp_all [rename, subst, List.map_map, Function.comp_def, liftSub_rename]

private theorem rename_liftSub (σ : Nat → Raw) (ρ : Nat → Nat) :
    (fun x => (liftSub σ x).rename (liftRenaming ρ)) =
      liftSub (fun x => (σ x).rename ρ) := by
  funext x
  cases x with
  | zero => simp [liftSub, rename, liftRenaming]
  | succ x => simp only [liftSub, rename_comp]; rfl

theorem rename_subst (t : Raw) (σ : Nat → Raw) (ρ : Nat → Nat) :
    (t.subst σ).rename ρ = t.subst (fun x => (σ x).rename ρ) := by
  induction t using Raw.rec
      (motive_2 := fun xs => ∀ σ ρ,
        (xs.map (subst σ)).map (rename ρ) = xs.map (subst (fun x => (σ x).rename ρ)))
      generalizing σ ρ <;>
    simp_all [rename, subst, List.map_map, Function.comp_def, rename_liftSub]

theorem shift_subst_lift (A : Raw) (σ : Nat → Raw) :
    (A.rename Nat.succ).subst (liftSub σ) = (A.subst σ).rename Nat.succ := by
  simp only [subst_rename, rename_subst, liftSub]

private theorem liftSub_comp (σ τ : Nat → Raw) :
    (fun x => (liftSub σ x).subst (liftSub τ)) = liftSub (fun x => (σ x).subst τ) := by
  funext x
  cases x with
  | zero => simp [liftSub, subst]
  | succ x => exact shift_subst_lift (σ x) τ

theorem subst_comp (t : Raw) (σ τ : Nat → Raw) :
    (t.subst σ).subst τ = t.subst (fun x => (σ x).subst τ) := by
  induction t using Raw.rec
      (motive_2 := fun xs => ∀ σ τ,
        (xs.map (subst σ)).map (subst τ) = xs.map (subst (fun x => (σ x).subst τ)))
      generalizing σ τ <;>
    simp_all [subst, List.map_map, Function.comp_def, liftSub_comp]

theorem subst_shift (A a : Raw) : (A.rename Nat.succ).subst (single a) = A := by
  simpa only [subst_rename, single] using subst_id A

theorem rename_instantiate (B a : Raw) (ρ : Nat → Nat) :
    (B.subst (single a)).rename ρ =
      (B.rename (liftRenaming ρ)).subst (single (a.rename ρ)) := by
  rw [rename_subst, subst_rename]
  congr 1
  funext x; cases x <;> simp [single, rename, liftRenaming]

theorem subst_instantiate (B a : Raw) (σ : Nat → Raw) :
    (B.subst (single a)).subst σ =
      (B.subst (liftSub σ)).subst (single (a.subst σ)) := by
  rw [subst_comp, subst_comp]
  congr 1
  funext x
  cases x with
  | zero => simp [liftSub, subst, single]
  | succ x => simpa only [single, subst, liftSub] using (subst_shift (σ x) (a.subst σ)).symm

@[simp] theorem proposition_rename (t : Raw) (ρ : Nat → Nat) :
    (t.rename ρ).proposition = t.proposition := by
  induction t using Raw.rec (motive_2 := fun _ => True) generalizing ρ <;>
    simp_all [rename, proposition]

end Jihoo.CoreBridge.Raw
