import Jihoo.NativeTyping

/-! Capture-avoiding algebra for the native Fold/Loop dependent telescopes. -/
namespace Jihoo.NativeKernel

theorem liftRenaming_after_shift (n : Nat) (ρ : Nat → Nat) (x : Nat) :
    liftRenaming n ρ (x + n) = ρ x + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Nat.succ (liftRenaming n ρ (x + n)) = Nat.succ (ρ x + n)
      exact congrArg Nat.succ ih

theorem liftSub_after_shift (n : Nat) (σ : Nat → Term) (x : Nat) :
    liftSub n σ (x + n) = (σ x).rename (fun y => y + n) := by
  induction n with
  | zero => exact (Term.rename_id (σ x)).symm
  | succ n ih =>
      change (liftSub n σ (x + n)).rename Nat.succ = (σ x).rename (fun y => y + (n + 1))
      rw [ih, Term.rename_comp]
      rfl

theorem Term.shift_rename (t : Term) (n : Nat) (ρ : Nat → Nat) :
    (t.rename (fun x => x + n)).rename (liftRenaming n ρ) =
      (t.rename ρ).rename (fun x => x + n) := by
  rw [Term.rename_comp, Term.rename_comp]
  congr 1
  funext x
  exact liftRenaming_after_shift n ρ x

theorem Term.shift_subst (t : Term) (n : Nat) (σ : Nat → Term) :
    (t.rename (fun x => x + n)).subst (liftSub n σ) =
      (t.subst σ).rename (fun x => x + n) := by
  rw [Term.subst_rename, Term.rename_subst]
  congr 1
  funext x
  exact liftSub_after_shift n σ x

theorem foldBodyType_rename (n : Term) (ρ : Nat → Nat) :
    (foldBodyType n).rename ρ = foldBodyType (n.rename ρ) := by
  simp [foldBodyType, Term.rename, renameArgs, Op.binders, liftRenaming,
    Indexed.liftRenaming, Term.rename_comp]

theorem foldBodyType_subst (n : Term) (σ : Nat → Term) :
    (foldBodyType n).subst σ = foldBodyType (n.subst σ) := by
  simp [foldBodyType, Term.subst, substArgs, Op.binders, liftSub, liftSubOne,
    Term.subst_rename, Term.rename_subst]

theorem loopBodyType_rename (n m : Term) (proof : Bool) (ρ : Nat → Nat) :
    (loopBodyType n m proof).rename ρ = loopBodyType (n.rename ρ) (m.rename ρ) proof := by
  simp [loopBodyType, Term.rename, renameArgs, Op.binders, liftRenaming,
    Indexed.liftRenaming, Term.rename_comp]

theorem loopBodyType_subst (n m : Term) (proof : Bool) (σ : Nat → Term) :
    (loopBodyType n m proof).subst σ = loopBodyType (n.subst σ) (m.subst σ) proof := by
  simp [loopBodyType, Term.subst, substArgs, Op.binders, liftSub, liftSubOne,
    Term.subst_rename, Term.rename_subst, Term.rename_comp, Term.rename]

@[simp] theorem loopSortTerm_rename (proof : Bool) (ρ : Nat → Nat) :
    (loopSortTerm proof).rename ρ = loopSortTerm proof := by
  cases proof <;> simp [loopSortTerm, Term.rename, renameArgs]

@[simp] theorem loopSortTerm_subst (proof : Bool) (σ : Nat → Term) :
    (loopSortTerm proof).subst σ = loopSortTerm proof := by
  cases proof <;> simp [loopSortTerm, Term.subst, substArgs]

end Jihoo.NativeKernel
