import Jihoo.NativeSubstitution

/-! Binding algebra for closed native terms, independent of every typing judgment. -/
namespace Jihoo.NativeKernel.Environment

private theorem liftRenaming_agree {depth : Nat} {ρ τ : Nat → Nat}
    (same : ∀ x < depth, ρ x = τ x) (binders : Nat) :
    ∀ x < depth + binders, liftRenaming binders ρ x = liftRenaming binders τ x := by
  induction binders with
  | zero => exact same
  | succ n ih =>
      intro x bound
      cases x with
      | zero => rfl
      | succ x =>
          exact congrArg Nat.succ (ih x (by omega))

private theorem liftSub_agree {depth : Nat} {σ τ : Nat → Term}
    (same : ∀ x < depth, σ x = τ x) (binders : Nat) :
    ∀ x < depth + binders, liftSub binders σ x = liftSub binders τ x := by
  induction binders with
  | zero => exact same
  | succ n ih =>
      intro x bound
      cases x with
      | zero => rfl
      | succ x =>
          exact congrArg (Term.rename Nat.succ) (ih x (by omega))

theorem scoped_rename_congr {term : Term} {depth : Nat} {ρ τ : Nat → Nat} (scope : term.Scoped depth)
    (same : ∀ x < depth, ρ x = τ x) : term.rename ρ = term.rename τ := by
  induction scope generalizing ρ τ with
  | var bound => simp only [Term.rename, same _ bound]
  | @node arguments depth op scopes ih =>
      simp only [Term.rename]
      apply congrArg (Term.node op)
      apply List.ext_getElem?
      intro index
      rw [renameArgs_get, renameArgs_get]
      cases found : arguments[index]? with
      | none => simp only [Option.map_none]
      | some child =>
          simp only [Option.map_some]
          apply congrArg some
          exact ih index child found (by simpa only [Nat.zero_add] using liftRenaming_agree same (op.binders index))

theorem scoped_subst_congr {term : Term} {depth : Nat} {σ τ : Nat → Term} (scope : term.Scoped depth)
    (same : ∀ x < depth, σ x = τ x) : term.subst σ = term.subst τ := by
  induction scope generalizing σ τ with
  | var bound => simp only [Term.subst, same _ bound]
  | @node arguments depth op scopes ih =>
      simp only [Term.subst]
      apply congrArg (Term.node op)
      apply List.ext_getElem?
      intro index
      rw [substArgs_get, substArgs_get]
      cases found : arguments[index]? with
      | none => simp only [Option.map_none]
      | some child =>
          simp only [Option.map_some]
          apply congrArg some
          exact ih index child found (by simpa only [Nat.zero_add] using liftSub_agree same (op.binders index))

theorem closed_rename {term : Term} (scope : term.Scoped 0) (ρ : Nat → Nat) : term.rename ρ = term := by
  exact (scoped_rename_congr scope (ρ := ρ) (τ := id) (by intro x bound; omega)).trans (Term.rename_id term)

theorem closed_subst {term : Term} (scope : term.Scoped 0) (σ : Nat → Term) : term.subst σ = term := by
  exact (scoped_subst_congr scope (σ := σ) (τ := Term.var) (by intro x bound; omega)).trans (Term.subst_id term)

end Jihoo.NativeKernel.Environment
