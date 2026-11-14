import Jihoo.NativeEnvironmentTyping

/-! The ownership and representation side conditions of Back/Give/Take are
stable under full binding-aware renaming and substitution. Ghost policies keep
arbitrary typed motive computations available to the ghost typing metatheory. -/
namespace Jihoo.NativeKernel.Environment

theorem Owned.renaming (h : Owned env T) (ρ : Nat → Nat) (closed : Conversion.Closed env) : Owned env (T.rename ρ) := by
  cases h with
  | buffer converted =>
      exact .buffer (by simpa only [rename_buffer] using converted.renaming ρ closed)
  | family found boxed converted =>
      exact .family found boxed (by simpa only [Term.rename] using converted.renaming ρ closed)

theorem Owned.substitution (h : Owned env T) (σ : Nat → Term) (closed : Conversion.Closed env) : Owned env (T.subst σ) := by
  cases h with
  | buffer converted =>
      exact .buffer (by simpa only [subst_buffer] using converted.substitution σ closed)
  | family found boxed converted =>
      exact .family found boxed (by simpa only [Term.subst] using converted.substitution σ closed)

theorem fixedRepresentation_rename (env : Environment) (t : Term) (ρ : Nat → Nat) :
    fixedRepresentation env (t.rename ρ) = fixedRepresentation env t := by
  cases t with
  | var => simp [Term.rename, fixedRepresentation]
  | node op args =>
      cases op <;> cases args with
      | nil => simp [Term.rename, renameArgs, fixedRepresentation]
      | cons a args =>
          cases args with
          | nil => simp [Term.rename, renameArgs, fixedRepresentation]
          | cons b args => cases args <;> simp [Term.rename, renameArgs, fixedRepresentation]

theorem fixedRepresentation_substitution (h : fixedRepresentation env t = true) (σ : Nat → Term) :
    fixedRepresentation env (t.subst σ) = true := by
  cases t with
  | var => simp [fixedRepresentation] at h
  | node op args =>
      cases op <;> cases args with
      | nil => simp_all [Term.subst, substArgs, fixedRepresentation]
      | cons a args =>
          cases args with
          | nil => simp_all [Term.subst, substArgs, fixedRepresentation]
          | cons b args => cases args <;> simp_all [Term.subst, substArgs, fixedRepresentation]

theorem BackRepresentation.renaming (h : BackRepresentation env ghost erased motive) (ρ : Nat → Nat) (closed : Conversion.Closed env) :
    BackRepresentation env ghost erased (motive.rename ρ) := by
  rcases h with ghost | erased | ⟨flag, domain, body, converted, fixed⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl erased)
  · exact Or.inr (Or.inr ⟨flag, domain.rename ρ, body.rename (liftRenaming 1 ρ),
      by simpa only [Term.rename, renameArgs, Op.binders, liftRenaming] using converted.renaming ρ closed,
      by simpa only [fixedRepresentation_rename] using fixed⟩)

theorem BackRepresentation.substitution (h : BackRepresentation env ghost erased motive) (σ : Nat → Term) (closed : Conversion.Closed env) :
    BackRepresentation env ghost erased (motive.subst σ) := by
  rcases h with ghost | erased | ⟨flag, domain, body, converted, fixed⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl erased)
  · exact Or.inr (Or.inr ⟨flag, domain.subst σ, body.subst (liftSub 1 σ),
      by simpa only [Term.subst, substArgs, Op.binders, liftSub] using converted.substitution σ closed,
      fixedRepresentation_substitution fixed _⟩)

theorem ghost_backRepresentation (env : Environment) (erased : Bool) (motive : Term) :
    BackRepresentation env true erased motive := Or.inl rfl

end Jihoo.NativeKernel.Environment
