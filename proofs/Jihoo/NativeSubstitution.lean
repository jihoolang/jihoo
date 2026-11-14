import Jihoo.NativeSyntax

/-! Simultaneous de Bruijn renaming/substitution algebra over the complete
native constructor vocabulary. Generic child-list proofs follow Op.binders, so
every native constructor, including both evidence-binding branches, is covered. -/
namespace Jihoo.NativeKernel

@[simp] theorem liftRenaming_id (n : Nat) : liftRenaming n id = id := by
  induction n with
  | zero => rfl
  | succ n ih => funext x; cases x <;> simp [liftRenaming, Indexed.liftRenaming, ih]

private theorem liftOne_comp (ρ τ : Nat → Nat) :
    (fun x => Indexed.liftRenaming τ (Indexed.liftRenaming ρ x)) =
      Indexed.liftRenaming (fun x => τ (ρ x)) := by
  funext x; cases x <;> rfl

theorem liftRenaming_comp (n : Nat) (ρ τ : Nat → Nat) :
    (fun x => liftRenaming n τ (liftRenaming n ρ x)) =
      liftRenaming n (fun x => τ (ρ x)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact (liftOne_comp (liftRenaming n ρ) (liftRenaming n τ)).trans
        (congrArg Indexed.liftRenaming ih)

@[simp] theorem Term.rename_id (t : Term) : t.rename id = t := by
  induction t using Term.rec
    (motive_2 := fun xs => ∀ op offset, renameArgs op id offset xs = xs) with
  | var => simp [Term.rename]
  | node op xs ih => simp [Term.rename, ih]
  | nil => simp [renameArgs]
  | cons x xs ihx ihxs => simp [renameArgs, liftRenaming_id, ihx, ihxs]

theorem Term.rename_comp (t : Term) (ρ τ : Nat → Nat) :
    (t.rename ρ).rename τ = t.rename (fun x => τ (ρ x)) := by
  induction t using Term.rec
    (motive_2 := fun xs => ∀ op offset ρ τ,
      renameArgs op τ offset (renameArgs op ρ offset xs) =
        renameArgs op (fun x => τ (ρ x)) offset xs) generalizing ρ τ with
  | var => simp [Term.rename]
  | node op xs ih => simp [Term.rename, ih]
  | nil => simp [renameArgs]
  | cons x xs ihx ihxs => simp [renameArgs, ihx, ihxs, liftRenaming_comp]

@[simp] theorem liftSub_var (n : Nat) : liftSub n Term.var = Term.var := by
  induction n with
  | zero => rfl
  | succ n ih => funext x; cases x <;> simp [liftSub, liftSubOne, Term.rename, ih]

@[simp] theorem Term.subst_id (t : Term) : t.subst Term.var = t := by
  induction t using Term.rec
    (motive_2 := fun xs => ∀ op offset, substArgs op Term.var offset xs = xs) with
  | var => simp [Term.subst]
  | node op xs ih => simp [Term.subst, ih]
  | nil => simp [substArgs]
  | cons x xs ihx ihxs => simp [substArgs, liftSub_var, ihx, ihxs]

theorem liftSub_rename (n : Nat) (ρ : Nat → Nat) (σ : Nat → Term) :
    (fun x => liftSub n σ (liftRenaming n ρ x)) =
      liftSub n (fun x => σ (ρ x)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext x
      cases x with
      | zero => simp [liftSub, liftSubOne, liftRenaming, Indexed.liftRenaming]
      | succ x =>
          simpa only [liftSub, liftSubOne, liftRenaming, Indexed.liftRenaming] using
            congrArg (fun t => t.rename Nat.succ) (congrFun ih x)

theorem Term.subst_rename (t : Term) (ρ : Nat → Nat) (σ : Nat → Term) :
    (t.rename ρ).subst σ = t.subst (fun x => σ (ρ x)) := by
  induction t using Term.rec
    (motive_2 := fun xs => ∀ op offset ρ σ,
      substArgs op σ offset (renameArgs op ρ offset xs) =
        substArgs op (fun x => σ (ρ x)) offset xs) generalizing ρ σ with
  | var => simp [Term.rename, Term.subst]
  | node op xs ih => simp [Term.rename, Term.subst, ih]
  | nil => simp [renameArgs, substArgs]
  | cons x xs ihx ihxs => simp [renameArgs, substArgs, ihx, ihxs, liftSub_rename]

theorem rename_liftSub (n : Nat) (σ : Nat → Term) (ρ : Nat → Nat) :
    (fun x => (liftSub n σ x).rename (liftRenaming n ρ)) =
      liftSub n (fun x => (σ x).rename ρ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext x
      cases x with
      | zero => simp [liftSub, liftSubOne, liftRenaming, Indexed.liftRenaming, Term.rename]
      | succ x =>
          simpa only [liftSub, liftSubOne, liftRenaming, Indexed.liftRenaming,
            Term.rename_comp] using congrArg (fun t => t.rename Nat.succ) (congrFun ih x)

theorem Term.rename_subst (t : Term) (σ : Nat → Term) (ρ : Nat → Nat) :
    (t.subst σ).rename ρ = t.subst (fun x => (σ x).rename ρ) := by
  induction t using Term.rec
    (motive_2 := fun xs => ∀ op offset σ ρ,
      renameArgs op ρ offset (substArgs op σ offset xs) =
        substArgs op (fun x => (σ x).rename ρ) offset xs) generalizing σ ρ with
  | var => simp [Term.subst]
  | node op xs ih => simp [Term.rename, Term.subst, ih]
  | nil => simp [renameArgs, substArgs]
  | cons x xs ihx ihxs => simp [renameArgs, substArgs, ihx, ihxs, rename_liftSub]

theorem liftSub_comp (n : Nat) (σ τ : Nat → Term) :
    (fun x => (liftSub n σ x).subst (liftSub n τ)) =
      liftSub n (fun x => (σ x).subst τ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext x
      cases x with
      | zero => simp [liftSub, liftSubOne, Term.subst]
      | succ x =>
          simp only [liftSub, liftSubOne, Term.subst_rename]
          change (liftSub n σ x).subst (fun y => (liftSub n τ y).rename Nat.succ) = _
          rw [← Term.rename_subst]
          exact congrArg (fun t => t.rename Nat.succ) (congrFun ih x)

theorem Term.subst_comp (t : Term) (σ τ : Nat → Term) :
    (t.subst σ).subst τ = t.subst (fun x => (σ x).subst τ) := by
  induction t using Term.rec
    (motive_2 := fun xs => ∀ op offset σ τ,
      substArgs op τ offset (substArgs op σ offset xs) =
        substArgs op (fun x => (σ x).subst τ) offset xs) generalizing σ τ with
  | var => simp [Term.subst]
  | node op xs ih => simp [Term.subst, ih]
  | nil => simp [substArgs]
  | cons x xs ihx ihxs => simp [substArgs, ihx, ihxs, liftSub_comp]

@[simp] theorem Term.shift_subst_single (t a : Term) :
    (t.rename Nat.succ).subst (single a) = t := by
  simpa only [Term.subst_rename, single] using Term.subst_id t

theorem Term.rename_instantiate (body a : Term) (ρ : Nat → Nat) :
    (body.subst (single a)).rename ρ =
      (body.rename (Indexed.liftRenaming ρ)).subst (single (a.rename ρ)) := by
  rw [Term.rename_subst, Term.subst_rename]
  congr 1
  funext x; cases x <;> simp [single, Term.rename, Indexed.liftRenaming]

theorem Term.subst_instantiate (body a : Term) (σ : Nat → Term) :
    (body.subst (single a)).subst σ =
      (body.subst (liftSubOne σ)).subst (single (a.subst σ)) := by
  rw [Term.subst_comp, Term.subst_comp]
  congr 1
  funext x
  cases x with
  | zero => simp [single, liftSubOne, Term.subst]
  | succ x => simp only [single, liftSubOne, Term.subst, Term.shift_subst_single]

@[simp] theorem renameArgs_length (op : Op) (ρ : Nat → Nat) (offset : Nat) (xs : List Term) :
    (renameArgs op ρ offset xs).length = xs.length := by
  induction xs generalizing offset with
  | nil => simp [renameArgs]
  | cons x xs ih => simp [renameArgs, ih]

@[simp] theorem substArgs_length (op : Op) (σ : Nat → Term) (offset : Nat) (xs : List Term) :
    (substArgs op σ offset xs).length = xs.length := by
  induction xs generalizing offset with
  | nil => simp [substArgs]
  | cons x xs ih => simp [substArgs, ih]

theorem renameArgs_get (op : Op) (ρ : Nat → Nat) (offset : Nat) (xs : List Term) (i : Nat) :
    (renameArgs op ρ offset xs)[i]? =
      xs[i]?.map (Term.rename (liftRenaming (op.binders (offset + i)) ρ)) := by
  induction xs generalizing offset i with
  | nil => simp [renameArgs]
  | cons x xs ih =>
      cases i with
      | zero => simp [renameArgs]
      | succ i => simpa [renameArgs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (offset + 1) i

theorem substArgs_get (op : Op) (σ : Nat → Term) (offset : Nat) (xs : List Term) (i : Nat) :
    (substArgs op σ offset xs)[i]? =
      xs[i]?.map (Term.subst (liftSub (op.binders (offset + i)) σ)) := by
  induction xs generalizing offset i with
  | nil => simp [substArgs]
  | cons x xs ih =>
      cases i with
      | zero => simp [substArgs]
      | succ i => simpa [substArgs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (offset + 1) i

def Within (source target : Nat) (ρ : Nat → Nat) : Prop :=
  ∀ x, x < source → ρ x < target

theorem Within.lift {source target : Nat} {ρ : Nat → Nat}
    (h : Within source target ρ) (binders : Nat) :
    Within (source + binders) (target + binders) (liftRenaming binders ρ) := by
  induction binders with
  | zero => exact h
  | succ n ih =>
      intro x hx
      cases x with
      | zero => simp [liftRenaming, Indexed.liftRenaming]; omega
      | succ x =>
          have lifted := ih x (by omega)
          simp only [liftRenaming, Indexed.liftRenaming]
          omega

theorem Term.Scoped.rename {source target : Nat} {t : Term} {ρ : Nat → Nat}
    (h : t.Scoped source) (hρ : Within source target ρ) : (t.rename ρ).Scoped target := by
  induction h generalizing target ρ with
  | var hx => simpa only [Term.rename] using Term.Scoped.var (hρ _ hx)
  | @node args source op hs ih =>
      rw [Term.rename]
      apply Term.Scoped.node
      intro i u hu
      rw [renameArgs_get] at hu
      obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.mp hu
      subst u
      simpa only [Nat.zero_add] using ih i t ht (hρ.lift (op.binders i))

theorem liftSub_scoped {source target : Nat} {σ : Nat → Term}
    (h : ∀ x, x < source → (σ x).Scoped target) (binders : Nat) :
    ∀ x, x < source + binders → (liftSub binders σ x).Scoped (target + binders) := by
  induction binders with
  | zero => exact h
  | succ n ih =>
      intro x hx
      cases x with
      | zero =>
          simp only [liftSub, liftSubOne]
          exact .var (by omega)
      | succ x =>
          simp only [liftSub, liftSubOne]
          exact (ih x (by omega)).rename (fun _ bound => by omega)

theorem Term.Scoped.subst {source target : Nat} {t : Term} {σ : Nat → Term}
    (h : t.Scoped source) (hσ : ∀ x, x < source → (σ x).Scoped target) :
    (t.subst σ).Scoped target := by
  induction h generalizing target σ with
  | var hx => simpa only [Term.subst] using hσ _ hx
  | @node args source op hs ih =>
      rw [Term.subst]
      apply Term.Scoped.node
      intro i u hu
      rw [substArgs_get] at hu
      obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.mp hu
      subst u
      simpa only [Nat.zero_add] using ih i t ht (liftSub_scoped hσ (op.binders i))

theorem Term.Scoped.instantiate {depth : Nat} {body a : Term}
    (hb : body.Scoped (depth + 1)) (ha : a.Scoped depth) :
    (body.subst (single a)).Scoped depth := by
  apply hb.subst
  intro x hx
  cases x with
  | zero => exact ha
  | succ x => exact .var (by omega)

theorem Term.WellFormed.rename {t : Term} (h : t.WellFormed) (ρ : Nat → Nat) :
    (t.rename ρ).WellFormed := by
  revert h
  induction t using Term.rec
    (motive_2 := fun xs => ∀ op offset ρ, (∀ t ∈ xs, t.WellFormed) →
      ∀ t ∈ renameArgs op ρ offset xs, t.WellFormed) generalizing ρ with
  | var => simp [Term.rename, Term.WellFormed]
  | node op xs ih =>
      intro h
      simp only [Term.WellFormed] at h
      simp only [Term.rename, Term.WellFormed]
      exact ⟨by simpa using h.1,
        ih op 0 ρ h.2⟩
  | nil => simp_all [renameArgs]
  | cons x xs ihx ihxs =>
      rename_i op offset ρ hs y hy
      simp only [renameArgs, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ihx _ (hs x (by simp))
      · exact ihxs op (offset + 1) ρ (fun t ht => hs t (by simp [ht])) y hy

theorem liftSub_wellFormed {σ : Nat → Term} (h : ∀ x, (σ x).WellFormed) (n : Nat) :
    ∀ x, (liftSub n σ x).WellFormed := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro x
      cases x with
      | zero => simp [liftSub, liftSubOne, Term.WellFormed]
      | succ x => exact (ih x).rename Nat.succ

theorem Term.WellFormed.subst {t : Term} {σ : Nat → Term}
    (h : t.WellFormed) (hσ : ∀ x, (σ x).WellFormed) : (t.subst σ).WellFormed := by
  revert h
  induction t using Term.rec
    (motive_2 := fun xs => ∀ op offset σ, (∀ x, (σ x).WellFormed) →
      (∀ t ∈ xs, t.WellFormed) → ∀ t ∈ substArgs op σ offset xs, t.WellFormed)
      generalizing σ with
  | var => intro _; simpa only [Term.subst] using hσ _
  | node op xs ih =>
      intro h
      simp only [Term.WellFormed] at h
      simp only [Term.subst, Term.WellFormed]
      exact ⟨by simpa using h.1,
        ih op 0 σ hσ h.2⟩
  | nil => simp_all [substArgs]
  | cons x xs ihx ihxs =>
      rename_i op offset σ hσ hs y hy
      simp only [substArgs, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ihx (liftSub_wellFormed hσ _) (hs x (by simp))
      · exact ihxs op (offset + 1) σ hσ (fun t ht => hs t (by simp [ht])) y hy

theorem Term.WellFormed.instantiate {body a : Term}
    (hb : body.WellFormed) (ha : a.WellFormed) :
    (body.subst (single a)).WellFormed := by
  apply hb.subst
  intro x
  cases x with
  | zero => exact ha
  | succ x => simp [single, Term.WellFormed]

end Jihoo.NativeKernel
