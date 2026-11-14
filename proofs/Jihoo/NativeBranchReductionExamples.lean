import Jihoo.NativePreservation

/-! All four literal branch choices preserve independently derived types.
True cases instantiate erased evidence; the nested example checks capture
avoidance beneath a returned lambda with a live outer variable. -/
namespace Jihoo.NativeKernel.BranchReductionExamples

open Conversion (normalize)

macro "native_branch_reduce" : tactic =>
  `(tactic| (simp [normalize,Conversion.children,Conversion.contract,
    Conversion.substitutionSafe,Conversion.treeSize,Conversion.treeDepth,
    Term.subst,substArgs,single,liftSub,liftSubOne,Term.rename,renameArgs,
    liftRenaming,Indexed.liftRenaming,Op.binders]))

private theorem evidenceVar (P : Term) (ctx : Context) :
    HasType (⟨P,true⟩ :: ctx) true (.var 0) (P.rename Nat.succ) :=
  .var (b := ⟨P.rename Nat.succ,true⟩) rfl (Or.inl rfl)

theorem lt_true_instantiates_evidence :
    HasType [] true (.decide (.natural 0) (.natural 1)) (.lt (.natural 0) (.natural 1)) := by
  have no : HasType [] true (.decide (.natural 0) (.natural 1)) (.lt (.natural 0) (.natural 1)) :=
    .decide (by decide) (by decide) (by decide)
  have source := HasType.ifLt (HasType.natural (n := 0) (by decide))
    (HasType.natural (n := 1) (by decide)) (evidenceVar _ []) no
  have computed : normalize 8 (.ifLt (.natural 0) (.natural 1) (.var 0)
      (.decide (.natural 0) (.natural 1))) = .decide (.natural 0) (.natural 1) := by
    native_branch_reduce
  simpa only [computed] using source.ghostNormalize 8

theorem eq_true_instantiates_evidence : HasType [] true (.refl (.natural 7)) (.eq (.natural 7) (.natural 7)) := by
  have no : HasType [] true (.refl (.natural 7)) (.eq (.natural 7) (.natural 7)) :=
    .refl (.natural (by decide))
  have source := HasType.ifEq (HasType.natural (n := 7) (by decide))
    (HasType.natural (n := 7) (by decide)) (evidenceVar _ []) no
  have computed : normalize 8 (.ifEq (.natural 7) (.natural 7) (.var 0) (.refl (.natural 7))) =
      .refl (.natural 7) := by native_branch_reduce
  simpa only [computed] using source.ghostNormalize 8

theorem lt_false_selects_no : HasType [] true (.natural 9) .u64 := by
  have no : HasType [] true (.natural 9) .u64 := .natural (by decide)
  have yes : HasType [⟨.lt (.natural 1) (.natural 0),true⟩] true (.natural 7)
      (Term.u64.rename Nat.succ) := by
    simpa [Term.rename,renameArgs] using
      (HasType.natural (ctx := [⟨.lt (.natural 1) (.natural 0),true⟩]) (ghost := true) (n := 7) (by decide))
  have source := HasType.ifLt (HasType.natural (n := 1) (by decide))
    (HasType.natural (n := 0) (by decide)) yes no
  have computed : normalize 8 (.ifLt (.natural 1) (.natural 0) (.natural 7) (.natural 9)) = .natural 9 := by
    native_branch_reduce
  simpa only [computed] using source.ghostNormalize 8

theorem eq_false_selects_no : HasType [] true (.natural 9) .u64 := by
  have no : HasType [] true (.natural 9) .u64 := .natural (by decide)
  have yes : HasType [⟨.eq (.natural 0) (.natural 1),true⟩] true (.natural 7)
      (Term.u64.rename Nat.succ) := by
    simpa [Term.rename,renameArgs] using
      (HasType.natural (ctx := [⟨.eq (.natural 0) (.natural 1),true⟩]) (ghost := true) (n := 7) (by decide))
  have source := HasType.ifEq (HasType.natural (n := 0) (by decide))
    (HasType.natural (n := 1) (by decide)) yes no
  have computed : normalize 8 (.ifEq (.natural 0) (.natural 1) (.natural 7) (.natural 9)) = .natural 9 := by
    native_branch_reduce
  simpa only [computed] using source.ghostNormalize 8

private theorem domain (ctx : Context) : Binder ctx false .u64 (.type 0) :=
  .intro .u64 (by simp [binderAllowed])

theorem live_outer_value_survives_true_binder_removal :
    HasType [⟨.u64,false⟩] true (.lam false .u64 (.refl (.var 1)))
      (.pi false .u64 (.eq (.var 1) (.var 1))) := by
  have oldVar : HasType [⟨.u64,false⟩,⟨.u64,false⟩] true (.var 1) .u64 :=
    .var (b := ⟨.u64,false⟩) (by simp [lookup,Term.rename,renameArgs]) (Or.inl rfl)
  have newVar : HasType [⟨.u64,false⟩,⟨.eq (.natural 0) (.natural 0),true⟩,⟨.u64,false⟩]
      true (.var 2) .u64 :=
    .var (b := ⟨.u64,false⟩) (by simp [lookup,Term.rename,renameArgs]) (Or.inl rfl)
  have no := HasType.lam (domain [⟨.u64,false⟩]) (HasType.refl (ghost := true) oldVar)
  have yes : HasType [⟨.eq (.natural 0) (.natural 0),true⟩,⟨.u64,false⟩] true
      (.lam false .u64 (.refl (.var 2)))
      ((Term.pi false .u64 (.eq (.var 1) (.var 1))).rename Nat.succ) := by
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming,Indexed.liftRenaming] using
      HasType.lam (domain [⟨.eq (.natural 0) (.natural 0),true⟩,⟨.u64,false⟩])
        (HasType.refl (ghost := true) newVar)
  have source := HasType.ifEq (HasType.natural (n := 0) (by decide))
    (HasType.natural (n := 0) (by decide)) yes no
  have computed : normalize 12 (.ifEq (.natural 0) (.natural 0)
      (.lam false .u64 (.refl (.var 2))) (.lam false .u64 (.refl (.var 1)))) =
      .lam false .u64 (.refl (.var 1)) := by native_branch_reduce
  simpa only [computed] using source.ghostNormalize 12

theorem unsigned_boundary_evidence :
    HasType [] true (.decide (.natural (2^64-2)) (.natural (2^64-1)))
      (.lt (.natural (2^64-2)) (.natural (2^64-1))) := by
  have no : HasType [] true (.decide (.natural (2^64-2)) (.natural (2^64-1)))
      (.lt (.natural (2^64-2)) (.natural (2^64-1))) := .decide (by decide) (by decide) (by decide)
  have source := HasType.ifLt (HasType.natural (n := 2^64-2) (by decide))
    (HasType.natural (n := 2^64-1) (by decide)) (evidenceVar _ []) no
  have computed : normalize 8 (.ifLt (.natural (2^64-2)) (.natural (2^64-1)) (.var 0)
      (.decide (.natural (2^64-2)) (.natural (2^64-1)))) =
      .decide (.natural (2^64-2)) (.natural (2^64-1)) := by native_branch_reduce
  simpa only [computed] using source.ghostNormalize 8

theorem invalid_literal_condition_untypable {Γ : Context} {mode : Bool} {yes no T : Term} :
    ¬ HasType Γ mode (.ifLt (.natural (2^64)) (.natural 0) yes no) T := by
  intro h
  obtain ⟨B,ha,hb,hy,hn,hconv⟩ := h.ifLtView
  exact Nat.lt_irrefl _ ha.naturalView.1

private def addition : Term := .uadd (.natural 1) (.natural 2)
private def predicate : Term := .lam false .u64 (.eq (.var 0) (.var 0))

private theorem transportSource : HasType [] true
    (.transport predicate (.refl (.natural 3)) (.refl addition)) (.app predicate (.natural 3)) := by
  have variable0 : HasType [⟨.u64,false⟩] true (.var 0) .u64 :=
    .var (b := ⟨.u64,false⟩) (by simp [lookup,Term.rename,renameArgs]) (Or.inl rfl)
  have pred : HasType [] true predicate (.pi false .u64 .prop) :=
    .lam (domain []) (.eq variable0 variable0)
  have number : HasType [] true addition .u64 := .uadd (.natural (by decide)) (.natural (by decide))
  have atAddition : Conversion.Conv (.app predicate addition) (.eq addition addition) := by
    simpa [predicate,Term.subst,substArgs,single,Op.binders,liftSub] using
      Conversion.Conv.beta false .u64 (.eq (.var 0) (.var 0)) addition
  have equality : HasType [] true (.refl (.natural 3)) (.eq addition (.natural 3)) :=
    (HasType.refl (ghost := true) (HasType.natural (by decide))).convert
      (.node .eq (.cons (.symm (.add 1 2 (by decide))) (.cons (.refl _) .nil)))
  have input := (HasType.refl (ghost := true) number).convert (.symm atAddition)
  exact .transport pred equality input

theorem transport_refl_retains_converted_indices :
    HasType [] true (.refl addition) (.app predicate (.natural 3)) := by
  apply Conversion.contract_ghost_preservation transportSource
  simp [Conversion.contract]

theorem transport_normalization_retains_predicate_application :
    HasType [] true (.refl (.natural 3)) (.app predicate (.natural 3)) := by
  have computed : normalize 10 (.transport predicate (.refl (.natural 3)) (.refl addition)) =
      .refl (.natural 3) := by
    simp only [predicate,addition]
    native_branch_reduce
  simpa only [computed] using transportSource.ghostNormalize 10

end Jihoo.NativeKernel.BranchReductionExamples
