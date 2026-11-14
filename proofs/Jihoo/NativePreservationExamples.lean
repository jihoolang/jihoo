import Jihoo.NativePreservation

/-! Concrete checks for the hard contextual cases: changed binder annotations,
changed dependent arguments, proof operands and independent normalization budgets.
Each theorem keeps its stated original type rather than silently normalizing it. -/
namespace Jihoo.NativeKernel.PreservationExamples

open Conversion (normalize)

private def alias : Term := .app (.lam false .u64 .u64) (.natural 0)
private def addition : Term := .uadd (.natural 1) (.natural 2)
private def dependent : Term := .lam false .u64 (.refl (.var 0))
private def source : Term := .app dependent addition

macro "native_preservation_reduce" : tactic =>
  `(tactic| (simp [normalize, Conversion.children, Conversion.contract,
    Conversion.substitutionSafe, Conversion.treeSize, Conversion.treeDepth,
    alias, addition, dependent, source, Term.subst, substArgs, single,
    liftSub, liftSubOne, Term.rename, renameArgs, liftRenaming,
    Indexed.liftRenaming, Op.binders]))

private theorem domain : Binder [] false .u64 (.type 0) := .intro .u64 (by simp [binderAllowed])

private theorem aliasTyped : HasType [] true alias (.univ 0) := by
  have typed := HasType.app (HasType.lam domain (HasType.u64 (ghost := true)))
    (HasType.natural (n := 0) (by decide)) (Or.inl rfl)
  simpa [alias,Term.subst,substArgs] using typed

private theorem aliasStep : Reduction.Step alias .u64 := by
  have step := Reduction.Step.beta false .u64 .u64 (.natural 0)
  simpa [alias,Term.subst,substArgs] using step

private theorem aliasLambda : HasType [] true (.lam false alias (.var 0))
    (.pi false alias (alias.rename Nat.succ)) := by
  have binder : Binder [] false alias (.type 0) := .intro aliasTyped (by simp [binderAllowed])
  exact .lam binder (.var (b := ⟨alias.rename Nat.succ,false⟩) rfl (Or.inl rfl))

theorem annotation_step_keeps_original_type :
    HasType [] true (.lam false .u64 (.var 0)) (.pi false alias (alias.rename Nat.succ)) := by
  exact aliasLambda.ghostPreservation (Reduction.Step.node (.lam false) [] [.var 0] aliasStep)

theorem annotation_normalization_keeps_original_type :
    HasType [] true (.lam false .u64 (.var 0)) (.pi false alias (alias.rename Nat.succ)) := by
  have computed : normalize 8 (.lam false alias (.var 0)) = .lam false .u64 (.var 0) := by
    native_preservation_reduce
  simpa only [computed] using aliasLambda.ghostNormalize 8

private theorem sourceTyped : HasType [] true source (.eq addition addition) := by
  have variable0 : HasType [⟨.u64,false⟩] true (.var 0) .u64 :=
    .var (b := ⟨.u64,false⟩) (by simp [lookup,Term.rename,renameArgs]) (Or.inl rfl)
  have function := HasType.lam domain (HasType.refl (ghost := true) variable0)
  have argument : HasType [] true addition .u64 :=
    .uadd (.natural (by decide)) (.natural (by decide))
  have typed := HasType.app function argument (Or.inl rfl)
  simpa [source,dependent,Term.subst,substArgs,single,Op.binders,liftSub] using typed

theorem dependent_argument_keeps_original_index :
    HasType [] true (.app dependent (.natural 3)) (.eq addition addition) := by
  exact sourceTyped.ghostPreservation
    (Reduction.Step.node .app [dependent] [] (.add 1 2 (by decide)))

theorem complete_normalization_keeps_original_index :
    HasType [] true (.refl (.natural 3)) (.eq addition addition) := by
  have computed : normalize 8 source = .refl (.natural 3) := by native_preservation_reduce
  simpa only [computed] using sourceTyped.ghostNormalize 8

theorem independent_type_normalization :
    HasType [] true (.refl (.natural 3)) (.eq (.natural 3) (.natural 3)) := by
  have term : normalize 8 source = .refl (.natural 3) := by native_preservation_reduce
  have type : normalize 4 (.eq addition addition) = .eq (.natural 3) (.natural 3) := by
    native_preservation_reduce
  simpa only [term,type] using sourceTyped.ghostNormalizeBoth 8 4

theorem proof_operand_keeps_original_type :
    HasType [] true (.refl (.natural 3)) (.eq addition addition) := by
  have argument : HasType [] true addition .u64 :=
    .uadd (.natural (by decide)) (.natural (by decide))
  exact (HasType.refl (ghost := false) argument).ghostPreservation
    (Reduction.Step.node .refl [] [] (.add 1 2 (by decide)))

theorem erased_binder_normalization_preserves_sort : Binder [] true .u64 (.type 0) := by
  have binder : Binder [] true alias (.type 0) :=
    .intro aliasTyped (Or.inr aliasStep.conversion)
  have computed : normalize 8 alias = .u64 := by native_preservation_reduce
  simpa only [computed] using binder.ghostNormalize 8

end Jihoo.NativeKernel.PreservationExamples
