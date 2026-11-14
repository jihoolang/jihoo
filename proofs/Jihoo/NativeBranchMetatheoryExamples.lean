import Jihoo.NativePreservation

/-! Branch evidence capture, context conversion after a control-index step,
and ghost elimination at a substituted type are checked by Lean's kernel. -/
namespace Jihoo.NativeKernel.BranchMetatheoryExamples

private def equality : Term := .eq (.natural 0) (.natural 0)
private def ordering : Term := .lt (.natural 0) (.natural 1)
private def addition : Term := .uadd (.natural 1) (.natural 2)
private def alias : Term := .app (.lam false .u64 .u64) (.natural 0)

theorem equality_evidence_capture : HasType [] true
    (.ifEq (.natural 0) (.natural 0) (.var 0) (.refl (.natural 0))) equality := by
  have old : HasType [⟨equality,true⟩] true (.var 0) equality :=
    .var (b := ⟨equality,true⟩)
      (by simp [lookup,equality,Term.rename,renameArgs,Op.binders,liftRenaming]) (Or.inl rfl)
  have fresh : HasType [⟨equality,true⟩,⟨equality,true⟩] true (.var 0) (equality.rename Nat.succ) :=
    .var (b := ⟨equality.rename Nat.succ,true⟩) rfl (Or.inl rfl)
  have source := HasType.ifEq (HasType.natural (n := 0) (by decide))
    (HasType.natural (n := 0) (by decide)) fresh old
  have evidence : HasType [] true (.refl (.natural 0)) equality := .refl (.natural (by decide))
  have result := source.ghostInstantiate evidence
  simpa [equality,Term.subst,substArgs,single,Op.binders,liftSub,liftSubOne,Term.rename,renameArgs] using result

theorem ordering_evidence_capture : HasType [] true
    (.ifLt (.natural 0) (.natural 1) (.var 0) (.decide (.natural 0) (.natural 1))) ordering := by
  have old : HasType [⟨ordering,true⟩] true (.var 0) ordering :=
    .var (b := ⟨ordering,true⟩)
      (by simp [lookup,ordering,Term.rename,renameArgs,Op.binders,liftRenaming]) (Or.inl rfl)
  have fresh : HasType [⟨ordering,true⟩,⟨ordering,true⟩] true (.var 0) (ordering.rename Nat.succ) :=
    .var (b := ⟨ordering.rename Nat.succ,true⟩) rfl (Or.inl rfl)
  have source := HasType.ifLt (HasType.natural (n := 0) (by decide))
    (HasType.natural (n := 1) (by decide)) fresh old
  have evidence : HasType [] true (.decide (.natural 0) (.natural 1)) ordering :=
    .decide (by decide) (by decide) (by decide)
  have result := source.ghostInstantiate evidence
  simpa [ordering,Term.subst,substArgs,single,Op.binders,liftSub,liftSubOne,Term.rename,renameArgs] using result

theorem changed_control_retains_original_evidence_type :
    HasType [⟨.lt addition (.natural 4),true⟩] true
      (.ifLt (.natural 3) (.natural 4) (.var 0) (.var 0)) (.lt addition (.natural 4)) := by
  have old : HasType [⟨.lt addition (.natural 4),true⟩] true (.var 0) (.lt addition (.natural 4)) :=
    .var (b := ⟨.lt addition (.natural 4),true⟩)
      (by simp [lookup,addition,Term.rename,renameArgs,Op.binders,liftRenaming]) (Or.inl rfl)
  have fresh : HasType [⟨.lt addition (.natural 4),true⟩,⟨.lt addition (.natural 4),true⟩]
      true (.var 0) ((Term.lt addition (.natural 4)).rename Nat.succ) :=
    .var (b := ⟨(Term.lt addition (.natural 4)).rename Nat.succ,true⟩) rfl (Or.inl rfl)
  have left : HasType [⟨.lt addition (.natural 4),true⟩] true addition .u64 :=
    .uadd (.natural (by decide)) (.natural (by decide))
  have source := HasType.ifLt left (HasType.natural (n := 4) (by decide)) fresh old
  exact source.ghostPreservation
    (Reduction.Step.node .ifLt [] [.natural 4,.var 0,.var 0] (.add 1 2 (by decide)))

private theorem aliasTyped (ctx : Context) : HasType ctx true alias (.univ 0) := by
  have domain : Binder ctx false .u64 (.type 0) := .intro .u64 (by simp [binderAllowed])
  have source := HasType.app (HasType.lam domain (HasType.u64 (ghost := true)))
    (HasType.natural (n := 0) (by decide)) (Or.inl rfl)
  simpa [alias,Term.subst,substArgs] using source

theorem absurd_annotation_keeps_original_type :
    HasType [⟨.lt (.natural 0) (.natural 0),true⟩] true (.absurd .u64 (.var 0)) alias := by
  have contradiction : HasType [⟨.lt (.natural 0) (.natural 0),true⟩] true (.var 0)
      (.lt (.natural 0) (.natural 0)) :=
    .var (b := ⟨.lt (.natural 0) (.natural 0),true⟩)
      (by simp [lookup,Term.rename,renameArgs,Op.binders,liftRenaming]) (Or.inl rfl)
  have source := HasType.absurd (s := .type 0) (aliasTyped _) contradiction (Or.inl rfl)
  have beta : Reduction.Step alias .u64 := by
    simpa [alias,Term.subst,substArgs] using Reduction.Step.beta false .u64 .u64 (.natural 0)
  exact source.ghostPreservation (Reduction.Step.node .absurd [] [.var 0] beta)

theorem ghost_absurd_substitutes_function_type :
    HasType [⟨.lt (.natural 0) (.natural 0),true⟩] true
      (.absurd (.pi false .u64 .u64) (.var 0)) (.pi false .u64 .u64) := by
  have typeVar : HasType [⟨.univ 0,false⟩,⟨.lt (.natural 0) (.natural 0),true⟩]
      true (.var 0) (.univ 0) :=
    .var (b := ⟨.univ 0,false⟩) (by simp [lookup,Term.rename,renameArgs]) (Or.inl rfl)
  have contradiction : HasType [⟨.univ 0,false⟩,⟨.lt (.natural 0) (.natural 0),true⟩]
      true (.var 1) (.lt (.natural 0) (.natural 0)) :=
    .var (b := ⟨.lt (.natural 0) (.natural 0),true⟩)
      (by simp [lookup,Term.rename,renameArgs,Op.binders,liftRenaming]) (Or.inl rfl)
  have source := HasType.absurd (s := .type 0) typeVar contradiction (Or.inl rfl)
  have functionType : HasType [⟨.lt (.natural 0) (.natural 0),true⟩] true (.pi false .u64 .u64) (.univ 0) :=
    .pi (s := .type 0) (r := .type 0) (.intro .u64 (by simp [binderAllowed])) .u64
  have result := source.ghostInstantiate functionType
  simpa [Term.subst,substArgs,single,Op.binders,liftSub] using result

end Jihoo.NativeKernel.BranchMetatheoryExamples
