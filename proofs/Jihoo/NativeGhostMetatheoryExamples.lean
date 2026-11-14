import Jihoo.NativeGhostMetatheory

/-! Dependent-result, universe-polymorphic and capture-avoidance applications
of proved typed substitution. Premises are independent declarative derivations;
none assumes typing of the substituted result. -/
namespace Jihoo.NativeKernel.GhostExamples

private theorem seven : HasType [] true (.natural 7) .u64 := .natural (by decide)

private theorem indexVar : HasType [⟨.u64,false⟩] true (.var 0) .u64 :=
  .var (b := ⟨.u64,false⟩) (by simp [lookup,Term.rename,renameArgs]) (Or.inl rfl)

theorem dependent_result : HasType [] true (.refl (.natural 7)) (.eq (.natural 7) (.natural 7)) := by
  have inst := (HasType.refl (ghost := true) indexVar).ghostInstantiate seven
  simpa [Term.subst,substArgs,single,Op.binders,liftSub] using inst

theorem substitute_type_argument : HasType [] true (.lam false .u64 (.var 0)) (.pi false .u64 .u64) := by
  have typeVar : HasType [⟨.univ 0,false⟩] true (.var 0) (.univ 0) :=
    .var (b := ⟨.univ 0,false⟩) (by simp [lookup,Term.rename,renameArgs]) (Or.inl rfl)
  have domain : Binder [⟨.univ 0,false⟩] false (.var 0) (.type 0) :=
    .intro typeVar (by simp [binderAllowed])
  have valueVar : HasType [⟨.var 0,false⟩,⟨.univ 0,false⟩] true (.var 0) (.var 1) :=
    .var (b := ⟨.var 1,false⟩) (by simp [lookup,Term.rename]) (Or.inl rfl)
  have poly := HasType.lam domain valueVar
  have inst := poly.ghostInstantiate (HasType.u64 (ctx := []) (ghost := true))
  simpa [Term.subst,substArgs,single,Op.binders,liftSub,liftSubOne,Term.rename,renameArgs] using inst

theorem erased_proof_argument : HasType [] true (.refl (.natural 7)) (.eq (.natural 7) (.natural 7)) := by
  have evidence : HasType [⟨.eq (.natural 7) (.natural 7),true⟩] true (.var 0)
      (.eq (.natural 7) (.natural 7)) :=
    .var (b := ⟨.eq (.natural 7) (.natural 7),true⟩)
      (by simp [lookup,Term.rename,renameArgs,Op.binders,liftRenaming]) (Or.inl rfl)
  have inst := evidence.ghostInstantiate (HasType.refl seven)
  simpa [Term.subst,substArgs,single,Op.binders,liftSub] using inst

theorem code_derivation_to_ghost_result : HasType [] true (.natural 7) .u64 := by
  have code : HasType [⟨.u64,true⟩] false (.natural 7) .u64 := .natural (by decide)
  have inst := code.ghostInstantiate seven
  simpa [Term.subst,substArgs] using inst

theorem capture_avoiding_typed_result :
    HasType [⟨.u64,false⟩] true (.lam false .u64 (.refl (.var 1)))
      (.pi false .u64 (.eq (.var 1) (.var 1))) := by
  have domain : Binder [⟨.u64,false⟩,⟨.u64,false⟩] false .u64 (.type 0) :=
    .intro .u64 (by simp [binderAllowed])
  have valueParam : HasType [⟨.u64,false⟩,⟨.u64,false⟩,⟨.u64,false⟩] true (.var 1) .u64 :=
    .var (b := ⟨.u64,false⟩) (by simp [lookup,Term.rename,renameArgs]) (Or.inl rfl)
  have inst := (HasType.lam domain (HasType.refl (ghost := true) valueParam)).ghostInstantiate indexVar
  simpa [Term.subst,substArgs,single,Op.binders,liftSub,liftSubOne,Term.rename,renameArgs] using inst

end Jihoo.NativeKernel.GhostExamples
