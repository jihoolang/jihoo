import Jihoo.NativeEnvironmentContextConversion

/-! Ghost metatheory regressions use recomputed checked histories, including
closed globals and a proposition motive which captures a substituted index. -/
namespace Jihoo.NativeKernel.Environment.GhostExamples

private def scalarDeclaration : GlobalDeclaration := ⟨.i64, .integer 3⟩
private def scalarEnv : Environment := ⟨#[scalarDeclaration], #[]⟩
private theorem scalarWellFormed : UnifiedProgram.EnvWellFormed scalarEnv :=
  UnifiedProgram.checkProgram_wellFormed
    (by cbv : UnifiedProgram.checkProgram 24 24 [scalarDeclaration] [] = some scalarEnv)

theorem closed_global_weakened : HasType scalarEnv [⟨.u64, true⟩] true (.node (.global 0) []) .i64 := by
  have source : HasType scalarEnv [] false (.node (.global 0) []) .i64 := by
    simpa only [scalarDeclaration, Term.rename, renameArgs] using
      (HasType.global (env := scalarEnv) (ctx := []) (ghost := false) (g := 0)
        (declaration := scalarDeclaration) rfl)
  simpa only [Term.rename, renameArgs] using source.ghostWeaken scalarWellFormed .u64 true

private def indexedDeclaration : FamilyDeclaration :=
  ⟨true, 1, 1, [.pi true .u64 (.node (.ind 0 1) [.var 0])], 0⟩
private def indexedEnv : Environment :=
  ⟨#[], #[⟨indexedDeclaration, [⟨[⟨true, .u64, none⟩], [.var 0]⟩], false⟩]⟩
private theorem indexedWellFormed : UnifiedProgram.EnvWellFormed indexedEnv :=
  UnifiedProgram.checkProgram_wellFormed
    (by cbv : UnifiedProgram.checkProgram 24 24 [] [indexedDeclaration] = some indexedEnv)

theorem dependent_constructor_instantiated : HasType indexedEnv [] true
    (.node (.con 0 0 1) [.natural 7]) (.node (.ind 0 1) [.natural 7]) := by
  have source : HasType indexedEnv [⟨.u64, true⟩] false
      (.node (.con 0 0 1) [.var 0]) (.node (.ind 0 1) [.var 0]) :=
    Checker.infer_sound (fuel := 24) (by cbv)
  have argument : HasType indexedEnv [] true (.natural 7) .u64 := .natural (by decide)
  simpa only [Term.subst, substArgs, Op.binders, liftSub, NativeKernel.single] using
    source.ghostInstantiate indexedWellFormed argument

private def propositionDeclaration : FamilyDeclaration :=
  ⟨false, 0, 1, [.pi false .u64 (.node (.ind 0 1) [.var 0])], 0⟩
private def propositionEnv : Environment :=
  ⟨#[], #[⟨propositionDeclaration, [⟨[⟨false, .u64, none⟩], [.var 0]⟩], false⟩]⟩
private theorem propositionWellFormed : UnifiedProgram.EnvWellFormed propositionEnv :=
  UnifiedProgram.checkProgram_wellFormed
    (by cbv : UnifiedProgram.checkProgram 24 24 [] [propositionDeclaration] = some propositionEnv)
private def motive : Term := .lam false .u64 (.eq (.var 1) (.var 1))
private def branch : Term := .lam false .u64 (.refl (.var 1))
private def inductionTerm : Term :=
  .node (.elim 0 1) [motive, branch, .node (.con 0 0 1) [.natural 2]]

theorem captured_proposition_motive_instantiated : HasType propositionEnv [] true
    (inductionTerm.subst (single (.natural 7))) (.eq (.natural 7) (.natural 7)) := by
  have source : HasType propositionEnv [⟨.u64, false⟩] true inductionTerm (.eq (.var 0) (.var 0)) :=
    Checker.check_sound (by cbv : Checker.check 32 propositionEnv [⟨.u64, false⟩] true inductionTerm
      (.eq (.var 0) (.var 0)) = true)
  have argument : HasType propositionEnv [] true (.natural 7) .u64 := .natural (by decide)
  simpa only [Term.subst, substArgs, Op.binders, liftSub, NativeKernel.single] using
    source.ghostInstantiate propositionWellFormed argument

private def aliasDeclaration : GlobalDeclaration := ⟨.univ 0,.u64⟩
private def aliasEnv : Environment := ⟨#[aliasDeclaration],#[]⟩
private def aliasTerm : Term := .node (.global 0) []
private theorem aliasWellFormed : UnifiedProgram.EnvWellFormed aliasEnv :=
  UnifiedProgram.checkProgram_wellFormed
    (by cbv : UnifiedProgram.checkProgram 24 24 [aliasDeclaration] [] = some aliasEnv)
private theorem aliasDelta : Conversion.Conv aliasEnv aliasTerm .u64 :=
  .delta (index := 0) (declaration := aliasDeclaration) rfl

/-- A real delta conversion in the body is transported through simultaneous
substitution using the authenticated closed-global invariant. -/
theorem delta_body_conversion_instantiated : HasType aliasEnv [] true (.natural 7) .u64 := by
  have lookupTyped : HasType aliasEnv [⟨aliasTerm,false⟩] false (.var 0) aliasTerm := by
    simpa only [aliasTerm,Term.rename,renameArgs] using
      (HasType.var (env := aliasEnv) (ctx := [⟨aliasTerm,false⟩]) (x := 0) rfl (Or.inr rfl))
  have converted := lookupTyped.convert aliasDelta
  have argument : HasType aliasEnv [] true (.natural 7) aliasTerm :=
    (HasType.natural (by decide)).convert (.symm aliasDelta)
  simpa only [Term.subst,substArgs,NativeKernel.single] using converted.ghostInstantiate aliasWellFormed argument

/-- Context conversion renames the actual delta equation under a binder. -/
theorem delta_context_annotation_converted : HasType aliasEnv [⟨aliasTerm,false⟩] true (.var 0) .u64 := by
  have source : HasType aliasEnv [⟨.u64,false⟩] true (.var 0) .u64 := by
    simpa only [Term.rename,renameArgs] using
      (HasType.var (env := aliasEnv) (ctx := [⟨.u64,false⟩]) (x := 0) rfl (Or.inl rfl))
  have related := Ghost.ContextConversion.extend (Ghost.ContextConversion.refl aliasEnv [])
    (.symm aliasDelta) false aliasWellFormed.closed
  exact source.ghostContext aliasWellFormed related

end Jihoo.NativeKernel.Environment.GhostExamples
