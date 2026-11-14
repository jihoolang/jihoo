import Jihoo.NativeRootPreservation

/-! Root preservation with genuinely converted function domains, dependent
results and refinement predicates. Every example constructs the original
derivation first and applies the proved preservation theorem. -/
namespace Jihoo.NativeKernel.RootPreservationExamples

private theorem variable0 : HasType [⟨.u64,false⟩] true (.var 0) .u64 :=
  .var (b := ⟨.u64,false⟩) (by simp [lookup,Term.rename,renameArgs]) (Or.inl rfl)

private theorem domain : Binder [] false .u64 (.type 0) := .intro .u64 (by simp [binderAllowed])

private def dependent : Term := .lam false .u64 (.refl (.var 0))
private def alias : Term := .app (.lam false .u64 .u64) (.natural 0)

private theorem domain_conversion : Conversion.Conv .u64 alias := by
  have beta := Conversion.Conv.beta false .u64 .u64 (.natural 0)
  exact .symm (by simpa [alias,Term.subst,substArgs] using beta)

theorem beta_converted_domain :
    HasType [] true (.refl (.natural 7)) (.eq (.natural 7) (.natural 7)) := by
  have original : HasType [] true dependent (.pi false .u64 (.eq (.var 0) (.var 0))) :=
    .lam domain (.refl variable0)
  have converted := original.convert
    (Conversion.Conv.node (.pi false) (.cons domain_conversion (.cons (.refl _) .nil)))
  have argument : HasType [] true (.natural 7) alias := (HasType.natural (by decide)).convert domain_conversion
  have result := converted.ghostBetaContract argument
  simpa [dependent,Term.subst,substArgs,single,Op.binders,liftSub] using result

theorem actual_beta_contraction :
    HasType [] true (.refl (.natural 7)) (.eq (.natural 7) (.natural 7)) := by
  have original : HasType [] true (.app dependent (.natural 7)) (.eq (.natural 7) (.natural 7)) := by
    have app := HasType.app (HasType.lam domain (HasType.refl (ghost := true) variable0))
      (HasType.natural (n := 7) (by decide)) (Or.inl rfl)
    simpa [dependent,Term.subst,substArgs,Op.binders,liftSub] using app
  apply Conversion.contract_ghost_preservation original
  simp [Conversion.contract,Conversion.substitutionSafe,Conversion.treeSize,Conversion.treeDepth,
    dependent,Term.subst,substArgs,single,Op.binders,liftSub]

private def predicate : Term := .lam false .u64 (.eq (.var 0) (.var 0))
private def alternate : Term := .app (.lam false .u64 predicate) (.natural 0)

private theorem predicates_convert : Conversion.Conv predicate alternate := by
  have beta := Conversion.Conv.beta false .u64 predicate (.natural 0)
  exact .symm (by simpa [alternate,predicate,Term.subst,substArgs,single,Op.binders,liftSub,liftSubOne,
    Term.rename,renameArgs] using beta)

theorem proof_projection_converted_predicate :
    HasType [] true (.refl (.natural 7))
      (.app alternate (.witness (.pack predicate (.natural 7) (.refl (.natural 7))))) := by
  have ptyped : HasType [] true predicate (.pi false .u64 .prop) := .lam domain (.eq variable0 variable0)
  have beta := Conversion.Conv.beta false .u64 (.eq (.var 0) (.var 0)) (.natural 7)
  have atSeven : Conversion.Conv (.app predicate (.natural 7)) (.eq (.natural 7) (.natural 7)) := by
    simpa [predicate,Term.subst,substArgs,single,Op.binders,liftSub] using beta
  have number : HasType [] true (.natural 7) .u64 := .natural (by decide)
  have evidence := (HasType.refl (ghost := true) number).convert (.symm atSeven)
  have packed := HasType.pack ptyped number evidence
  have converted := packed.convert (Conversion.Conv.node .refine (.cons predicates_convert .nil))
  have projection := HasType.proof (ghost := true) converted
  exact projection.ghostProofPack

end Jihoo.NativeKernel.RootPreservationExamples
