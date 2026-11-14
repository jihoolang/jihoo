import Jihoo.NativeEnvironmentContextualPreservation

/-! Original-type regressions cover dependent binders, constructor indices,
continuation syntax, and the exact bounded normalizer. -/
namespace Jihoo.NativeKernel.Environment.ContextualExamples

private theorem emptyHistory : UnifiedProgram.UnifiedProgramChecked [] [] empty := .empty

private abbrev two : Term := .uadd (.natural 1) (.natural 1)
private theorem emptyWellFormed : UnifiedProgram.EnvWellFormed empty :=
  UnifiedProgram.checkProgram_wellFormed
    (by cbv : UnifiedProgram.checkProgram 24 24 [] [] = some empty)

/-- An annotation contracts while the lambda retains its original Pi type. -/
theorem dependent_binder_original_type : HasType empty [] true
    (.lam false (.array (.natural 2)) (.var 0)) (.pi false (.array two) (.array two)) := by
  have source : HasType empty [] false (.lam false (.array two) (.var 0))
      (.pi false (.array two) (.array two)) := Checker.check_sound
        (by cbv : Checker.check 32 empty [] false (.lam false (.array two) (.var 0))
          (.pi false (.array two) (.array two)) = true)
  have count : ACU.MixedRed two (.natural 2) := .arithmetic (.literalAdd 1 1 (by decide))
  have array : ACU.MixedRed (.array two) (.array (.natural 2)) := .node .array (.cons count .nil)
  exact source.ghostMixedRed emptyWellFormed (.node (.lam false) (.cons array (.cons (.refl _) .nil)))

private def familyDeclaration : FamilyDeclaration :=
  ⟨true, 1, 1, [.pi true .u64 (.node (.ind 0 1) [.var 0])], 0⟩
private def familyEnv : Environment :=
  ⟨#[], #[⟨familyDeclaration, [⟨[⟨true, .u64, none⟩], [.var 0]⟩], false⟩]⟩
private theorem familyWellFormed : UnifiedProgram.EnvWellFormed familyEnv :=
  UnifiedProgram.checkProgram_wellFormed
    (by cbv : UnifiedProgram.checkProgram 24 24 [] [familyDeclaration] = some familyEnv)

/-- The output constructor carries numeral2 while retaining its original
family result indexed by (1+1). -/
theorem dependent_constructor_original_index : HasType familyEnv [] true
    (.node (.con 0 0 1) [.natural 2]) (.node (.ind 0 1) [two]) := by
  have source : HasType familyEnv [] false (.node (.con 0 0 1) [two]) (.node (.ind 0 1) [two]) :=
    Checker.check_sound (by cbv : Checker.check 32 familyEnv [] false
      (.node (.con 0 0 1) [two]) (.node (.ind 0 1) [two]) = true)
  exact source.ghostMixedRed familyWellFormed
    (.node (.con 0 0 1) (.cons (.arithmetic (.literalAdd 1 1 (by decide))) .nil))

/-- Ref formation requires the actual forward rigid Buffer head, including
when the buffer length contracts. -/
theorem ref_buffer_original_type : HasType empty [] true (.ref (.buffer (.natural 2))) (.univ 0) := by
  have source : HasType empty [] false (.ref (.buffer two)) (.univ 0) :=
    Checker.infer_sound (fuel := 24) (by cbv)
  exact source.ghostMixedRed emptyWellFormed
    (.node .ref (.cons (.node .buffer (.cons (.arithmetic (.literalAdd 1 1 (by decide))) .nil)) .nil))

private abbrev allocated : Term := .alloc (.natural 2) (.integer 0)
private abbrev evidence : Term := .decide (.natural 0) (.natural 2)
private def loadContinuation (answer : Term) : Term :=
  .lam false .i64 (.lam false (.buffer (.natural 2)) (.free (.var 0) answer))

/-- A computation under both Load binders preserves the lowered result type. -/
theorem load_nested_computation : HasType empty [] true
    (.load allocated (.natural 0) evidence (loadContinuation (.natural 2))) .u64 := by
  have source : HasType empty [] true (.load allocated (.natural 0) evidence (loadContinuation two)) .u64 :=
    Checker.check_sound (by cbv : Checker.check 32 empty [] true
      (.load allocated (.natural 0) evidence (loadContinuation two)) .u64 = true)
  have answer : ACU.MixedRed two (.natural 2) := .arithmetic (.literalAdd 1 1 (by decide))
  have rest : ACU.MixedRed (.free (.var 0) two) (.free (.var 0) (.natural 2)) :=
    .node .free (.cons (.refl _) (.cons answer .nil))
  have inner : ACU.MixedRed (.lam false (.buffer (.natural 2)) (.free (.var 0) two))
      (.lam false (.buffer (.natural 2)) (.free (.var 0) (.natural 2))) :=
    .node (.lam false) (.cons (.refl _) (.cons rest .nil))
  exact source.ghostMixedRed emptyWellFormed
    (.node .load (.cons (.refl _) (.cons (.refl _) (.cons (.refl _)
      (.cons (.node (.lam false) (.cons (.refl _) (.cons inner .nil))) .nil)))))

/-- The public bounded implementation, rather than an assumed conversion,
supplies the forward reduction used by preservation. -/
theorem concrete_normalizer_original_type : HasType empty [] true
    (.ref (.buffer (.natural 2))) (.univ 0) := by
  have source : HasType empty [] false (.ref (.buffer two)) (.univ 0) :=
    Checker.infer_sound (fuel := 24) (by cbv)
  exact source.ghostNormalize emptyHistory
    (by cbv : Conversion.normalize? empty 4 (.ref (.buffer two)) = some (.ref (.buffer (.natural 2))))

private def backMotive : Term := .lam false (.buffer (.natural 2)) .i64
private def given : Term := .give false backMotive allocated (.integer 0)
private def takeContinuation (count : Term) : Term :=
  .lam false (.buffer count) (.lam false .i64 (.free (.var 1) (.var 0)))

/-- Take retains its two leading lambdas while a declared owner annotation
contracts, and the original lowered result remains I64. -/
theorem take_annotation_computation : HasType empty [] true
    (.take given (takeContinuation (.natural 2))) .i64 := by
  have source : HasType empty [] true (.take given (takeContinuation two)) .i64 :=
    Checker.check_sound (by cbv : Checker.check 40 empty [] true
      (.take given (takeContinuation two)) .i64 = true)
  have count : ACU.MixedRed two (.natural 2) := .arithmetic (.literalAdd 1 1 (by decide))
  have owner : ACU.MixedRed (.buffer two) (.buffer (.natural 2)) := .node .buffer (.cons count .nil)
  exact source.ghostMixedRed emptyWellFormed
    (.node .take (.cons (.refl _) (.cons
      (.node (.lam false) (.cons owner (.cons (.refl _) .nil))) .nil)))

end Jihoo.NativeKernel.Environment.ContextualExamples
