import Jihoo.NativeDependentProofFundamental

/-! Concrete checker regressions for dependent source interpretation. Semantic
truth is derived from typing and syntax recognition, without normalization. -/
namespace Jihoo.NativeKernel.Environment.Semantics.Dependent.Examples
open Jihoo.NativeKernel.Environment.Conversion

private theorem emptyWellFormed : UnifiedProgram.EnvWellFormed empty :=
  UnifiedProgram.UnifiedProgramChecked.empty.wellFormed

private def reflexive : Term := .lam false .u64 (.refl (.var 0))
private def reflexiveType : Term := .pi false .u64 (.eq (.var 0) (.var 0))
private theorem reflexiveRecognized : Recognized reflexive := .lam (.refl (.var 0))

theorem dependent_lambda_realized : ∀ assignment, FamilyTruth empty reflexiveType assignment := by
  have typed : HasType empty [] true reflexive reflexiveType := Checker.check_sound
    (by cbv : Checker.check 24 empty [] true reflexive reflexiveType = true)
  exact native_fundamental (depth := 0) emptyWellFormed typed reflexiveRecognized

theorem dependent_application_realized :
    ∀ assignment, FamilyTruth empty (.eq (.natural 7) (.natural 7)) assignment := by
  have typed : HasType empty [] true (.app reflexive (.natural 7)) (.eq (.natural 7) (.natural 7)) :=
    Checker.check_sound (by cbv : Checker.check 24 empty [] true (.app reflexive (.natural 7))
      (.eq (.natural 7) (.natural 7)) = true)
  exact native_fundamental (depth := 0) emptyWellFormed typed (.app (.natural 7) reflexiveRecognized)

private def outerCapture : Term :=
  .lam false .u64 (.app (.lam false .u64 (.refl (.var 1))) (.var 0))

theorem outer_index_survives_dependent_application :
    ∀ assignment, FamilyTruth empty reflexiveType assignment := by
  have typed : HasType empty [] true outerCapture reflexiveType := Checker.check_sound
    (by cbv : Checker.check 32 empty [] true outerCapture reflexiveType = true)
  exact native_fundamental (depth := 0) emptyWellFormed typed
    (.lam (.app (.var 0) (.lam (.refl (.var 1)))))

private def innerCapture : Term := .lam false .u64 (.lam false .u64 (.refl (.var 0)))
private def innerType : Term := .pi false .u64 (.pi false .u64 (.eq (.var 0) (.var 0)))

theorem nested_dependent_lambdas_realized : ∀ assignment, FamilyTruth empty innerType assignment := by
  have typed : HasType empty [] true innerCapture innerType := Checker.check_sound
    (by cbv : Checker.check 24 empty [] true innerCapture innerType = true)
  exact native_fundamental (depth := 0) emptyWellFormed typed (.lam (.lam (.refl (.var 0))))

private def rawResult : Term := .uadd (.eq (.natural 7) (.natural 7)) (.natural 0)

theorem unformed_proposition_representative_realized : ∀ assignment, FamilyTruth empty rawResult assignment := by
  have typed : HasType empty [] true (.app reflexive (.natural 7)) rawResult := Checker.check_sound
    (by cbv : Checker.check 24 empty [] true (.app reflexive (.natural 7)) rawResult = true)
  exact native_fundamental (depth := 0) emptyWellFormed typed (.app (.natural 7) reflexiveRecognized)

private def declaration : GlobalDeclaration := ⟨.prop,reflexiveType⟩
private def checkedEnvironment : Environment := ⟨#[declaration],#[]⟩
private theorem history : UnifiedProgram.UnifiedProgramChecked [declaration] [] checkedEnvironment :=
  UnifiedProgram.checkProgram_sound
    (by cbv : UnifiedProgram.checkProgram 32 32 [declaration] [] = some checkedEnvironment)

theorem checked_delta_dependent_family_realized :
    ∀ assignment, FamilyTruth checkedEnvironment (.node (.global 0) []) assignment := by
  have typed : HasType checkedEnvironment [] true reflexive (.node (.global 0) []) := Checker.check_sound
    (by cbv : Checker.check 32 checkedEnvironment [] true reflexive (.node (.global 0) []) = true)
  exact checked_fundamental (depth := 0) history typed reflexiveRecognized

theorem false_closed_equality_excluded
    (typed : HasType empty [] mode term (.eq (.natural 0) (.natural 1)))
    (recognized : Recognized term) : False :=
  no_recognized_false_equality emptyWellFormed (by decide) typed recognized

theorem false_closed_less_excluded
    (typed : HasType empty [] mode term (.lt (.natural 1) (.natural 0)))
    (recognized : Recognized term) : False :=
  no_recognized_false_less emptyWellFormed (by decide) typed recognized

end Jihoo.NativeKernel.Environment.Semantics.Dependent.Examples
