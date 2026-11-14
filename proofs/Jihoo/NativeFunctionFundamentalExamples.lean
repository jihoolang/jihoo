import Jihoo.NativeFunctionFundamental
import Jihoo.NativeTypeFormationBoundary

/-! Independent checker inputs exercise the contextual source fundamental.
No test supplies normalization or realization of its own source as a premise. -/
namespace Jihoo.NativeKernel.Environment.Semantics.Functions.Examples
open Jihoo.NativeKernel.Environment.Conversion

private theorem emptyWellFormed : UnifiedProgram.EnvWellFormed empty :=
  UnifiedProgram.UnifiedProgramChecked.empty.wellFormed

private def identity : Term := .lam false .u64 (.var 0)
private def application : Term := .app identity (.natural 7)

private theorem identityRecognized : Recognized identity := .lam .natural .var
private theorem applicationRecognized : Recognized application := .app identityRecognized .natural

theorem checked_identity_application_canonicity :
    ∃ value, value < 2^64 ∧ Conv empty application (.natural value) := by
  have typed : HasType empty [] true application .u64 := Checker.check_sound
    (by cbv : Checker.check 24 empty [] true application .u64 = true)
  exact closed_natural_canonicity emptyWellFormed typed applicationRecognized

private def intrinsicIdentity : Expression [] (.arrow .natural .natural) := .lam (.var .here)
private def intrinsicApplication : Expression [] .natural := .app intrinsicIdentity (.natural 7 (by decide))

theorem computed_identity_application : Conv env application (.natural 7) := by
  have result := intrinsicApplication.closed_natural_conversion (env := env)
  simpa only [intrinsicApplication,intrinsicIdentity,Expression.syntax,Expression.meaning,
    Member.value,application,identity,SimpleType.syntax] using result.2

theorem native_identity_accepts_arbitrary_realizable_argument
    (argument : Realizes env .natural term value) : Realizes env .natural (.app identity term) value := by
  have function := intrinsicIdentity.closed_fundamental (env := env)
  exact function term value argument

private def twice : Term :=
  .lam false (.pi false .u64 .u64)
    (.lam false .u64 (.app (.var 1) (.app (.var 1) (.var 0))))
private def twiceApplied : Term := .app (.app twice identity) (.natural 7)

private theorem twiceRecognized : Recognized twice :=
  .lam (.arrow .natural .natural) (.lam .natural (.app .var (.app .var .var)))

theorem checked_higher_order_canonicity :
    ∃ value, value < 2^64 ∧ Conv empty twiceApplied (.natural value) := by
  have typed : HasType empty [] true twiceApplied .u64 := Checker.check_sound
    (by cbv : Checker.check 32 empty [] true twiceApplied .u64 = true)
  exact closed_natural_canonicity emptyWellFormed typed (.app (.app twiceRecognized identityRecognized) .natural)

theorem converted_unformed_result_realized :
    ∃ A, ∃ expression : Expression [] A,
      expression.syntax = .natural 0 ∧ Conv empty A.syntax TypeFormationBoundary.badType ∧
      Realizes empty A (.natural 0) (expression.meaning .nil) := by
  have typed : HasType empty [] true (.natural 0) TypeFormationBoundary.badType := Checker.check_sound
    (by cbv : Checker.check 24 empty [] true (.natural 0) TypeFormationBoundary.badType = true)
  exact closed_native_fundamental emptyWellFormed typed .natural

private def aliasDeclaration : GlobalDeclaration := ⟨.univ 0,.u64⟩
private def aliasEnvironment : Environment := ⟨#[aliasDeclaration],#[]⟩
private theorem aliasHistory : UnifiedProgram.UnifiedProgramChecked [aliasDeclaration] [] aliasEnvironment :=
  UnifiedProgram.checkProgram_sound
    (by cbv : UnifiedProgram.checkProgram 24 24 [aliasDeclaration] [] = some aliasEnvironment)

theorem checked_delta_result_realized :
    ∃ A, ∃ expression : Expression [] A,
      expression.syntax = application ∧ Conv aliasEnvironment A.syntax (.node (.global 0) []) ∧
      Realizes aliasEnvironment A application (expression.meaning .nil) := by
  have typed : HasType aliasEnvironment [] true application (.node (.global 0) []) := Checker.check_sound
    (by cbv : Checker.check 24 aliasEnvironment [] true application (.node (.global 0) []) = true)
  exact closed_native_fundamental aliasHistory.wellFormed typed applicationRecognized

theorem checked_delta_result_canonicity :
    ∃ value, value < 2^64 ∧ Conv aliasEnvironment application (.natural value) := by
  have typed : HasType aliasEnvironment [] true application (.node (.global 0) []) := Checker.check_sound
    (by cbv : Checker.check 24 aliasEnvironment [] true application (.node (.global 0) []) = true)
  have delta : Conv aliasEnvironment (.node (.global 0) []) .u64 := EnvironmentDelta.Basis.Conv.delta (env := aliasEnvironment) (index := 0) (declaration := aliasDeclaration) (by rfl)
  exact closed_natural_canonicity aliasHistory.wellFormed (typed.convert delta) applicationRecognized

end Jihoo.NativeKernel.Environment.Semantics.Functions.Examples
