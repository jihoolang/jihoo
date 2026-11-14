import Jihoo.NativeEnvironmentContextualPreservation

/-! Regression derivations for global unfolding in the same executable checker,
conversion, and original-type metatheory. No independent delta checker is used. -/
namespace Jihoo.NativeKernel.Environment.DeltaCAPIExamples

private def global (index : Nat) : Term := .node (.global index) []
private def identity : Term := .lam false .u64 (.var 0)
private def definitions : List GlobalDeclaration :=
  [⟨.univ 0,.u64⟩,⟨global 0,.natural 7⟩,⟨.pi false (global 0) (global 0),identity⟩]
private def env : Environment :=
  ⟨#[⟨.univ 0,.u64⟩,⟨.u64,.natural 7⟩,⟨.pi false .u64 .u64,identity⟩],#[]⟩
private theorem history : UnifiedProgram.UnifiedProgramChecked definitions [] env :=
  UnifiedProgram.checkProgram_sound
    (by cbv : UnifiedProgram.checkProgram 24 24 definitions [] = some env)

/-- Global equality is part of the conversion used by all typing constructors. -/
theorem installed_type_alias : Conversion.Conv env (global 0) .u64 := .delta (env := env) (index := 0) (declaration := ⟨.univ 0,.u64⟩) rfl

theorem actual_checker_compares_alias : Checker.check 24 env [] false (.natural 7) (global 0) = true := by cbv

theorem actual_checker_exposes_global_function :
    Checker.infer 24 env [] false (.app (global 2) (global 1)) = some .u64 := by cbv

theorem actual_checker_types_alias_binder :
    Checker.infer 24 env [] false (.lam false (global 0) (.var 0)) =
      some (.pi false (global 0) (global 0)) := by cbv

theorem actual_checker_normalizes_global_beta :
    Conversion.normalize? env 24 (.app (global 2) (global 1)) = some (.natural 7) := by cbv

theorem original_alias_type_retained : HasType env [] true (.natural 7) (global 0) := by
  have typed : HasType env [] false (.app (global 2) (global 1)) (global 0) :=
    Checker.check_sound (fuel := 24) (by cbv)
  exact typed.ghostNormalize history (by cbv :
    Conversion.normalize? env 24 (.app (global 2) (global 1)) = some (.natural 7))

theorem unfolding_under_dependent_binder_retains_original_type :
    HasType env [] true identity (.pi false (global 0) (global 0)) := by
  have typed : HasType env [] false (.lam false (global 0) (.var 0))
      (.pi false (global 0) (global 0)) := Checker.infer_sound (fuel := 24) (by cbv)
  exact typed.ghostNormalize history (by cbv :
    Conversion.normalize? env 24 (.lam false (global 0) (.var 0)) = some identity)

theorem authentic_world_type_uniqueness (typed : HasType env [] mode identity type) :
    Conversion.Conv env (.pi false .u64 .u64) type :=
  (Checker.infer_sound (fuel := 24) (by cbv :
    Checker.infer 24 env [] false identity = some (.pi false .u64 .u64))).unique history.wellFormed typed

/-- A later definition cannot invalidate the positive code continuation certificate. -/
theorem code_nonfunction_prefix_stable (extension : Extends before after)
    (checked : continuationAllowed before false type) : continuationAllowed after false type := by
  rcases checked with impossible | witness
  · cases impossible
  · exact Or.inr (witness.extend extension)

/-- Unresolved aliases fail bounded comparison instead of becoming scalar type witnesses. -/
theorem unresolved_alias_comparison_rejected : Conversion.equal env 24 (global 9) .u64 = false := by cbv

theorem malformed_alias_comparison_rejected :
    Conversion.equal env 24 (.node (.global 0) [.natural 1]) .u64 = false := by cbv

end Jihoo.NativeKernel.Environment.DeltaCAPIExamples
