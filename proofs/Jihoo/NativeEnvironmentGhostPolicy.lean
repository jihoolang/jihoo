import Jihoo.NativeEnvironmentCheckerSoundness

/-! A neutral nonfunction certificate is not stable under unrestricted ghost
substitution. The declarative continuation policy makes this boundary explicit;
the data-input checker applies the nonfunction gate only to executable code. -/
namespace Jihoo.NativeKernel.Environment

theorem nonFunction_neutral : nonFunction (.var 0) :=
  Environment.nonFunctionHead_full rfl

theorem function_not_nonFunction : ¬ nonFunction (.pi false .u64 .u64) := by
  intro impossible
  exact impossible false .u64 .u64 (.refl _)

theorem nonFunction_not_substitution_stable :
    ∃ term substitution, nonFunction term ∧ ¬nonFunction (term.subst substitution) := by
  refine ⟨.var 0, (fun _ => .pi false .u64 .u64), nonFunction_neutral, ?_⟩
  simpa only [Term.subst] using function_not_nonFunction

theorem ghost_continuation_allowed (result : Term) : continuationAllowed true result := Or.inl rfl

theorem code_continuation_nonFunction (allowed : continuationAllowed false result) : nonFunction result := by
  rcases allowed with impossible | admitted
  · cases impossible
  · exact admitted

namespace GhostContinuationExamples

def beforeContext : Context :=
  [⟨.buffer (.natural 2), false⟩, ⟨.var 0, false⟩, ⟨.univ 0, false⟩]

def afterContext : Context :=
  [⟨.buffer (.natural 2), false⟩, ⟨.pi false .u64 .u64, false⟩]

def loadTerm : Term := .load (.var 0) (.natural 0) (.decide (.natural 0) (.natural 2))
  (.lam false .i64 (.lam false (.buffer (.natural 2)) (.var 3)))

/-- A:Type0, f:A, b:Buffer 2: neutral A passes Core's strict Load gate. -/
theorem neutral_result_accepted :
    Checker.infer 32 empty beforeContext true loadTerm = some (.var 2) := by cbv

/-- Substitute A := U64→U64: ghost checking preserves the accepted result. -/
theorem function_substitution_accepted :
    Checker.infer 32 empty afterContext true loadTerm = some (.pi false .u64 .u64) := by cbv

/-- Runtime continuation capture policy remains unchanged. -/
theorem function_result_code_rejected :
    Checker.infer 32 empty afterContext false loadTerm = none := by cbv

end GhostContinuationExamples
end Jihoo.NativeKernel.Environment
