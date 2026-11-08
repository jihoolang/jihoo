import Jihoo.CheckedCorePrincipal

namespace Jihoo.CoreBridge.CorePrincipal.Examples
open LinearNaturals LinearEvidence

private def wide : Raw := .uadd (.natural (wordBound - 1)) (.natural 1)
private def wideDecision : Raw := .decide (.natural 0) wide

theorem semantic_wide_decision_accepted :
    (LinearEvidence.infer 0 wideDecision).isSome = true := by decide

theorem principal_wide_decision_rejected :
    (CorePrincipal.infer 0 wideDecision).isSome = false := by decide

/-- The extra compatibility premise is necessary, even for true closed claims. -/
theorem wide_decision_unbounded : ¬ DecisionBounded wideDecision := by
  intro h
  have hb := h.2 (fun _ => 0) _ (.add .lit .lit)
  simp [wordBound] at hb

theorem wide_decision_has_no_principal (p : Formula 0) : ¬ Principal wideDecision p := by
  intro h
  exact wide_decision_unbounded h.bounded

theorem wide_zero_le_still_accepted :
    (CorePrincipal.infer 0 (.zeroLe (.natural (wordBound - 1)))).isSome = true := by decide

theorem computed_decision_accepted :
    (CorePrincipal.infer 0 (.decide (.uadd (.natural 1) (.natural 1)) (.natural 3))).isSome = true := by
  decide

theorem false_decision_rejected :
    (CorePrincipal.infer 0 (.decide (.natural 3) (.natural 2))).isSome = false := by decide

theorem symbolic_decision_rejected :
    (CorePrincipal.infer 1 (.decide (.natural 0) (.uadd (.var 0) (.natural 1)))).isSome = false := by
  decide

theorem computed_endpoint_steps : Raw.Computation.Steps
    (.uadd (.natural 2) (.uadd (.natural 1) (.natural 2))) (.natural 5) :=
  closed_reduces (.add (.lit ⟨2, by decide⟩) (.add (.lit ⟨1, by decide⟩) (.lit ⟨2, by decide⟩)) : Expr 0)
    (by decide) (by decide)

/-- Principal shape does not normalize scalar subexpressions or replace the
inferred type by a convertible requested type. -/
theorem original_refl_type_preserved :
    inferredShape (.refl (.uadd (.natural 2) (.natural 3))) =
      some (.eq (.uadd (.natural 2) (.natural 3)) (.uadd (.natural 2) (.natural 3))) := rfl

end Jihoo.CoreBridge.CorePrincipal.Examples
