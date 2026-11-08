import Jihoo.CheckedFirstOrderApplication

namespace Jihoo.CoreBridge.LinearEvidence.ApplicationExamples
open LinearNaturals

/-- The argument is an existing free variable. Substituting beneath a new
quantifier must move it to index 1, not capture it as the new index 0. -/
private def openBody : Formula 2 := .all (.equal (.var ⟨1, by decide⟩) (.var ⟨0, by decide⟩))
private def openArgument : Expr 1 := .var ⟨0, by decide⟩

theorem capture_avoided : (openBody.instantiate openArgument).encode =
    .pi false .u64 (.eq (.var 1) (.var 0)) := by rfl

theorem capture_would_change_truth : ¬(openBody.instantiate openArgument).Holds (fun _ => 7) := by
  rw [Formula.holds_instantiate]
  intro h
  have bad := h 9
  change 7 = 9 at bad
  omega

private def deeperBody : Formula 2 :=
  .all (.all (.equal (.var ⟨2, by decide⟩) (.var ⟨0, by decide⟩)))

theorem two_binders_avoid_capture : (deeperBody.instantiate openArgument).encode =
    .pi false .u64 (.pi false .u64 (.eq (.var 2) (.var 0))) := by rfl

private def sum : Expr 2 := .add (.var ⟨1, by decide⟩) (.var ⟨0, by decide⟩)

private def afterFirst : Formula 1 := (Formula.equal sum sum).substitute
  (lift (Fin.cases (.lit ⟨3, by decide⟩ : Expr 0) Expr.var))

theorem nested_application_sound (ρ : Nat → Nat) :
    (afterFirst.instantiate (.lit ⟨4, by decide⟩)).Holds ρ := by
  have first := Applied.app (.base (Derives.lam (Derives.lam (Derives.refl sum))))
    (.lit ⟨3, by decide⟩ : Expr 0)
  have second := Applied.app first (.lit ⟨4, by decide⟩ : Expr 0)
  exact second.sound ρ

end Jihoo.CoreBridge.LinearEvidence.ApplicationExamples
