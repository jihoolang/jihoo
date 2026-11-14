import Jihoo.NativeEnvironmentConversionPolicies

/-! Closed stored bodies are a necessary binding invariant, not a trusted
convenience assumption. An open stored body collapses raw delta/beta equality. -/
namespace Jihoo.NativeKernel.EnvironmentDelta.Basis.Boundary

private def global : Term := .node (.global 0) []
private def openWorld : Environment := ⟨#[⟨.u64,.var 0⟩],#[]⟩

/-- The same raw Global becomes any argument when an open body is unfolded under a lambda. -/
theorem open_global_equals_every_term (term : Term) : Conv openWorld global term := by
  have keep : Conv openWorld (.app (.lam false .u64 global) term) global :=
    .legacy (by simpa only [global,Term.subst,substArgs] using
      NativeKernel.Conversion.Conv.beta false .u64 global term)
  have unfoldBody : Conv openWorld (.app (.lam false .u64 global) term)
      (.app (.lam false .u64 (.var 0)) term) :=
    .node .app (.cons (.node (.lam false) (.cons (.refl _) (.cons (.delta (env := openWorld) (index := 0) (declaration := ⟨.u64,.var 0⟩) rfl) .nil))) (.cons (.refl _) .nil))
  have beta : Conv openWorld (.app (.lam false .u64 (.var 0)) term) term :=
    .legacy (by simpa only [Term.subst,single] using
      NativeKernel.Conversion.Conv.beta false .u64 (.var 0) term)
  exact keep.symm.trans (unfoldBody.trans beta)

theorem open_world_collapses_types : Conv openWorld .u64 (.pi false .i64 .i64) :=
  (open_global_equals_every_term .u64).symm.trans (open_global_equals_every_term (.pi false .i64 .i64))

theorem open_world_not_closed : ¬ Closed openWorld := by
  intro closed
  have scope := closed 0 ⟨.u64,.var 0⟩ rfl
  cases scope with | var bound => omega

theorem open_world_not_admissible : ¬ EnvironmentDelta.Admissible openWorld :=
  fun admitted => open_world_not_closed admitted.closed

end Jihoo.NativeKernel.EnvironmentDelta.Basis.Boundary
