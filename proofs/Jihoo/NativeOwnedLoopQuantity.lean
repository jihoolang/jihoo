import Jihoo.NativeQuantityFunctions

/-! The same projected repeat used by native Fold/Loop forbids every queried
outer owner and checks all local scopes, including an owned accumulator. -/
namespace Jihoo.NativeKernel.NativeQuantity

open Jihoo.Quantity

theorem repeated_body_zero (checked : (.seq first (.repeat body) : Control).demand resource = some count) :
    body.demand resource = some 0 := by
  cases hf : first.demand resource with
  | none => simp [Control.demand, hf] at checked
  | some firstCount =>
      cases hb : body.demand resource with
      | none => simp [Control.demand, hf, hb] at checked
      | some bodyCount =>
          by_cases zero : bodyCount = 0
          · simp only [zero]
          · simp [Control.demand, hf, hb, zero] at checked

theorem checked_repeat_local_and_outer
    (checked : check fuel depth owners erased term = true)
    (projected : project fuel term = some (.seq first (.repeat body))) :
    LocalScopes body ∧ ∀ resource ∈ owners, body.demand resource = some 0 := by
  obtain ⟨c, origin, sentinel, linear, _⟩ := checked_origin checked
  have same : c = .seq first (.repeat body) := Option.some.inj (origin.symm.trans projected)
  rw [same] at sentinel linear
  exact ⟨demand_localScopes body (repeated_body_zero sentinel),
    fun resource found => repeated_body_zero (linear resource found)⟩

theorem iteration_local_accumulator_once
    (locals : LocalScopes (Control.scopes [.unrestricted, .erased, .linear] body)) :
    body.demand 0 = some 1 := locals.2.1

/-- A partial application after an owned runtime argument still cannot return
an explicit residual function, regardless of the new non-linear call support. -/
theorem linear_partial_lambda_rejected (fuel : Nat) (locals : List Bool) (erased : Bool) (A body : Term) :
    peelCallAux (fuel + 1) locals true (.node (.lam erased) [A, body]) [] = none := by
  simp only [peelCallAux, callResult, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte]

end Jihoo.NativeKernel.NativeQuantity
