import Jihoo.PureOwnedScalarBridge

/-! Closing-substitution readiness through the same mixed-context operations.
Unavailable owner/dead entries are not required to carry scalar values. -/
namespace Jihoo.PureOwnedScalar
open OwnedScalarContext

theorem Ready.scalarShift (ready : Ready ctx values) : Ready (scalarShift ctx) (v :: values) := by
  intro k slot lookup
  simp only [OwnedScalarContext.scalarShift, List.getElem?_map] at lookup
  cases h : ctx[k]? with
  | none => simp [h] at lookup
  | some b =>
      cases b with
      | owner | dead => simp [h] at lookup
      | scalar old =>
          simp [h] at lookup
          subst slot
          obtain ⟨value, found, bound⟩ := ready k old h
          exact ⟨value, found, bound⟩

theorem Ready.bindScalar (ready : Ready ctx values) (bound : v < 2^63) :
    Ready (bindScalar ctx) (v :: values) := by
  intro k slot lookup
  cases k with
  | zero =>
      simp [PureOwnedScalar.bindScalar] at lookup
      subst slot
      exact ⟨v, rfl, bound⟩
  | succ k => exact ready.scalarShift k slot lookup

theorem Ready.fresh (ready : Ready ctx values) : Ready (fresh ctx) values := by
  intro k slot lookup
  cases k with
  | zero => simp [ScalarCoreCallers.fresh] at lookup
  | succ k =>
      simp only [ScalarCoreCallers.fresh, List.getElem?_cons_succ, List.getElem?_map] at lookup
      cases h : ctx[k]? with
      | none => simp [h] at lookup
      | some b =>
          cases b with
          | owner | dead => simp [h] at lookup
          | scalar old =>
              simp [h] at lookup
              subst slot
              exact ready k old h

theorem Ready.consumed (ready : Ready ctx values) : Ready (consumed selected ctx) values := by
  intro k slot lookup
  simp only [OwnedScalarContext.consumed, List.getElem?_map] at lookup
  cases h : ctx[k]? with
  | none => simp [h] at lookup
  | some b =>
      cases b with
      | owner old => by_cases eq : old = selected <;> simp [h, eq] at lookup
      | dead => simp [h] at lookup
      | scalar old =>
          simp [h] at lookup
          subst slot
          exact ready k old h

theorem Ready.ownedReturned (ready : Ready ctx values) : Ready (ownedReturned ctx selected) values := by
  intro k slot lookup
  cases k with
  | zero => simp [OwnedScalarContext.ownedReturned] at lookup
  | succ k => exact ready.fresh k slot lookup

theorem Ready.scalarReturned (ready : Ready ctx values) (bound : v < 2^63) :
    Ready (scalarReturned ctx selected) (v :: values) := by
  intro k slot lookup
  cases k with
  | zero => simp [OwnedScalarContext.scalarReturned] at lookup
  | succ k => exact (ready.bindScalar bound) k slot lookup

/-- A conventional scoped scalar environment supplies the generic substitution
premise, independently of which scalar variables a particular term uses. -/
theorem ready_of_scoped (scope : ∀ (k slot : Nat), ctx[k]? = some (.scalar slot) → slot < values.length)
    (bounded : ∀ v ∈ values, v < 2^63) : Ready ctx values := by
  intro k slot lookup
  have inside := scope k slot lookup
  exact ⟨values[slot], List.getElem?_eq_getElem inside, bounded _ (List.getElem_mem inside)⟩

end Jihoo.PureOwnedScalar
