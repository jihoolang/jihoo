import Jihoo.CallEntry
import Jihoo.OwnershipLoweringExamples
namespace Jihoo.CallEntry.Examples
open LoweringEnvironment Quantity OwnershipLowering

def shapes : List Shape := [.ghost, .value, .hypothesis 2, .ghost, .value]

theorem numbered_slots : number shapes 2 =
    [.ghost, .value 2, .hypothesis 3 [4, 5], .ghost, .value 6] := by decide

theorem contiguous_references : pack (number shapes 2) = [2, 3, 4, 5, 6] := by decide

theorem two_phase_allocation :
    number ([.ghost, .hypothesis 2] ++ [.value, .ghost, .value]) 2 =
    number [.ghost, .hypothesis 2] 2 ++ number [.value, .ghost, .value] 5 :=
  number_append _ _

theorem initialized_with_reserved_and_node :
    entry [90] 91 [.ghost, .value 7, .hypothesis 8 [9]] = [90, 91, 7, 8, 9] := by decide

theorem reserved_and_node_not_parameters :
    0 ∉ references [90] [.value 7] ∧ 1 ∉ references [90] [.value 7] := by decide

/-- Instantiate the constructed pipeline without supplying a decoded frame or
an assignment proof. Both are derived by the new entry algorithm. -/
theorem constructed_owner :
    let caller := OwnershipLowering.Examples.caller
    let evaluate := fun i => ((entry [90] 91 caller)[i]?).getD 999
    let callee := number (layout caller) 2
    nativeLookup (callee.map (Slot.map evaluate)) 3 = some (.value 7) ∧
    (∀ xs, Finishes (lowerControl caller OwnershipLowering.Examples.source) xs → xs.count 0 = 1) ∧
    (∀ xs, Prefix (lowerControl caller OwnershipLowering.Examples.source) xs → xs.count 0 ≤ 1) := by
  obtain ⟨r, hr, _, hv, hf, hp⟩ := constructed_owner_pipeline
    (by decide : nativeLookup OwnershipLowering.Examples.caller 3 = some (.value 7))
    (by decide : OwnershipLowering.Examples.source.demand 3 = some 1) [90] 91 999
  have same : r = 0 := by simpa [OwnershipLowering.Examples.caller, layout, Slot.shape,
    resourceMap, scalarPosition, Shape.width] using hr.symm
  subst r
  exact ⟨hv, hf, hp⟩

/-- A wrong start offset silently reads a reserved value, which is why the
constructed numbering and freshness proofs are material premises. -/
theorem wrong_base_counterexample :
    ([90, 91, 7] : List Nat)[0]? = some 90 ∧
    ([90, 91, 7] : List Nat)[2]? = some 7 ∧ (90 : Nat) ≠ 7 := by decide

end Jihoo.CallEntry.Examples
