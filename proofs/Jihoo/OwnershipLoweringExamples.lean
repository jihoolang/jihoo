import Jihoo.OwnershipLowering
namespace Jihoo.OwnershipLowering.Examples
open LoweringEnvironment Quantity Quantity.Substitution

def caller : List (Slot Nat) := [.value 7, .hypothesis 100 [101, 102], .value 9, .ghost]
def references : List Nat := [10, 11, 12, 13, 14]
def callee : List (Slot Nat) := [.value 10, .hypothesis 11 [12, 13], .value 14, .ghost]
def evaluate (i : Nat) : Nat := [7, 100, 101, 102, 9][i - 10]!
def source : Control := .scope .erased (.seq (.use 4) (.use 2))

theorem packed_owner_positions :
    resourceMap (layout caller) 3 = some 0 ∧ resourceMap (layout caller) 1 = some 4 := by decide

theorem no_scalar_hypothesis_or_ghost :
    resourceMap (layout caller) 2 = none ∧ resourceMap (layout caller) 0 = none := by decide

theorem decoded_frame : decode (layout caller) references = some callee := by decide
theorem assigned_frame : references.map evaluate = pack caller := by decide

/-- This example uses the integrated theorem, not a direct trace recount. -/
theorem integrated_owner :
    nativeLookup (callee.map (Slot.map evaluate)) 3 = some (.value 7) ∧
    (∀ xs, Finishes (lowerControl caller source) xs → xs.count 0 = 1) ∧
    (∀ xs, Prefix (lowerControl caller source) xs → xs.count 0 ≤ 1) := by
  obtain ⟨r, hr, _, hv, hf, hp⟩ := checked_owner_pipeline
    (by decide : nativeLookup caller 3 = some (.value 7))
    (by decide : source.demand 3 = some 1) decoded_frame assigned_frame
  have same : r = 0 := by simpa [caller, layout, Slot.shape, resourceMap, scalarPosition,
    Shape.width] using hr.symm
  subst r
  exact ⟨hv, hf, hp⟩

theorem nonvacuous_runtime_trace : Finishes (lowerControl caller source) [0, 4] :=
  .seq .use .use

/-- Checking alone cannot guarantee a native resource if its alleged slot is
actually ghost. The native scalar-owner premise is essential. -/
theorem ghost_owner_counterexample :
    (Control.use 0).demand 0 = some 1 ∧ lowerControl caller (.use 0) = .pure := by decide

theorem trap_prefix_survives :
    Prefix (lowerControl caller (.seq (.use 3) .trap)) [0] := .seqRight .use .start

theorem trap_does_not_finish :
    ¬ Finishes (lowerControl caller (.seq (.use 3) .trap)) xs := by
  intro h
  obtain ⟨ys, hy, _⟩ := finishes_iff.mp h
  cases hy with | seq _ ht => cases ht

end Jihoo.OwnershipLowering.Examples
