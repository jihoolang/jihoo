import Jihoo.ReferenceHeapFrame

/-! Kernel-checked boundary witnesses. No native_decide or additional axioms. -/
namespace Jihoo.ReferenceHeap.Frame.Checks

private def buffer : Object := ⟨true, #[some (.scalar 7), none]⟩
private def data : Object := ⟨true, #[some (.reference .null), some (.reference (.object 0 0))]⟩
private def heap : Heap := #[buffer, data]

-- Distinct references are not sufficient separation for object-level ownership.
theorem distinct_refs_alias_object : Ref.object 0 0 ≠ Ref.object 0 1 := by decide

theorem alias_release_invalidates_other_slot :
    ((release heap (.object 1 0)).bind (fun K => loadRef K (.object 1 1))) = none ∧
    loadRef heap (.object 1 1) = some (.object 0 0) := by decide

theorem alias_store_changes_content :
    ((store heap (.object 0 0) (.scalar 8)).bind (fun K => loadScalar K (.object 0 0))) =
      some 8 ∧ loadScalar heap (.object 0 0) = some 7 := by decide

-- Pointer contents do not confer ownership or promise target liveness.
theorem foreign_pointer_survives_but_target_dies :
    ((release heap (.object 0 0)).bind (fun K => loadRef K (.object 1 1))) =
      some (.object 0 0) ∧
    ((release heap (.object 0 0)).bind (fun K => load K (.object 0 0))) = none := by decide

theorem store_dangling_allowed :
    ((store heap (.object 1 0) (.reference (.object 999 99))).bind
      (fun K => loadRef K (.object 1 0))) = some (.object 999 99) := by decide

theorem self_reference_allowed :
    ((store heap (.object 1 0) (.reference (.object 1 0))).bind
      (fun K => loadRef K (.object 1 0))) = some (.object 1 0) := by decide

theorem uninitialized_address_is_valid :
    address heap (.object 0 1) = some (0, 1, buffer) ∧
    load heap (.object 0 1) = none := by decide

theorem store_initializes :
    ((store heap (.object 0 1) (.scalar 9)).bind
      (fun K => loadScalar K (.object 0 1))) = some 9 := by decide

theorem initialized_null_differs_from_uninitialized :
    loadRef heap (.object 1 0) = some .null ∧ loadRef heap (.object 0 1) = none := by decide

theorem one_past_is_invalid :
    load heap (.object 0 2) = none ∧ store heap (.object 0 2) (.scalar 1) = none := by decide

theorem absent_object_is_invalid :
    load heap (.object 2 0) = none ∧ store heap (.object 2 0) (.scalar 1) = none ∧
    release heap (.object 2 0) = none := by decide

theorem null_operations_fail :
    load heap .null = none ∧ store heap .null (.scalar 1) = none ∧
    release heap .null = none := by decide

theorem dead_operations_fail :
    let H : Heap := #[⟨false, #[some (.scalar 7)]⟩]
    load H (.object 0 0) = none ∧ store H (.object 0 0) (.scalar 1) = none ∧
    release H (.object 0 0) = none := by decide

theorem interior_release_fails : release heap (.object 1 1) = none := by decide

theorem zero_size_live_base_not_readable :
    let H : Heap := #[⟨true, #[]⟩]
    address H (.object 0 0) = none ∧
    release H (.object 0 0) = some #[⟨false, #[]⟩] := by decide

theorem oversized_scalar_rejected :
    store heap (.object 0 0) (.scalar BoundedMir.scalarBound) = none := by decide

theorem wrong_typed_load_fails :
    loadRef heap (.object 0 0) = none ∧ loadScalar heap (.object 1 0) = none := by decide

theorem scalar_store_breaks_reference_load :
    ((store heap (.object 1 0) (.scalar 3)).bind
      (fun K => loadRef K (.object 1 0))) = none := by decide

-- Non-vacuous mixed Buffer/Data ownership, with scalar initialization, null,
-- and a pointer alias into the buffer. Separation is on owners, not cell values.
private def claims : List Claim :=
  [⟨0, .buffer, buffer.cells⟩, ⟨1, .data, data.cells⟩]

theorem mixed_example : OwnMixed claims heap := by
  simp only [OwnMixed, claims, Own, heap, Shape, buffer, data] at *
  simp [validCell,
    BoundedMir.scalarBound, Array.getElem?_eq_some_iff]
  constructor <;> intro i v hi hv <;>
    have cases : i = 0 ∨ i = 1 := by omega
  all_goals rcases cases with rfl | rfl <;> simp_all
  all_goals subst v <;> simp

-- A third object can change while both kinds survive together.
theorem mixed_store_client (H K : Heap) (h : store H (.object 2 i) v = some K)
    (owned : OwnMixed claims H) : OwnMixed claims K := by
  apply store_mixed h _ owned
  simp [claims]

theorem mixed_release_client (H K : Heap) (h : release H (.object 2 0) = some K)
    (owned : OwnMixed claims H) : OwnMixed claims K := by
  apply release_mixed h _ owned
  simp [claims]

end Jihoo.ReferenceHeap.Frame.Checks
