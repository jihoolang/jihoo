import Jihoo.RecursiveFieldRuntime
import Jihoo.RecursiveFieldOwnershipExamples

namespace Jihoo.RecursiveFieldRuntimeExamples
open HeapLeases LinearHeapPrograms OwnedCoreContinuation RecursiveFieldOwnership
open RecursiveFieldRuntime
open RecursiveFieldOwnershipExamples (leaf)

def rightTree : Tree := .node 2 (leaf 3) .empty

def fixture : RecursiveFieldRuntime.State :=
  ⟨⟨4, 0, fun x => decide (x < 4), fun _ => 7, fun _ => none⟩,
    fun x => if x = 0 then some ⟨some 1, some 2⟩
      else if x = 2 then some ⟨some 3, none⟩
      else if x = 1 ∨ x = 3 then some ⟨none, none⟩ else none⟩

theorem valid_fixture : Valid fixture.heap := by
  constructor
  · intro x h; simpa [fixture] using h
  · intro l x h; simp [fixture] at h

theorem owns_fixture : Owns fixture.heap [0, 1, 2, 3] := by
  constructor
  · decide
  · intro x h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> decide
  · intro x h l; simp [fixture]

theorem fields_fixture : Represents fixture.cells (.node 0 (leaf 1) rightTree) := by
  simp [Represents, fixture, leaf, rightTree, root]

/-- The runtime split reads pointers 1 and 2, not the flattened right inventory
[2,3]. This distinguishes actual field roots from ownership accounting. -/
theorem split_actual_pointers :
    (take fixture 0).map Prod.fst = some ⟨some 1, some 2⟩ := by decide

theorem missing_cell_stuck : take { fixture with cells := fun _ => none } 0 = none := rfl

theorem dead_parent_stuck : take (release fixture 0) 0 = none := rfl

theorem wrong_field_rejected :
    ¬ Interprets { fixture with cells := put fixture.cells 0 (some ⟨some 3, some 2⟩) }
      (some 0) (.node 0 (leaf 1) rightTree) := by
  intro h
  have cell := h.fields.1
  simp [put, leaf, root] at cell

/-- An active reader prevents ownership interpretation even though raw take
has no dynamic lease guard; static ownership must justify its use. -/
theorem borrowed_parent_rejected :
    ¬ Interprets { fixture with heap := { fixture.heap with lease := fun _ => some 0 } }
      (some 0) (.node 0 (leaf 1) rightTree) := by
  intro h
  exact h.owned.leaseFree 0 (by simp [Tree.owners]) 0 rfl

/-- Nonvacuous totality instance: the existing Core consumer frees left child
1 and returns a scalar; interpretation of right nodes 2 and 3 survives. -/
theorem interpreted_core_consumer :
    ∃ value events t,
      take fixture 0 = some (⟨some 1, some 2⟩, release fixture 0) ∧
      OwnedCoreApplications.Evaluation OwnedApplicationExamples.graph .scalar
        OwnedCoreResults.consumerContext 9 [1] [] (release fixture 0).heap value events t ∧
      Steps fixture.heap (.free 0 :: events) t ∧ Valid t ∧
      Owns t (OwnedCoreApplications.resultOwners .scalar value ++ [2, 3]) ∧
      Interprets ⟨t, (release fixture 0).cells⟩ (some 2) rightTree := by
  exact RecursiveFieldRuntime.consume_left_total (l := leaf 1) (r := rightTree) (frame := [])
    OwnedApplicationExamples.consume_typed rfl rfl valid_fixture fields_fixture owns_fixture

def emptyState : RecursiveFieldRuntime.State := ⟨HeapLeases.empty, fun _ => none⟩

theorem allocate_then_take :
    take (allocate emptyState none none 7) 0 =
      some (⟨none, none⟩, release (allocate emptyState none none 7) 0) := rfl

/-- A store lookup cannot justify a shorter ownership witness for the same
root, even if a caller supplies that alternate tree explicitly. -/
theorem truncated_witness_rejected :
    ¬ Represents fixture.cells (.node 0 (leaf 1) (leaf 2)) := by
  intro h
  have eq := Represents.unique fields_fixture h rfl
  have impossible : rightTree = leaf 2 := (Tree.node.inj eq).2.2
  cases impossible

end Jihoo.RecursiveFieldRuntimeExamples
