import Jihoo.RecursiveFieldOwnership
import Jihoo.OwnedApplicationExamples

namespace Jihoo.RecursiveFieldOwnershipExamples
open HeapLeases LinearHeapPrograms RecursiveFieldOwnership OwnedCoreContinuation

def leaf (x : Nat) : Tree := .node x .empty .empty

example : (Tree.node 0 (leaf 1) (.node 2 (leaf 3) .empty)).owners = [0, 1, 2, 3] := rfl

/-- Reject sibling aliasing even though each child could be owned alone. -/
theorem reject_shared_child : ¬ OwnsTree s (.node 0 (leaf 1) (leaf 1)) := by
  intro h
  exact fields_separate (y := 1) h (by simp [leaf, Tree.owners]) (by simp [leaf, Tree.owners])

/-- Reject an ancestor identity hidden two levels into a field. -/
theorem reject_ancestor_alias : ¬ OwnsTree s (.node 0 (.node 1 (leaf 0) .empty) .empty) := by
  intro h
  exact (root_not_in_fields h).1 (by simp [leaf, Tree.owners])

theorem reject_dead_field (dead : s.live 1 = false) :
    ¬ OwnsTree s (.node 0 (leaf 1) .empty) := by
  intro h
  have live := h.live 1 (by simp [leaf, Tree.owners])
  simp [dead] at live

theorem reject_borrowed_field (borrowed : s.lease token = some 1) :
    ¬ OwnsTree s (.node 0 (leaf 1) .empty) := by
  intro h
  exact h.leaseFree 1 (by simp [leaf, Tree.owners]) token borrowed

/-- Destruction preserves the child and the unrelated frame together. -/
theorem release_preserves_child_and_frame (valid : Valid s)
    (owned : Owns s [0, 1, 2]) :
    Step s (.free 0) (freedState s 0) ∧ Valid (freedState s 0) ∧
      Owns (freedState s 0) [1, 2] := by
  exact release_node (l := leaf 1) (r := .empty) (frame := [2]) valid owned

/-- Nonempty, live, unborrowed initial inventory; no safety premise is assumed. -/
def fixture : State := ⟨3, 0, fun x => decide (x < 3), fun _ => 7, fun _ => none⟩

theorem fixture_valid : Valid fixture := by
  constructor
  · intro x h; simpa [fixture] using h
  · intro l x h; simp [fixture] at h

theorem fixture_owned : Owns fixture [0, 1, 2] := by
  constructor
  · decide
  · intro x h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> decide
  · intro x h l; simp [fixture]

/-- A real Core free/return graph consumes the left field, with both primitive
frees justified and the unrelated owner retained. -/
theorem concrete_core_consumer :
    Steps fixture [.free 0, .free 1] (freedState (freedState fixture 0) 1) ∧
    Valid (freedState (freedState fixture 0) 1) ∧
    Owns (freedState (freedState fixture 0) 1) [2] := by
  exact consume_left (l := leaf 1) (r := .empty) (frame := [2])
    OwnedApplicationExamples.consume_typed rfl rfl fixture_valid fixture_owned
    (OwnedApplicationExamples.consume_run (freedState fixture 0) 1)

end Jihoo.RecursiveFieldOwnershipExamples
