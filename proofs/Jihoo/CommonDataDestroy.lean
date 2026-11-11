import Jihoo.CommonDataSyntax

/-! Store-driven destruction for the single binary family. Runtime derivations
read child references; finite-tree witnesses occur only in the safety theorem. -/
namespace Jihoo.CommonData
open HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime

inductive Destroy : Ref → State → List HeapLeases.Event → State → Prop where
  | empty : Destroy none s [] s
  | node : s.cells x = some cell →
      Destroy cell.left (finish s x) left middle →
      Destroy cell.right middle right t →
      Destroy (some x) s (.free x :: (left ++ right)) t

variable {s : State} {tree : Tree} {frame : List Nat}

theorem Destroy.deterministic (a : Destroy ref s es t) (b : Destroy ref s fs u) :
    es = fs ∧ t = u := by
  induction a generalizing fs u with
  | empty => cases b; exact ⟨rfl,rfl⟩
  | node cell left right ihl ihr =>
    cases b with
    | node other l r =>
      have eq := Option.some.inj (cell.symm.trans other)
      cases eq
      obtain ⟨rfl,rfl⟩ := ihl l
      obtain ⟨rfl,rfl⟩ := ihr r
      exact ⟨rfl,rfl⟩

theorem Destroy.lengths (run : Destroy ref s es t) : t.buffers.length = s.buffers.length := by
  induction run with
  | empty => rfl
  | node cell left right ihl ihr => exact ihr.trans ihl

theorem Destroy.cells_frame (run : Destroy ref s es t) (absent : x ∉ released es) :
    t.cells x = s.cells x := by
  induction run with
  | empty => rfl
  | @node cell s y left middle right t lookup l r ihl ihr =>
    have parts : x ≠ y ∧ x ∉ released left ∧ x ∉ released right := by
      simpa [released, List.filterMap_append] using absent
    rw [ihr parts.2.2, ihl parts.2.1]
    simp [finish, RecursiveCaseBody.finish, put, parts.1]

/-- Exact release trace, safe termination and arbitrary ambient ownership.
The recursive calls are obtained by structural induction on the finite input
interpretation, not by assuming arbitrary pointer graphs terminate. -/
theorem destroy_total (fields : Represents s.cells tree) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (tree.owners ++ frame)) :
    ∃ t, Destroy (root tree) s (tree.owners.map Event.free) t ∧
      Steps s.buffers.heap (tree.owners.map Event.free) t.buffers.heap ∧
      Valid t.buffers.heap ∧ Owns t.buffers.heap frame := by
  induction tree generalizing s frame with
  | empty => exact ⟨s, .empty, .nil, valid, owned⟩
  | node x left right ihl ihr =>
    obtain ⟨step, vm, children⟩ := release_node valid owned
    have separated := root_not_in_fields (OwnedApplicationFrame.owns_left owned)
    have leftFields := fields.2.1.clear_other separated.1
    have rightFields := fields.2.2.clear_other separated.2
    obtain ⟨middle, lrun, lsteps, vl, remain⟩ :=
      ihl (s := finish s x) (frame := right.owners ++ frame) leftFields vm
        (by simpa [List.append_assoc, finish, RecursiveCaseBody.finish, SizedBufferHeap.release, OwnedCoreContinuation.freedState] using children)
    have rightStill : Represents middle.cells right := by
      apply rightFields.congr
      intro y member
      apply lrun.cells_frame
      have noShare : y ∉ left.owners := by
        intro hl
        exact fields_separate (OwnedApplicationFrame.owns_left owned) hl member
      simpa [released] using noShare
    obtain ⟨t, rrun, rsteps, vt, kept⟩ := ihr rightStill vl remain
    refine ⟨t, ?_, ?_, vt, kept⟩
    · simpa [Tree.owners, List.map_append, root] using Destroy.node fields.1 lrun rrun
    · simpa [Tree.owners, List.map_append] using
        Steps.cons step (steps_append lsteps rsteps)

theorem destroy_every_run (fields : Represents s.cells tree) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (tree.owners ++ frame))
    (run : Destroy (root tree) s es t) :
    es = tree.owners.map Event.free ∧ Steps s.buffers.heap es t.buffers.heap ∧
      Valid t.buffers.heap ∧ Owns t.buffers.heap frame := by
  obtain ⟨u, canonical, steps, vu, kept⟩ := destroy_total fields valid owned
  obtain ⟨rfl,rfl⟩ := run.deterministic canonical
  exact ⟨rfl,steps,vu,kept⟩

/-- The primitive frees every owned identity exactly once, with no allocation
or lease events. This is not a whole-language accounting theorem. -/
theorem destroy_accounting (fields : Represents s.cells tree) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (tree.owners ++ frame))
    (run : Destroy (root tree) s es t) :
    released es = tree.owners ∧ (released es).Nodup ∧
      (∀ event ∈ es, ∃ x, event = Event.free x) := by
  obtain ⟨rfl,_,_,_⟩ := destroy_every_run fields valid owned run
  refine ⟨by simp [released, Function.comp_def], ?_, ?_⟩
  · simpa [released, Function.comp_def] using (OwnedApplicationFrame.owns_left owned).distinct
  · intro event member
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp member
    exact ⟨x,rfl⟩

end Jihoo.CommonData
