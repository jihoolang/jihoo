import Jihoo.CommonDataFrameSafety

namespace Jihoo.CommonData
open HeapLeases LinearHeapPrograms RecursiveLexicalFields

/-- All executions of the same typed graph have the accounted postcondition,
including executions admitted independently of a resource partition plan. -/
theorem Typing.every_run_accounted (typed : Typing g ctx count sizes term kind)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) ctx env)
    (layout : SizedBufferContext.Layout s.buffers owners sizes) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) (observed : Eval g env term s v es t) :
    AccountedPost kind t v frame (footprint (caps trees owners)) es := by
  obtain ⟨w,fs,u,canonical,_,_,post⟩ := typed.total_accounted length agreement layout valid owned fields
  obtain ⟨rfl,rfl,rfl⟩ := observed.deterministic canonical
  exact post

/-- Any tracked allocation absent from the returned whole-tree footprint is
released exactly once and really dead. No initial coverage is needed. -/
theorem Typing.other_released (typed : Typing g ctx count sizes term kind)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) ctx env)
    (layout : SizedBufferContext.Layout s.buffers owners sizes) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) (observed : Eval g env term s v es t)
    (outputView : ResultFootprint t.cells v output)
    (tracked : x ∈ footprint (caps trees owners) ∨ x ∈ allocations es)
    (notReturned : x ∉ output) : (released es).count x = 1 ∧ t.buffers.heap.live x = false := by
  have safe := (typed.every_run length agreement layout valid owned fields observed).1
  have post := typed.every_run_accounted length agreement layout valid owned fields observed
  have eq := post.account_for outputView x
  rw [List.count_eq_zero.mpr notReturned, Nat.add_zero] at eq
  have positive : 0 < (released es).count x := by
    rcases tracked with initial | allocated
    · have := List.count_pos_iff.mpr initial; omega
    · have := List.count_pos_iff.mpr allocated; omega
  have member := List.count_pos_iff.mp positive
  have once := (releases_distinct valid safe).count (a := x)
  exact ⟨by simpa [member] using once,released_dead valid safe (released_mem.mp member)⟩

/-- Returned descendants and external frame objects survive and cannot have
been released by the safe trace. This is allocation, not lease accounting. -/
theorem Typing.survivors (typed : Typing g ctx count sizes term kind)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) ctx env)
    (layout : SizedBufferContext.Layout s.buffers owners sizes) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) (observed : Eval g env term s v es t)
    (outputView : ResultFootprint t.cells v output) (member : x ∈ output ++ frame) :
    t.buffers.heap.live x = true ∧ x ∉ released es := by
  have safe := (typed.every_run length agreement layout valid owned fields observed).1
  obtain ⟨actual,view,final,_⟩ :=
    (typed.every_run_accounted length agreement layout valid owned fields observed).output
  cases view.unique outputView
  have live := final.live x member
  refine ⟨live,?_⟩
  intro released
  have dead := released_dead valid safe (released_mem.mp released)
  simp [live] at dead

/-- Initial live coverage is essential. The conclusion is equality of live
identity sets, not equality of payloads, stale cells or allocation counters. -/
theorem Typing.live_domain (typed : Typing g ctx count sizes term kind)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) ctx env)
    (layout : SizedBufferContext.Layout s.buffers owners sizes) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) (observed : Eval g env term s v es t)
    (outputView : ResultFootprint t.cells v output)
    (coverage : ∀ x, s.buffers.heap.live x = true → x ∈ footprint (caps trees owners) ++ frame) :
    ∀ x, t.buffers.heap.live x = true ↔ x ∈ output ++ frame := by
  intro x
  constructor
  · intro live
    by_cases member : x ∈ output ++ frame
    · exact member
    have safe := (typed.every_run length agreement layout valid owned fields observed).1
    have origin := live_origin safe live
    have tracked : x ∈ footprint (caps trees owners) ∨ x ∈ allocations es := by
      rcases origin with initial | allocated
      · rcases List.mem_append.mp (coverage x initial) with input | ambient
        · exact Or.inl input
        · exact False.elim (member (List.mem_append_right output ambient))
      · exact Or.inr allocated
    have dead := (typed.other_released length agreement layout valid owned fields observed outputView tracked
      (fun returned => member (List.mem_append_left frame returned))).2
    simp [live] at dead
  · intro member
    exact (typed.survivors length agreement layout valid owned fields observed outputView member).1

/-- A scalar consumer with complete initial coverage and no external frame
leaves no live allocation, including allocations created inside its execution. -/
theorem Typing.scalar_no_leaks (typed : Typing g ctx count sizes term .scalar)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) ctx env)
    (layout : SizedBufferContext.Layout s.buffers owners sizes) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners)))
    (fields : Fields s.cells (caps trees owners)) (observed : Eval g env term s (.scalar n) es t)
    (coverage : ∀ x, s.buffers.heap.live x = true → x ∈ footprint (caps trees owners)) :
    ∀ x, t.buffers.heap.live x = false := by
  have domain := typed.live_domain (frame := []) length agreement layout valid (by simpa using owned)
    fields observed (output := []) rfl (by simpa using coverage)
  intro x
  have absent : ¬ t.buffers.heap.live x = true := by simpa using (domain x).mp
  cases h : t.buffers.heap.live x <;> simp_all

end Jihoo.CommonData
