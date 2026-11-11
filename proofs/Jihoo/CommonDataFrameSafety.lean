import Jihoo.CommonDataDeterminism

namespace Jihoo.CommonData
open HeapLeases LinearHeapPrograms RecursiveLexicalFields

/-- The result cannot consume the ambient frame, regardless of result kind. -/
theorem Post.frame_owned (post : Post kind s v frame) : Owns s.buffers.heap frame := by
  cases kind with
  | scalar => exact post.2
  | data => obtain ⟨tree,_,_,owned⟩ := post; exact OwnedApplicationFrame.owns_right owned

/-- Every common typing derivation, including nested partitioned applications,
constructs execution preserving the actual cells and lengths of its frame. -/
theorem Typing.total_preserving (typed : Typing g ctx count sizes term kind)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) ctx env)
    (layout : SizedBufferContext.Layout s.buffers owners sizes) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) :
    ∃ v es t, Eval g env term s v es t ∧ Steps s.buffers.heap es t.buffers.heap ∧
      Valid t.buffers.heap ∧ Post kind t v frame ∧
      (∀ x ∈ frame, t.cells x = s.cells x ∧ t.buffers.length x = s.buffers.length x) := by
  obtain ⟨v,es,t,run,steps,vt,post⟩ := typed.total length agreement layout valid owned fields
  refine ⟨v,es,t,run,steps,vt,post,?_⟩
  intro x member
  have before := OwnedApplicationFrame.owns_right owned
  have untouched := surviving_untouched valid steps
    (valid.allocated x (before.live x member)) (post.frame_owned.live x member)
  exact ⟨run.cells_frame untouched.1 untouched.2,run.lengths_frame untouched.1⟩

/-- The frame guarantee concerns every operational execution, not a selected
partition plan or a producer-supplied field-preservation certificate. -/
theorem Typing.every_run_preserving (typed : Typing g ctx count sizes term kind)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) ctx env)
    (layout : SizedBufferContext.Layout s.buffers owners sizes) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) (observed : Eval g env term s v es t) :
    Steps s.buffers.heap es t.buffers.heap ∧ Valid t.buffers.heap ∧ Post kind t v frame ∧
      (∀ x ∈ frame, t.cells x = s.cells x ∧ t.buffers.length x = s.buffers.length x) := by
  obtain ⟨w,fs,u,run,safe,vu,post,preserved⟩ :=
    typed.total_preserving length agreement layout valid owned fields
  obtain ⟨rfl,rfl,rfl⟩ := observed.deterministic run
  exact ⟨safe,vu,post,preserved⟩

end Jihoo.CommonData
