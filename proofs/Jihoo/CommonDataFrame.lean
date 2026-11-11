import Jihoo.CommonDataTyping

/-! Runtime frame contents are derived from actual events and heap safety.
No untouched-cell premise is imposed on typed application arguments. -/
namespace Jihoo.CommonData
open HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime
open RecursiveLexicalFields

/-- Buffer lengths can change only at identities explicitly allocated by a
sized execution, including fresh owned-reader results. -/
theorem sized_lengths_frame (run : SizedCoreExecution.Eval g env term s v es t)
    (fresh : x ∉ allocations (es.map SizedBufferHeap.Event.project)) :
    t.length x = s.length x := by
  induction run with
  | scalar _ | natural _ | var _ _ => rfl
  | app _ _ _ _ first last =>
    simp only [List.map_append, allocations, List.filterMap_append, List.mem_append, not_or] at fresh
    exact (last fresh.2).trans (first fresh.1)
  | allocate _ _ _ =>
    simp only [allocations, List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil, SizedBufferHeap.Event.project, List.mem_cons, List.not_mem_nil, or_false] at fresh
    simp [SizedBufferHeap.allocate, put, fresh]
  | free _ _ _ _ ih => exact ih (by simpa [allocations, SizedBufferHeap.Event.project] using fresh)
  | yes _ _ _ _ _ ih | no _ _ _ _ _ ih => exact ih fresh
  | lend _ _ _ _ _ ih =>
    exact ih (by simpa [allocations, SizedBufferHeap.Event.project] using fresh)
  | ownedLend _ _ _ _ _ _ ih =>
    simp only [SizedOwnedLend.events, List.map_append, List.map_cons, List.map_nil,
      allocations, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      SizedBufferHeap.Event.project] at fresh
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
    have eq := ih fresh.2
    simpa [SizedOwnedLend.final, SizedBufferHeap.allocate, SizedBufferHeap.restore, ScopedLend.restored, put, fresh.1] using eq

theorem Eval.lengths_frame (run : Eval g env term s v es t)
    (fresh : x ∉ allocations es) : t.buffers.length x = s.buffers.length x := by
  induction run with
  | core _ old => exact sized_lengths_frame old fresh
  | literal _ | empty _ | dataVar _ _ | construct _ _ _ _ _ => rfl
  | bufferLet _ _ _ old _ ih =>
    simp only [allocations, List.filterMap_append, List.mem_append, not_or] at fresh
    exact (ih fresh.2).trans (sized_lengths_frame old fresh.1)
  | dataLet _ _ _ _ _ first last =>
    simp only [allocations, List.filterMap_append, List.mem_append, not_or] at fresh
    exact (last fresh.2).trans (first fresh.1)
  | drop _ _ _ destroyed _ ih =>
    simp only [allocations, List.filterMap_append, List.mem_append, not_or] at fresh
    exact (ih fresh.2).trans (congrFun destroyed.lengths x)
  | emptyCase _ _ _ _ ih => exact ih fresh
  | nodeCase _ _ _ _ ih =>
    apply ih
    simpa [allocations, List.filterMap_append] using fresh

/-- Cells are changed only by fresh Data allocation or actual release events. -/
theorem Eval.cells_frame (run : Eval g env term s v es t)
    (fresh : x ∉ allocations es) (kept : x ∉ released es) : t.cells x = s.cells x := by
  induction run with
  | core _ _ | literal _ | empty _ | dataVar _ _ => rfl
  | construct _ _ _ _ _ =>
    simp only [allocations, List.filterMap_cons, List.filterMap_nil, List.mem_cons, List.not_mem_nil, or_false] at fresh
    simp [allocate, put, fresh]
  | bufferLet _ _ _ _ _ ih =>
    apply ih
    · exact fun h => fresh (by simp only [allocations, List.filterMap_append, List.mem_append]; exact Or.inr h)
    · exact fun h => kept (by simp only [released, List.filterMap_append, List.mem_append]; exact Or.inr h)
  | dataLet _ _ _ _ _ first last =>
    have fa : x ∉ allocations _ := fun h => fresh (by simp only [allocations, List.filterMap_append, List.mem_append]; exact Or.inl h)
    have fb : x ∉ allocations _ := fun h => fresh (by simp only [allocations, List.filterMap_append, List.mem_append]; exact Or.inr h)
    have ka : x ∉ released _ := fun h => kept (by simp only [released, List.filterMap_append, List.mem_append]; exact Or.inl h)
    have kb : x ∉ released _ := fun h => kept (by simp only [released, List.filterMap_append, List.mem_append]; exact Or.inr h)
    exact (last fb kb).trans (first fa ka)
  | drop _ _ _ destroyed _ ih =>
    have fb : x ∉ allocations _ := fun h => fresh (by simp only [allocations, List.filterMap_append, List.mem_append]; exact Or.inr h)
    have ka : x ∉ released _ := fun h => kept (by simp only [released, List.filterMap_append, List.mem_append]; exact Or.inl h)
    have kb : x ∉ released _ := fun h => kept (by simp only [released, List.filterMap_append, List.mem_append]; exact Or.inr h)
    exact (ih fb kb).trans (destroyed.cells_frame ka)
  | emptyCase _ _ _ _ ih => exact ih fresh kept
  | nodeCase _ _ _ _ ih =>
    simp only [released, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at kept
    have fa : x ∉ allocations _ := fun h => fresh (by simp only [allocations, List.filterMap_append, List.mem_append]; exact Or.inl h)
    simpa [finish, RecursiveCaseBody.finish, put, kept.2] using ih fa kept.1

/-- An initially allocated identity that is live after a safe execution has
neither been reallocated nor released (abstract identities are never reused). -/
theorem surviving_untouched (valid : Valid s) (run : Steps s es t)
    (old : x < s.nextObject) (live : t.live x = true) :
    x ∉ allocations es ∧ x ∉ released es := by
  constructor
  · intro member; have := OwnedApplicationFrame.allocations_fresh run member; omega
  · intro member
    have dead := released_dead valid run (released_mem.mp member)
    simp [live] at dead

/-- Heap frame survival strengthens to equality of actual recursive cells. -/
theorem Eval.frame_cells (run : Eval g env term s v es t)
    (valid : Valid s.buffers.heap) (safe : Steps s.buffers.heap es t.buffers.heap)
    (before : Owns s.buffers.heap frame) (after : Owns t.buffers.heap frame)
    (member : x ∈ frame) : t.cells x = s.cells x := by
  obtain ⟨fresh,kept⟩ := surviving_untouched valid safe
    (valid.allocated x (before.live x member)) (after.live x member)
  exact run.cells_frame fresh kept

/-- Whole finite tree interpretations survive, not only their root liveness. -/
theorem Eval.frame_fields (run : Eval g env term s v es t)
    (valid : Valid s.buffers.heap) (safe : Steps s.buffers.heap es t.buffers.heap)
    (before : Owns s.buffers.heap (footprint retained))
    (after : Owns t.buffers.heap (footprint retained)) (fields : Fields s.cells retained) :
    Fields t.cells retained := by
  intro c member
  cases c with
  | buffer _ => trivial
  | data tree =>
    apply (fields (.data tree) member).congr
    intro x hx
    exact run.frame_cells valid safe before after (footprint_member member hx)

/-- Reserved Buffer capabilities retain their exact dynamic length layout. -/
theorem Eval.frame_layout (run : Eval g env term s v es t)
    (valid : Valid s.buffers.heap) (safe : Steps s.buffers.heap es t.buffers.heap)
    (owned : Owns s.buffers.heap owners) (layout : SizedBufferContext.Layout s.buffers owners sizes) :
    SizedBufferContext.Layout t.buffers owners sizes := by
  refine ⟨layout.length, ?_⟩
  intro k x n hx hn
  have old := valid.allocated x (owned.live x (List.mem_of_getElem? hx))
  have fresh : x ∉ allocations es := by
    intro member; have := OwnedApplicationFrame.allocations_fresh safe member; omega
  exact (run.lengths_frame fresh).trans (layout.lookup k x n hx hn)

end Jihoo.CommonData
