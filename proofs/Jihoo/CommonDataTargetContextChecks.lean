import Jihoo.CommonDataTargetContext
import Jihoo.CommonDataReferenceChecks

namespace Jihoo.CommonDataTargetContext.Checks
open CommonDataReference RecursiveLexicalFields ReferenceCfg
open CommonDataReferenceChecks (image buffer source source_valid related)

def heap : ReferenceHeap.Heap := CommonDataReferenceChecks.heap ++
  #[ReferenceHeap.nilObject, ⟨false, #[some (.scalar 91)]⟩]
def ctx : List Entry := [.data 0, .data 0, .data 1, .buffer 2, .scalar, .nat 9]
def env : List RecursiveLexicalFields.Value := [.data (some 7), .data (some 7), .data none, .buffer 4, .scalar 77, .nat 9]
def slots : List Nat := [0, 0, 1, 2, 3, 4]
def caller : ReferenceCalls.Function :=
  ⟨TreeDropCall.compileDrop
    ⟨⟨#[.ptr, .ptr, .ptr, .i64, .u64, .unit, .ptr, .ptr], #[⟨#[], .ret⟩]⟩, #[some .retUnit]⟩
    2 (TreeDropCall.arg 0) 5 0, #[]⟩
def program : ReferenceCalls.Program := #[caller, caller, TreeDropCall.body 2]
def entry : ReferenceCalls.State := ⟨1, ⟨1, 0,
  #[some (.pointer 3 0), some (.pointer 4 0), some (.pointer 0 0),
    some (.i64 77), some (.u64 9), none, some (.pointer 1 0), some (.pointer 2 0)], heap⟩, []⟩

theorem initial : CommonContext [image, .nil 4] [(4,0)] [2] [] [] [10]
    ctx env slots source entry.frame := by
  constructor
  · constructor
    · exact source_valid
    · exact .cons ⟨_, rfl, rfl⟩ (.cons ⟨_, rfl, rfl⟩
        (.cons ⟨_, rfl, rfl⟩ (.cons ⟨_, rfl, rfl⟩ (.cons ⟨_, rfl⟩ (.cons rfl .nil)))))
    · exact .cons ⟨_, rfl, rfl⟩ (.cons ⟨_, rfl, rfl⟩
        (.cons ⟨_, rfl, rfl⟩ (.cons ⟨_, _, rfl, rfl⟩ (.cons ⟨_, rfl⟩ (.cons rfl .nil)))))
    · intro r member
      simp only [inventory, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact related.push ReferenceHeap.nilObject |>.push ⟨false, #[some (.scalar 91)]⟩
      · refine ⟨trivial, ?_, rfl, by decide⟩
        exact ⟨by simp [Image.source, RecursiveFieldOwnership.Tree.owners],
          by simp [Image.source, RecursiveFieldOwnership.Tree.owners],
          by simp [Image.source, RecursiveFieldOwnership.Tree.owners]⟩
      · exact CommonDataReferenceChecks.retained_buffer.push ReferenceHeap.nilObject |>.push ⟨false, #[some (.scalar 91)]⟩
    · refine ⟨by decide, ?_, ?_⟩
      · intro x hx
        change x ∈ [7,4] at hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> rfl
      · simp [source, HeapLeases.Unborrowed]
    · decide
    · intro a ha; cases ha
  · exact ⟨rfl, by intro k x n hx hn; cases k <;> simp_all [source]⟩

theorem site : TreeDropCall.Site program entry 5 0 := ⟨⟨caller, rfl, by decide, rfl⟩, by decide⟩
theorem installed : program[2]? = some (TreeDropCall.body 2) := rfl

theorem callAt : ∀ slot, slots[0]? = some slot → ∃ fn, program[entry.function]? = some fn ∧
    ReferenceCalls.extension fn.code entry.frame = some (.call
      (TreeDropCall.call 2 (TreeDropCall.arg slot) 5 0)) := by
  intro slot hs
  have eq : slot = 0 := by simpa [slots] using hs.symm
  subst slot
  exact ⟨caller, rfl, rfl⟩

theorem fresh : Fresh (CommonData.removeHead ctx) slots 5 := by
  intro k e slot he hs _
  have member := List.mem_of_getElem? hs
  simp [slots] at member
  omega

/-- Nontrivial continuation typing: drop retained Nil, free Buffer, return scalar. -/
def graph : CommonData.Graph := #[.core (.var 0), .core (.var 2), .core (.var 3),
  .core (.integer 7), .core (.free 2 3), .drop 0 1 4, .drop 0 0 5]

theorem typed : CommonData.Typing graph ctx 2 [2] 6 .scalar := by
  apply CommonData.Typing.drop (index := 0) rfl rfl rfl
  apply CommonData.Typing.drop (index := 2) rfl rfl rfl
  apply CommonData.Typing.freeBuffer (index := 3) (slot := 0) rfl rfl rfl (by decide)
  exact CommonData.Typing.literal rfl (by decide)

/-- The final theorem actually supplies both executions and continuation context. -/
theorem typed_boundary :
    CommonData.Typing graph (CommonData.removeHead ctx) 1 [2] 5 .scalar ∧
    ∃ middle K,
      CommonData.Destroy (RecursiveFieldRuntime.root image.source) source
        (image.source.owners.map HeapLeases.Event.free) middle ∧
      ReferenceCalls.Steps program (.running entry) (image.ids.map HeapLifecycle.Event.free)
        (.running (TreeDropCall.resume entry 5 0 K)) ∧
      CommonContext [.nil 4] [(4,0)] [2] [] [] [10] (CommonData.removeHead ctx) env slots middle
        (TreeDropCall.resume entry 5 0 K).frame ∧
      (∀ j, K[j]? = if j ∈ image.ids then entry.frame.heap[j]?.map deadObject else entry.frame.heap[j]?) :=
  typed_drop_prefix initial typed rfl rfl installed site callAt fresh (by decide : 0+1+image.depth ≤ 3)

theorem stale_aliases : ∀ K,
    (TreeDropCall.resume entry 5 0 K).frame.locals[0]? = some (some (.pointer 3 0)) ∧
    (CommonData.removeHead ctx)[0]? = some .dead ∧ (CommonData.removeHead ctx)[1]? = some .dead := by
  intro K; exact ⟨rfl, rfl, rfl⟩

theorem duplicate_nil_rejected : ¬ (targets [.data (.nil 1), .data (.nil 1)]).Nodup := by decide
theorem data_buffer_overlap_rejected : ¬ (targets [.data (.nil 1), .buffer 4 1]).Nodup := by decide

theorem scalar_destination_rejected : ¬ Fresh (CommonData.removeHead ctx) slots 3 := by
  intro h; exact h 4 .scalar 3 rfl rfl trivial rfl

theorem nat_destination_rejected : ¬ Fresh (CommonData.removeHead ctx) slots 4 := by
  intro h; exact h 5 (.nat 9) 4 rfl rfl trivial rfl

/-- Ghost binder has no target-local allocation requirement. -/
theorem case_children :
    Context [.data (.nil 1), .data (.nil 2), .data (.nil 4), .buffer 4 0]
      [⟨7,3,image.object⟩] [] [10] (bindContext 1 ctx)
      (bindValues 1 ⟨none,none⟩ env) (7 :: 6 :: 99 :: slots) source entry.frame :=
  (initial.toContext.open_case (k := 0) rfl (leftSlot := 6) rfl (rightSlot := 7) rfl [99]).2.2



/-- A child Nil Drop preserves the pending parent even though its saved child
reference now points at a dead box. Source empty destruction stutters. -/
theorem pending_after_child :
    Context [.data (.nil 2), .data (.nil 4), .buffer 4 0] [⟨7,3,image.object⟩] [] [10]
      (CommonData.removeHead (bindContext 1 ctx)) (bindValues 1 ⟨none,none⟩ env)
      (7 :: 6 :: 99 :: slots) source
      (TreeDropCall.resume entry 5 0 (retired heap 1 ReferenceHeap.nilObject)).frame := by
  apply case_children.after_drop (i := .nil 1) CommonData.Destroy.empty
  · exact Frees.cons (by decide +kernel) Frees.nil
  · intro k e slot _ hs _
    have member := List.mem_of_getElem? hs
    simp [slots] at member
    omega

theorem pending_shell_still_live :
    (retired heap 1 ReferenceHeap.nilObject)[3]? = some image.object ∧
    ReferenceHeap.loadScalar (retired heap 1 ReferenceHeap.nilObject) (.object 1 0) = none := by
  decide +kernel

theorem dead_absent_external_frame : ∃ K : ReferenceHeap.Heap,
    K[5]? = some ⟨false, #[some (.scalar 91)]⟩ ∧ K[10]? = none := by
  obtain ⟨_, _, K, _, _, _, effect⟩ := typed_boundary
  refine ⟨K, ?_, ?_⟩
  · simpa [image, Image.ids, entry, heap, CommonDataReferenceChecks.heap] using effect 5
  · simpa [image, Image.ids, entry, heap, CommonDataReferenceChecks.heap] using effect 10

/-- A zero-length buffer is live although no element load is possible. -/
theorem zero_buffer : BufferRelated {source with buffers := {source.buffers with length := fun _ => 0}}
    #[⟨true, #[]⟩] 4 0 := by
  constructor <;> rfl

end Jihoo.CommonDataTargetContext.Checks
