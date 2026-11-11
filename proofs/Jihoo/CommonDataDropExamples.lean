import Jihoo.CommonDataChecks

namespace Jihoo.CommonDataDropExamples
open HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime
open RecursiveLexicalFields CommonData
open CommonDataExamples (start parent)
open RecursiveFieldRuntimeExamples (rightTree)
open RecursiveFieldOwnershipExamples (leaf)

/-- Drop has the original Core family/owner/rest argument order. Family 0 is
only the specified binary family; these are not compiler-exported nodes. -/
def graph : CommonData.Graph := #[
  .core (.integer 99), .embedded 0, .core (.var 0), .drop 0 2 1,
  .core (.var 1), .core (.var 2), .drop 0 2 5, .drop 0 4 6,
  .caseTree 4 2 7 0, .empty, .caseTree 2 9 8 0,
  .drop 0 4 2, .caseTree 2 9 11 0, .drop 1 2 1,
  .core (.var 1), .core (.free 14 0), .embedded 15, .drop 0 2 16]

theorem graph_valid : validGraph graph = true := by decide

theorem drop_typed : Typing graph [.data 0] 1 [] 3 .scalar :=
  .drop rfl rfl rfl (.core rfl (.literal (v := 99) (by rw [core_at]; rfl) (by decide)))

def destroyed := finish (finish (finish (finish start 0) 1) 2) 3

theorem destroy_run : Destroy (some 0) start [.free 0,.free 1,.free 2,.free 3] destroyed :=
  .node (left := [.free 1]) (right := [.free 2,.free 3]) rfl
    (.node (left := []) (right := []) rfl .empty .empty)
    (.node (left := [.free 3]) (right := []) rfl
      (.node (left := []) (right := []) rfl .empty .empty) .empty)

theorem drop_run : Eval graph [.data (some 0)] 3 start (.scalar 99)
    [.free 0,.free 1,.free 2,.free 3] destroyed :=
  .drop rfl rfl rfl destroy_run (.core rfl (.scalar (v := 99) (by rw [core_at]; rfl)))

theorem input_owned : Owns start.buffers.heap (parent.owners ++ [4,5,6]) :=
  CommonDataExamples.owns_start

theorem drop_safe : Steps start.buffers.heap [.free 0,.free 1,.free 2,.free 3]
    destroyed.buffers.heap ∧ Valid destroyed.buffers.heap ∧ Owns destroyed.buffers.heap [4,5,6] := by
  have result := destroy_every_run (tree := parent) (frame := [4,5,6])
    RecursiveFieldRuntimeExamples.fields_fixture CommonDataExamples.valid_start input_owned destroy_run
  exact result.2

theorem empty_drop_run : Eval graph [.data none] 3 start (.scalar 99) [] start :=
  .drop rfl rfl rfl .empty (.core rfl (.scalar (v := 99) (by rw [core_at]; rfl)))

theorem nested_case_typed : Typing graph [.data 0] 1 [] 10 .data := by
  apply Typing.caseTree (count := 0) rfl rfl rfl
  · exact .empty rfl
  · apply Typing.caseTree (count := 1) rfl rfl rfl
    · exact .dataVar rfl rfl
    · exact .drop rfl rfl rfl (.drop rfl rfl rfl (.dataVar rfl rfl))

theorem nested_case_run : Eval graph [.data (some 0)] 10 start (.data (some 2))
    [.free 1,.free 0] (finish (finish start 1) 0) := by
  exact .nodeCase rfl rfl rfl
    (.nodeCase rfl rfl rfl (.drop rfl rfl rfl .empty
      (.drop rfl rfl rfl .empty (.dataVar rfl rfl))))

theorem drop_child_typed : Typing graph [.data 0] 1 [] 12 .data :=
  .caseTree (count := 0) rfl rfl rfl (.empty rfl)
    (.drop rfl rfl rfl (.dataVar rfl rfl))

theorem drop_child_run : Eval graph [.data (some 0)] 12 start (.data (some 2))
    [.free 1,.free 0] (finish (finish start 1) 0) :=
  .nodeCase rfl rfl rfl
    (.drop rfl rfl rfl (.node (left := []) (right := []) rfl .empty .empty) (.dataVar rfl rfl))

theorem input_fields : Fields start.cells (caps [parent] []) := by
  intro c member
  simp [caps] at member
  subst c
  exact RecursiveFieldRuntimeExamples.fields_fixture

theorem nested_case_safe : Steps start.buffers.heap [.free 1,.free 0]
    (finish (finish start 1) 0).buffers.heap ∧
    Valid (finish (finish start 1) 0).buffers.heap ∧
    Post .data (finish (finish start 1) 0) (.data (some 2)) [4,5,6] :=
  nested_case_typed.every_run (trees := [parent]) (owners := []) rfl
    (.cons ⟨parent,rfl,rfl⟩ .nil) empty_layout CommonDataExamples.valid_start input_owned input_fields nested_case_run

theorem sibling_fields : Represents (finish (finish start 1) 0).cells rightTree := by
  simp [Represents,finish,RecursiveCaseBody.finish,start,rightTree,leaf,root,put,
    RecursiveFieldRuntimeExamples.fixture]

theorem wrong_family_rejected : ¬ Typing graph [.data 0] 1 [] 13 .scalar := by
  intro typed
  cases typed <;> simp_all [nodeAt,graph]

theorem all_aliases_retired : removeHead [.data 0,.data 0,.data 1,.buffer 2] =
    [.dead,.dead,.data 0,.buffer 1] := rfl

theorem missing_cell_rejected : ¬ Destroy (some 0) { start with cells := fun _ => none } es t := by
  intro run
  cases run with
  | node cell _ _ => cases cell

theorem shared_child_ownership_rejected :
    ¬ Owns start.buffers.heap ((Tree.node 0 (leaf 1) (leaf 1)).owners ++ [6]) := by
  intro h
  have distinct := h.distinct
  simp [Tree.owners,leaf] at distinct

theorem drop_projects_opaque : ScopedLend.Graph.nodeAt (coreGraph graph) 3 = .opaque := by
  rw [core_at]; rfl

theorem leased_child_rejected :
    ¬ Owns { start.buffers.heap with lease := fun _ => some 1 } (parent.owners ++ [6]) := by
  intro h
  have absent := h.leaseFree 1 (by decide) 0
  simp at absent

theorem stale_alias_rejected : ¬ Typing graph (removeHead [.data 0,.data 0]) 0 [] 2 .data := by
  intro typed
  cases typed <;> simp_all [nodeAt,graph,removeHead,removeEntry]

theorem buffer_continuation_typed : Typing graph [.data 0,.buffer 1] 1 [1] 17 .scalar := by
  apply Typing.drop (count := 0) rfl rfl rfl
  apply Typing.core rfl
  exact .free (owner := 14) (body := 0) (k := 1) (slot := 0)
    (by rw [core_at]; rfl) (by rw [core_at]; rfl) rfl (by decide)
    (.literal (v := 99) (by rw [core_at]; rfl) (by decide))

theorem buffer_continuation_run : Eval graph [.data (some 0),.buffer 4] 17 start (.scalar 99)
    [.free 0,.free 1,.free 2,.free 3,.free 4]
    ⟨SizedBufferHeap.release destroyed.buffers 4,destroyed.cells⟩ :=
  .drop rfl rfl rfl destroy_run (.core (g := graph) (body := 15) rfl
    (.free (owner := 14) (body := 0) (k := 1) (by rw [core_at]; rfl)
      (by rw [core_at]; rfl) rfl (.scalar (v := 99) (by rw [core_at]; rfl))))

theorem buffer_continuation_safe :
    Steps start.buffers.heap [.free 0,.free 1,.free 2,.free 3,.free 4]
      (SizedBufferHeap.release destroyed.buffers 4).heap ∧
    Valid (SizedBufferHeap.release destroyed.buffers 4).heap ∧
    Owns (SizedBufferHeap.release destroyed.buffers 4).heap [5,6] := by
  have layout : SizedBufferContext.Layout start.buffers [4] [1] := by
    constructor
    · rfl
    · intro k x n hx hn
      cases k with
      | zero => cases hx; cases hn; rfl
      | succ k => simp at hx
  have fields : Fields start.cells (caps [parent] [4]) := by
    intro c member
    simp [caps] at member
    rcases member with rfl | rfl
    · exact RecursiveFieldRuntimeExamples.fields_fixture
    · trivial
  have result := buffer_continuation_typed.every_run (trees := [parent]) (owners := [4])
    (frame := [5,6]) rfl (.cons ⟨parent,rfl,rfl⟩ (.cons ⟨4,rfl,rfl⟩ .nil))
    layout CommonDataExamples.valid_start input_owned fields buffer_continuation_run
  exact ⟨result.1,result.2.1,result.2.2.2⟩

end Jihoo.CommonDataDropExamples
