import Jihoo.CommonDataPartitionChecks
import Jihoo.CommonDataAccounting
import Jihoo.SizedCompositionExamples

namespace Jihoo.CommonDataAccountingChecks
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
open HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime
open RecursiveLexicalFields CommonData
open CommonDataExamples (start parent)
open CommonDataDropExamples (input_owned input_fields)
open RecursiveFieldOwnershipExamples (leaf)
open RecursiveFieldRuntimeExamples (rightTree)

private theorem agreement : Agrees (caps [parent] []) [.data 0] [.data (some 0)] :=
  .cons ⟨parent,rfl,rfl⟩ .nil

/-- Rebuild then Drop accounts for both the original parent and the freshly
allocated replacement, together with every descendant. -/
theorem computed_drop_accounted :
    Account [0,1,2,3] [] [.alloc 7 0,.free 0,.free 7,.free 1,.free 2,.free 3] := by
  have post := CommonDataApplicationExamples.rebuild_then_drop_typed.every_run_accounted
    (trees := [parent]) (owners := []) rfl agreement empty_layout
    CommonDataExamples.valid_start input_owned input_fields CommonDataApplicationExamples.drop_run
  exact post.account_for (output := []) rfl

theorem fresh_replacement_released :
    (released [.alloc 7 0,.free 0,.free 7,.free 1,.free 2,.free 3]).count 7 = 1 ∧
      CommonDataApplicationExamples.dropped.buffers.heap.live 7 = false :=
  CommonDataApplicationExamples.rebuild_then_drop_typed.other_released
    (trees := [parent]) (owners := []) rfl agreement empty_layout
    CommonDataExamples.valid_start input_owned input_fields CommonDataApplicationExamples.drop_run
    (output := []) rfl (Or.inr (by decide)) (by simp)

/-- Returning a tree returns all its descendants, not just root 8. -/
theorem rebuilt_descendants_accounted :
    Account [0,1,2,3] [8,1,2,3] [.alloc 7 0,.free 0,.alloc 8 0,.free 7] := by
  have post := CommonDataApplicationExamples.rebuild_twice_typed.every_run_accounted
    (trees := [parent]) (owners := []) rfl agreement empty_layout
    CommonDataExamples.valid_start input_owned input_fields CommonDataApplicationExamples.twice_run
  apply post.account_for
  exact ⟨.node 8 (leaf 1) rightTree,rfl,⟨rfl,⟨rfl,trivial,trivial⟩,⟨rfl,⟨rfl,trivial,trivial⟩,trivial⟩⟩,rfl⟩

/-- Nested Cases free both pending shells while returning the right subtree. -/
theorem nested_shells_accounted : Account [0,1,2,3] [2,3] [.free 1,.free 0] := by
  have post := CommonDataDropExamples.nested_case_typed.every_run_accounted
    (trees := [parent]) (owners := []) rfl agreement empty_layout
    CommonDataExamples.valid_start input_owned input_fields CommonDataDropExamples.nested_case_run
  exact post.account_for ⟨rightTree,rfl,CommonDataDropExamples.sibling_fields,rfl⟩

private theorem split_owned :
    Owns start.buffers.heap (footprint (caps [leaf 1,rightTree] []) ++ [0,4,5,6]) := by
  apply owns_permute CommonDataExamples.owns_start
  decide

private theorem split_fields : Fields start.cells (caps [leaf 1,rightTree] []) := by
  intro c member
  simp [caps] at member
  rcases member with rfl | rfl
  · exact RecursiveFieldRuntimeExamples.fields_fixture.2.1
  · exact RecursiveFieldRuntimeExamples.fields_fixture.2.2

/-- Partitioned application counts retained captures once in the final tree. -/
theorem split_return_accounted : Account [1,2,3] [8,7,2,3] [.alloc 7 0,.free 1,.alloc 8 0] := by
  have post := CommonDataPartitionChecks.reassemble_typed.every_run_accounted
    (trees := [leaf 1,rightTree]) (owners := []) rfl
    (.cons ⟨leaf 1,rfl,rfl⟩ (.cons ⟨rightTree,rfl,rfl⟩ .nil)) empty_layout
    CommonDataExamples.valid_start split_owned split_fields CommonDataPartitionChecks.nonempty_captures_run
  apply post.account_for
  exact ⟨.node 8 (leaf 7) rightTree,rfl,⟨rfl,⟨rfl,trivial,trivial⟩,⟨rfl,⟨rfl,trivial,trivial⟩,trivial⟩⟩,rfl⟩

/-- The final live set includes returned descendants and the declared frame. -/
theorem split_live_domain :
    ∀ x, CommonDataPartitionChecks.combined.buffers.heap.live x = true ↔ x ∈ [8,7,2,3,0,4,5,6] := by
  apply CommonDataPartitionChecks.reassemble_typed.live_domain
    (trees := [leaf 1,rightTree]) (owners := []) (frame := [0,4,5,6]) rfl
    (.cons ⟨leaf 1,rfl,rfl⟩ (.cons ⟨rightTree,rfl,rfl⟩ .nil)) empty_layout
    CommonDataExamples.valid_start split_owned split_fields CommonDataPartitionChecks.nonempty_captures_run
    (output := [8,7,2,3])
  · exact ⟨.node 8 (leaf 7) rightTree,rfl,⟨rfl,⟨rfl,trivial,trivial⟩,⟨rfl,⟨rfl,trivial,trivial⟩,trivial⟩⟩,rfl⟩
  · intro x live
    have bound : x < 7 := by simpa [CommonDataExamples.start] using live
    simp [caps,footprint,Capability.owners,leaf,rightTree,Tree.owners]
    omega

/-- A literal consumes no tracked allocation. Without initial coverage an
untracked live object can remain, so unconditional whole-heap emptiness is false. -/
theorem untracked_survives :
    Typing CommonDataPartitionChecks.graph [] 0 [] 6 .scalar ∧
    Eval CommonDataPartitionChecks.graph [] 6 start (.scalar 99) [] start ∧
    start.buffers.heap.live 6 = true ∧
    ¬ (∀ x, start.buffers.heap.live x = true → x ∈ ([] : List Nat)) := by
  refine ⟨.literal rfl (by decide),.literal rfl,rfl,?_⟩
  intro coverage
  have impossible := coverage 6 rfl
  simp at impossible

/-- Allocation accounting intentionally does not observe empty logical slots. -/
theorem empty_footprint_limit : Account [] [] [] ∧
    footprint (caps [Tree.empty] []) = footprint (caps [Tree.empty,Tree.empty] []) :=
  ⟨Account.refl,rfl⟩

/-- A hand-wrapped common graph projects exactly to the existing sized graph.
The embedded node occupies an unused opaque slot, not a new native export. -/
def bufferGraph : CommonData.Graph :=
  (SizedCompositionGraph.graph.map CommonData.Node.core).setIfInBounds 86 (.embedded 81)

theorem buffer_projection : coreGraph bufferGraph = SizedCompositionGraph.graph := by
  simp only [coreGraph,bufferGraph,Array.map_setIfInBounds,Array.map_map,
    Function.comp_def,projectNode]
  change (SizedCompositionGraph.graph.map id).setIfInBounds 86 .opaque = _
  rw [Array.map_id]
  apply Array.ext
  · simp
  · intro i hi hj
    rw [Array.getElem_setIfInBounds hj]
    split
    · next eq => subst i; rfl
    · rfl

private theorem buffer_shape : nodeAt bufferGraph 86 = .embedded 81 := by
  simp [nodeAt,bufferGraph,
    show 86 < SizedCompositionGraph.graph.size by decide]

def bufferContext (n m i : Nat) : List Entry := [.scalar,.nat i,.nat m,.nat n]
def bufferEnv (n m i value : Nat) : List Value := [.scalar value,.nat i,.nat m,.nat n]
def bufferStart : CommonData.State := ⟨SizedBufferHeap.empty,fun _ => none⟩

/-- Existing owned-result readers and their fresh allocations are included by
reuse of the sized typing derivation inside the common accounted theorem. -/
theorem buffer_reader_typed (n m i : Nat) : Typing bufferGraph (bufferContext n m i) 0 [] 86 .scalar := by
  apply Typing.core (body := 81) buffer_shape
  rw [buffer_projection]
  exact SizedCompositionExamples.body_typed n m i

theorem buffer_reader_accounted (n m i value : Nat) :
    ∃ events t, Eval bufferGraph (bufferEnv n m i value) 86 bufferStart
      (.scalar (if i < n then value else 99)) events t ∧ Account [] [] events ∧
      (∀ x, t.buffers.heap.live x = false) := by
  obtain ⟨events,t,old⟩ := SizedCompositionExamples.body_value_run n m i value
  have run : Eval bufferGraph (bufferEnv n m i value) 86 bufferStart
      (.scalar (if i < n then value else 99)) (events.map SizedBufferHeap.Event.project) ⟨t,bufferStart.cells⟩ := by
    apply Eval.core (body := 81) buffer_shape
    rw [buffer_projection]
    exact old
  have agrees : Agrees (caps [] []) (bufferContext n m i) (bufferEnv n m i value) :=
    .cons ⟨value,rfl⟩ (.cons rfl (.cons rfl (.cons rfl .nil)))
  have fields : Fields bufferStart.cells (caps [] []) := by intro c hc; simp [caps] at hc
  have owned : Owns bufferStart.buffers.heap (footprint (caps [] [])) := LinearHeapPrograms.empty_owns
  have valid : Valid bufferStart.buffers.heap := HeapLeases.empty_valid
  have coverage : ∀ x, bufferStart.buffers.heap.live x = true → x ∈ footprint (caps [] []) := by
    intro x live; cases live
  have counted := (buffer_reader_typed n m i).every_run_accounted (frame := [])
    (trees := []) (owners := []) rfl agrees empty_layout valid (by simpa using owned) fields run
  exact ⟨_,_,run,counted.account_for rfl,
    (buffer_reader_typed n m i).scalar_no_leaks rfl agrees empty_layout valid owned fields run coverage⟩

end Jihoo.CommonDataAccountingChecks
