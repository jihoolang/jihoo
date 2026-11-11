import Jihoo.RecursiveCaseBody
import Jihoo.RecursiveLexicalFieldsExamples

namespace Jihoo.RecursiveCaseBodyExamples
open HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime
open RecursiveLexicalFields RecursiveBodyProjection RecursiveCaseBody
open RecursiveFieldRuntimeExamples (rightTree)
open RecursiveFieldOwnershipExamples (leaf)

/-- A hand-built graph in the existing Core constructor view. No Case/export
fidelity is asserted. Outer Buffer variables are at lexical slots 5 and 9. -/
def graph : ScopedLend.Graph.Graph := #[
  .natural 1, .natural 0, .buffer 0, .ref 2, .i64,
  .var 0, .decide 1 0, .index 5 1 6, .lam false 3 7,
  .var 1, .integer 99, .free 5 9, .lam false 2 11,
  .lam false 4 12, .lend 5 8 13, .lam false 2 14,
  .opaque, .var 7, .var 8, .alloc 17 18, .app 15 19,
  .var 9, .free 21 20, .var 5, .free 23 22, .var 0]

def parent : Tree := .node 0 (leaf 1) rightTree

def ctx : List Entry :=
  [.data 0, .buffer 1, .buffer 1, .nat 1, .scalar, .buffer 2, .buffer 2, .ghost]
def env : List Value :=
  [.data (some 0), .buffer 4, .buffer 4, .nat 1, .scalar 7, .buffer 5, .buffer 5, .ghost]

def start : RecursiveCaseBody.State :=
  ⟨⟨⟨6, 0, fun x => decide (x < 6), fun _ => 7, fun _ => none⟩,
    fun x => if x = 5 then 2 else 1⟩, RecursiveFieldRuntimeExamples.fixture.cells⟩

def opened := bindValues 2 ⟨some 1, some 2⟩ env

theorem agreement : Agrees [.data parent, .buffer 4, .buffer 5] ctx env :=
  .cons ⟨parent, rfl, rfl⟩ (.cons ⟨4, rfl, rfl⟩ (.cons ⟨4, rfl, rfl⟩
    (.cons rfl (.cons ⟨7, rfl⟩ (.cons ⟨5, rfl, rfl⟩ (.cons ⟨5, rfl, rfl⟩ (.cons rfl .nil)))))))

theorem initial_valid : SizedBufferHeap.Valid start.buffers := by
  constructor
  · intro x h; simpa [start] using h
  · intro l x h; simp [start] at h

theorem inventory : Inventory start.recursive [.data parent, .buffer 4, .buffer 5] := by
  constructor
  · constructor
    · decide
    · intro x h
      simp only [footprint, Capability.owners, parent, Tree.owners,
        leaf, rightTree, List.append_nil, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro x h l; simp [State.recursive, start]
  · intro c h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact RecursiveFieldRuntimeExamples.fields_fixture
    all_goals trivial

theorem layout : SizedBufferContext.Layout start.buffers [4,5] [1,2] := by
  constructor
  · rfl
  · intro k x n hx hn
    cases k with
    | zero => cases hx; cases hn; rfl
    | succ k => cases k with
      | zero => cases hx; cases hn; rfl
      | succ k => simp at hx

theorem read_shape : SizedCoreExecution.ReadLend graph 14 5 3 1 6 2 11 :=
  .intro rfl rfl rfl rfl rfl rfl rfl

theorem typed : SegmentTyping graph ctx [1,2] 25 0 2 24 := by
  refine ⟨rfl, rfl, ?_⟩
  apply SizedCoreTyping.Typing.free (slot := 0) rfl rfl rfl (by decide)
  apply SizedCoreTyping.Typing.free (slot := 0) rfl rfl rfl (by decide)
  apply SizedCoreTyping.Typing.allocate (function := 15) (argument := 19)
    (domain := 2) (length := 17) (init := 18) (n := 1) rfl rfl
  · exact ⟨0, rfl, DependentBufferIndices.Eval.literal rfl (by decide)⟩
  · rfl
  · exact DependentBufferIndices.Eval.var rfl rfl
  · exact .var rfl rfl
  · apply SizedCoreTyping.Typing.lend (slot := 0) (n := 1) (i := 0) read_shape rfl rfl rfl
    · exact ⟨2, rfl, 0, rfl, DependentBufferIndices.Eval.literal rfl (by decide)⟩
    · exact ⟨0, rfl, DependentBufferIndices.Eval.literal rfl (by decide)⟩
    · exact DependentBufferIndices.Eval.literal rfl (by decide)
    · exact .decide rfl rfl rfl (by decide) (by decide) rfl
    · exact .free (slot := 0) rfl rfl rfl (by decide) (.scalar rfl rfl)

def afterBody : RecursiveCaseBody.State :=
  ⟨SizedBufferHeap.release (SizedBufferHeap.restore
    (SizedBufferHeap.allocate (SizedBufferHeap.release (SizedBufferHeap.release start.buffers 4) 5) 1 7)) 6,
    start.cells⟩

def bodyEvents : List SizedBufferHeap.Event :=
  [.free 4, .free 5, .alloc 6 1 7, .beginLease 0 6, .read 0 0 7, .close 0, .free 6]

theorem body_run : BodyRun graph opened 24 start 7 bodyEvents afterBody := by
  apply BodyRun.core
  apply SizedCoreExecution.Eval.free rfl rfl rfl
  apply SizedCoreExecution.Eval.free rfl rfl rfl
  apply SizedCoreExecution.Eval.app rfl rfl
    (.allocate rfl (DependentBufferIndices.Eval.var rfl rfl) (.var rfl rfl))
  exact .lend read_shape rfl rfl (DependentBufferIndices.Eval.literal rfl (by decide))
    (.free rfl rfl rfl (.var rfl rfl))

theorem segment_run : SegmentRun graph env 25 2 24 start 7
    (bodyEvents ++ [SizedBufferHeap.Event.free 0]) (finish afterBody 0) :=
  .node rfl rfl body_run

theorem segment_safe :
    SizedBufferHeap.Steps start.buffers (bodyEvents ++ [SizedBufferHeap.Event.free 0]) (finish afterBody 0).buffers ∧
    SizedBufferHeap.Valid (finish afterBody 0).buffers ∧
    Inventory (finish afterBody 0).recursive [.data (leaf 1), .data rightTree] :=
  segment_every_run (owners := [4,5]) (parent := 0) typed agreement inventory layout initial_valid segment_run

theorem all_buffer_aliases_retired : continuation 2 (bindContext 2 ctx) =
    [.scalar, .data 1, .data 0, .ghost, .ghost,
     .dead, .dead, .dead, .nat 1, .scalar, .dead, .dead, .ghost] := rfl

theorem parent_only_freed_last :
    0 ∉ released (bodyEvents.map SizedBufferHeap.Event.project) ∧
      (released ((bodyEvents ++ [SizedBufferHeap.Event.free 0]).map SizedBufferHeap.Event.project)).count 0 = 1 := by decide

theorem parent_live_through_body : afterBody.buffers.heap.live 0 = true ∧
    (finish afterBody 0).buffers.heap.live 0 = false := by decide

theorem data_projected_dead : context 2 [.data 0, .data 1, .buffer 2] =
    [.dead, .dead, .owner 0] := rfl

theorem ghosts_supply_no_bound : SizedBufferContext.proofs (context 2 [.ghost, .ghost]) k = none := by
  cases k with
  | zero => rfl
  | succ k => cases k <;> rfl

theorem graph_valid : ScopedLend.Graph.valid graph = true := by decide

theorem cannot_free_data :
    ¬ SizedCoreTyping.Typing graph (context 2 [.data 0]) [1] 11 .scalar := by
  intro h
  have absent (k slot : Nat) : (context 2 [.data 0])[k]? ≠ some (.owner slot) := by
    cases k <;> simp [context, entry]
  cases h <;> first
    | solve_by_elim [absent]
    | simp [ScopedLend.Graph.nodeAt, graph] at *

theorem shared_data_buffer_rejected :
    ¬ Inventory start.recursive [.data parent, .buffer 2] := by
  intro h
  have distinct := h.1.distinct
  simp [footprint, Capability.owners, parent, Tree.owners, leaf, rightTree] at distinct

def noBuffers : RecursiveCaseBody.State :=
  ⟨⟨RecursiveFieldRuntimeExamples.fixture.heap, fun _ => 0⟩,
    RecursiveFieldRuntimeExamples.fixture.cells⟩

theorem empty_suffix_total : ∃ n es t,
    SegmentRun graph RecursiveLexicalFieldsExamples.environment 25 2 10 noBuffers n es t ∧
    Inventory t.recursive [.data (leaf 1), .data rightTree] := by
  have typing : SegmentTyping graph RecursiveLexicalFieldsExamples.context [] 25 0 2 10 :=
    ⟨rfl, rfl, .literal rfl (by decide)⟩
  have emptyLayout : SizedBufferContext.Layout noBuffers.buffers [] [] :=
    ⟨rfl, by intro k x n hx; simp at hx⟩
  obtain ⟨n, es, t, opened, _, run, _, _, children, _⟩ :=
    segment_total (s := noBuffers) (owners := []) (parent := 0) (left := leaf 1) (right := rightTree)
      typing RecursiveLexicalFieldsExamples.agrees_fixture
      RecursiveLexicalFieldsExamples.inventory_fixture emptyLayout RecursiveFieldRuntimeExamples.valid_fixture
  exact ⟨n, es, t, run, children⟩

end Jihoo.RecursiveCaseBodyExamples
