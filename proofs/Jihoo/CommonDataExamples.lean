import Jihoo.CommonDataDeterminism
import Jihoo.RecursiveCaseBodyExamples

namespace Jihoo.CommonDataExamples
open HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime
open RecursiveLexicalFields RecursiveBodyProjection CommonData
open RecursiveFieldRuntimeExamples (rightTree)
open RecursiveFieldOwnershipExamples (leaf)

local macro "core_shape" : term => `(by first | rfl | (rw [core_at]; rfl))

/-- A hand-built extension graph. Existing Core IDs 0..25 are retained, with
Case/construct/empty and scalar-let continuation nodes added above them. -/
def graph : CommonData.Graph := #[
  .core (.natural 1),
  .core (.natural 0),
  .core (.buffer 0),
  .core (.ref 2),
  .core (.i64),
  .core (.var 0),
  .core (.decide 1 0),
  .core (.index 5 1 6),
  .core (.lam false 3 7),
  .core (.var 1),
  .core (.integer 99),
  .core (.free 5 9),
  .core (.lam false 2 11),
  .core (.lam false 4 12),
  .core (.lend 5 8 13),
  .core (.lam false 2 14),
  .core (.opaque),
  .core (.var 7),
  .core (.var 8),
  .core (.alloc 17 18),
  .core (.app 15 19),
  .core (.var 9),
  .core (.free 21 20),
  .core (.var 5),
  .core (.free 23 22),
  .core (.var 0),
  .core (.var 2),
  .core (.var 1),
  .construct 26 27,
  .core (.lam false 4 28),
  .core (.app 29 24),
  .empty,
  .core .opaque,
  .core (.var 1),
  .core (.var 5),
  .core (.free 34 10),
  .core (.free 33 35),
  .core (.lam false 4 31),
  .core (.app 37 36),
  .caseTree 25 38 30 2]

abbrev ctx := RecursiveCaseBodyExamples.ctx
abbrev env := RecursiveCaseBodyExamples.env
abbrev parent := RecursiveCaseBodyExamples.parent
abbrev opened := RecursiveCaseBodyExamples.opened

theorem graph_valid : validGraph graph = true := by decide

theorem read_shape : SizedCoreExecution.ReadLend (coreGraph graph) 14 5 3 1 6 2 11 :=
  .intro (reader := 8) (cont := 13) (readRoot := 7) (operand := 5) (scalarTy := 4) (inner := 12) core_shape core_shape core_shape core_shape core_shape core_shape core_shape

theorem node_buffer_typed : SizedCoreTyping.Typing (coreGraph graph)
    (context 2 (bindContext 2 ctx)) [1,2] 24 .scalar := by
  apply SizedCoreTyping.Typing.free (owner := 23) (body := 22) (k := 5) (slot := 0) core_shape core_shape core_shape (by decide)
  apply SizedCoreTyping.Typing.free (owner := 21) (body := 20) (k := 9) (slot := 0) core_shape core_shape core_shape (by decide)
  apply SizedCoreTyping.Typing.allocate (function := 15) (argument := 19)
    (domain := 2) (length := 17) (init := 18) (n := 1) core_shape core_shape
  · exact ⟨0, core_shape, DependentBufferIndices.Eval.literal core_shape (by decide)⟩
  · exact core_shape
  · exact DependentBufferIndices.Eval.var core_shape core_shape
  · exact .var core_shape core_shape
  · apply SizedCoreTyping.Typing.lend (slot := 0) (n := 1) (i := 0) read_shape core_shape core_shape core_shape
    · exact ⟨2, core_shape, 0, core_shape, DependentBufferIndices.Eval.literal core_shape (by decide)⟩
    · exact ⟨0, core_shape, DependentBufferIndices.Eval.literal core_shape (by decide)⟩
    · exact DependentBufferIndices.Eval.literal core_shape (by decide)
    · exact .decide core_shape core_shape core_shape (by decide) (by decide) core_shape
    · exact .free (slot := 0) core_shape core_shape core_shape (by decide) (.scalar core_shape core_shape)

theorem nil_buffer_typed : SizedCoreTyping.Typing (coreGraph graph)
    (context 0 (removeHead ctx)) [1,2] 36 .scalar :=
  .free (owner := 33) (body := 35) (k := 1) (slot := 0) core_shape core_shape core_shape (by decide)
    (.free (owner := 34) (body := 10) (k := 5) (slot := 0) core_shape core_shape core_shape (by decide) (.literal (v := 99) core_shape (by decide)))

/-- Both actual branches share the common Data result. Node branch returns
one new tree containing both original subtrees; no child inventory escapes. -/
theorem case_typed : Typing graph ctx 1 [1,2] 39 .data := by
  apply Typing.caseTree (count := 0) rfl rfl rfl
  · exact .bufferLet rfl rfl rfl nil_buffer_typed (.empty rfl)
  · exact .bufferLet rfl rfl rfl node_buffer_typed (.construct rfl rfl rfl rfl rfl)

/-- Object 6 is an external pending frame, never a Buffer input. -/
def start : CommonData.State :=
  ⟨⟨⟨7, 0, fun x => decide (x < 7), fun _ => 7, fun _ => none⟩,
    fun x => if x = 5 then 2 else 1⟩, RecursiveFieldRuntimeExamples.fixture.cells⟩

theorem valid_start : Valid start.buffers.heap := by
  constructor
  · intro x h; simpa [start] using h
  · intro l x h; simp [start] at h

theorem owns_start : Owns start.buffers.heap (footprint (caps [parent] [4,5]) ++ [6]) := by
  constructor
  · decide
  · intro x h
    change x ∈ [0,1,2,3,4,5,6] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro x h l; simp [start]

theorem fields_start : Fields start.cells (caps [parent] [4,5]) :=
  RecursiveCaseBodyExamples.inventory.2

theorem layout_start : SizedBufferContext.Layout start.buffers [4,5] [1,2] := by
  constructor
  · rfl
  · intro k x n hx hn
    cases k with
    | zero => cases hx; cases hn; rfl
    | succ k => cases k with
      | zero => cases hx; cases hn; rfl
      | succ k => simp at hx

def afterBody : CommonData.State :=
  ⟨SizedBufferHeap.release (SizedBufferHeap.restore
    (SizedBufferHeap.allocate (SizedBufferHeap.release (SizedBufferHeap.release start.buffers 4) 5) 1 7)) 7,
    start.cells⟩

def bufferEvents : List SizedBufferHeap.Event :=
  [.free 4, .free 5, .alloc 7 1 7, .beginLease 0 7, .read 0 0 7, .close 0, .free 7]

def finalState := CommonData.finish (CommonData.allocate afterBody (some 1) (some 2)) 0

def events : List HeapLeases.Event :=
  bufferEvents.map SizedBufferHeap.Event.project ++ [.alloc 8 0, .free 0]

theorem node_buffer_run : SizedCoreExecution.Eval (coreGraph graph) (environment opened)
    24 start.buffers (.scalar 7) bufferEvents afterBody.buffers := by
  apply SizedCoreExecution.Eval.free (owner := 23) (body := 22) (k := 5) core_shape core_shape core_shape
  apply SizedCoreExecution.Eval.free (owner := 21) (body := 20) (k := 9) core_shape core_shape core_shape
  apply SizedCoreExecution.Eval.app core_shape core_shape
    (.allocate core_shape (DependentBufferIndices.Eval.var core_shape core_shape) (.var core_shape core_shape))
  exact .lend read_shape core_shape core_shape (DependentBufferIndices.Eval.literal core_shape (by decide))
    (.free core_shape core_shape core_shape (.var core_shape core_shape))

theorem case_run : Eval graph env 39 start (.data (some 8)) events finalState := by
  have branch : Eval graph opened 30 start (.data (some 8))
      (bufferEvents.map SizedBufferHeap.Event.project ++ [.alloc 8 0])
      (CommonData.allocate afterBody (some 1) (some 2)) :=
    .bufferLet rfl rfl rfl node_buffer_run (.construct rfl rfl rfl rfl rfl)
  simpa [events, finalState, List.append_assoc] using
    Eval.nodeCase (g := graph) (term := 39) (env := env) (index := 0)
      (scrutinee := 25) (nilBranch := 38) (ghosts := 2) rfl rfl rfl branch

theorem case_safe : Steps start.buffers.heap events finalState.buffers.heap ∧
    Valid finalState.buffers.heap ∧ Post .data finalState (.data (some 8)) [6] :=
  case_typed.every_run (trees := [parent]) (owners := [4,5]) rfl
    RecursiveCaseBodyExamples.agreement layout_start valid_start owns_start fields_start case_run

theorem result_fields : Represents finalState.cells (.node 8 (leaf 1) rightTree) := by
  simp [Represents, finalState, CommonData.finish, RecursiveCaseBody.finish, CommonData.allocate, afterBody,
    start, root, leaf, rightTree, HeapLeases.put, SizedBufferHeap.release,
    SizedBufferHeap.restore, SizedBufferHeap.allocate, ScopedLend.restored,
    RecursiveFieldRuntimeExamples.fixture, allocatedState]

theorem complete_result_ownership : Owns finalState.buffers.heap [8,1,2,3,6] := by
  obtain ⟨tree, eq, fields, owned⟩ := case_safe.2.2
  have same := Represents.unique fields result_fields (Value.data.inj eq).symm
  subst tree
  exact owned

theorem old_parent_freed_last :
    (released events).count 0 = 1 ∧ events.getLast? = some (.free 0) ∧
    finalState.buffers.heap.live 0 = false ∧ finalState.buffers.heap.live 6 = true := by decide

/-- Nil has no boxed parent; only the two Buffer inputs and frame are live. -/
def emptyStart : CommonData.State :=
  ⟨⟨⟨7, 0, fun x => decide (x = 4 ∨ x = 5 ∨ x = 6), fun _ => 7, fun _ => none⟩,
    start.buffers.length⟩, fun _ => none⟩
def emptyEnv : List Value :=
  [.data none, .buffer 4, .buffer 4, .nat 1, .scalar 7, .buffer 5, .buffer 5, .ghost]
def emptyFinal : CommonData.State :=
  ⟨SizedBufferHeap.release (SizedBufferHeap.release emptyStart.buffers 4) 5, emptyStart.cells⟩

theorem empty_agreement : Agrees (caps [.empty] [4,5]) ctx emptyEnv :=
  .cons ⟨.empty, rfl, rfl⟩ (.cons ⟨4,rfl,rfl⟩ (.cons ⟨4,rfl,rfl⟩
    (.cons rfl (.cons ⟨7,rfl⟩ (.cons ⟨5,rfl,rfl⟩ (.cons ⟨5,rfl,rfl⟩ (.cons rfl .nil)))))))

theorem empty_valid : Valid emptyStart.buffers.heap := by
  constructor
  · intro x h; simp [emptyStart] at h; rcases h with rfl | rfl | rfl <;> decide
  · intro l x h; simp [emptyStart] at h

theorem empty_owned : Owns emptyStart.buffers.heap (footprint (caps [.empty] [4,5]) ++ [6]) := by
  constructor
  · decide
  · intro x h; change x ∈ [4,5,6] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> decide
  · intro x h l; simp [emptyStart]

theorem empty_fields : Fields emptyStart.cells (caps [.empty] [4,5]) := by
  intro c member
  change c ∈ [.data .empty, .buffer 4, .buffer 5] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> trivial

theorem empty_run : Eval graph emptyEnv 39 emptyStart (.data none) [.free 4, .free 5] emptyFinal := by
  apply Eval.emptyCase core_shape core_shape core_shape
  exact .bufferLet core_shape core_shape core_shape (.free (owner := 33) (body := 35) (k := 1) core_shape core_shape core_shape (.free (owner := 34) (body := 10) (k := 5) core_shape core_shape core_shape (.scalar (v := 99) core_shape))) (.empty core_shape)

theorem empty_safe : Steps emptyStart.buffers.heap [.free 4, .free 5] emptyFinal.buffers.heap ∧
    Valid emptyFinal.buffers.heap ∧ Post .data emptyFinal (.data none) [6] := by
  have layout : SizedBufferContext.Layout emptyStart.buffers [4,5] [1,2] :=
    ⟨layout_start.length, layout_start.lookup⟩
  exact case_typed.every_run (trees := [.empty]) (owners := [4,5]) rfl empty_agreement
    layout empty_valid empty_owned empty_fields empty_run

end Jihoo.CommonDataExamples
