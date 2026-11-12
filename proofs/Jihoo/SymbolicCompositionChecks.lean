import Jihoo.SymbolicMirLoweringTotality
import Jihoo.SymbolicCoreRejections
import Jihoo.SizedCompositionExamples
import Jihoo.SymbolicCommonDataChecks

/-! One static derivation for the exporter-tested composed graph. No closing
values or successful executions are premises of source typing. -/
namespace Jihoo.SymbolicCompositionChecks
open ScopedLend SymbolicCoreContext SymbolicCoreTyping
open DependentBufferIndices (Expr)
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
abbrev graph := SizedCompositionGraph.graph
def inputs : Context := [.scalar, .nat, .nat, .nat]

theorem body_typed : Typing graph inputs [] 81 .scalar := by
  apply Typing.allocate (function := 77) (argument := 80) (domain := 14)
    (length := 78) (init := 79) (n := .var 3) rfl rfl
  · exact ⟨13, rfl, ⟨.var rfl, .var rfl⟩⟩
  · rfl
  · exact ⟨.var rfl, .var rfl⟩
  · exact .var rfl rfl
  · apply Typing.branch (left := 15) (right := 16) (a := .var 2) (b := .var 4) rfl
    · exact ⟨.var rfl, .var rfl⟩
    · exact ⟨.var rfl, .var rfl⟩
    · apply Typing.ownedLend (slot := 0) (n := .var 5) (m := .var 4) (i := .var 3) SizedCompositionExamples.copy_shape rfl rfl rfl
      · exact ⟨19, rfl, 18, rfl, ⟨.var rfl, .var rfl⟩⟩
      · exact ⟨.var rfl, .var rfl⟩
      · exact ⟨28, rfl, ⟨.var rfl, .var rfl⟩⟩
      · exact ⟨30, rfl, ⟨.var rfl, .var rfl⟩⟩
      · exact ⟨.var rfl, .var rfl⟩
      · exact .var rfl rfl
      · apply Typing.framedApp (function := 62) (argument := 68) (domain := 33)
          (p := 1) (n := .var 6) rfl rfl (by simp)
        · exact ⟨32, rfl, ⟨.var rfl, .var rfl⟩⟩
        · apply Typing.ownedLet (function := 66) (argument := 67) (domain := 64)
            (slot := 0) (n := .var 6) rfl rfl rfl rfl rfl
          · exact ⟨63, rfl, ⟨.var rfl, .var rfl⟩⟩
          · exact .owner rfl rfl
        · apply Typing.branch (left := 34) (right := 35) (a := .literal 0) (b := .var 7) rfl
          · exact ⟨.literal rfl (by decide), .literal⟩
          · exact ⟨.var rfl, .var rfl⟩
          · apply Typing.lend (slot := 0) (n := .var 8) (i := .literal 0) SizedCompositionExamples.observe_shape rfl rfl rfl
            · exact ⟨38, rfl, 37, rfl, ⟨.var rfl, .var rfl⟩⟩
            · exact ⟨46, rfl, ⟨.var rfl, .var rfl⟩⟩
            · exact ⟨.literal rfl (by decide), .literal⟩
            · exact .var rfl rfl
            · apply Typing.free (slot := 1) rfl rfl rfl (by simp)
              exact .free (slot := 0) rfl rfl rfl (by simp) (.scalar rfl rfl)
          · apply Typing.free (slot := 1) rfl rfl rfl (by simp)
            exact .free (slot := 0) rfl rfl rfl (by simp) (.scalar rfl rfl)
    · exact .free (slot := 0) rfl rfl rfl (by simp) (.literal rfl (by decide))


theorem inputs_close (hn : n < 2^64) (hm : m < 2^64) (hi : i < 2^64) :
    Closes inputs (SizedCompositionExamples.inputContext n m i) :=
  .cons trivial (.cons hi (.cons hm (.cons hn .nil)))

theorem all_lengths_typed (hn : n < 2^64) (hm : m < 2^64) (hi : i < 2^64) :
    SizedCoreTyping.Typing graph (SizedCompositionExamples.inputContext n m i) [] 81 .scalar :=
  body_typed.instantiate (inputs_close hn hm hi) .nil trivial

theorem zero_result_typed :
    SizedCoreTyping.Typing graph (SizedCompositionExamples.inputContext 7 0 6) [] 81 .scalar :=
  all_lengths_typed (by decide) (by decide) (by decide)

theorem distinct_lengths_typed :
    SizedCoreTyping.Typing graph (SizedCompositionExamples.inputContext 7 2 6) [] 81 .scalar :=
  all_lengths_typed (by decide) (by decide) (by decide)

theorem framed_aliases_rejected (a : Graph.nodeAt g ra = .var 1)
    (b : Graph.nodeAt g rb = .var 3) :
    ¬ Typing g (callBody [.owner 0,.nat,.owner 0,.owner 1] 1) sizes ra kind ∧
    ¬ Typing g (callBody [.owner 0,.nat,.owner 0,.owner 1] 1) sizes rb kind :=
  ⟨SymbolicCoreRejections.dead_var_rejected a rfl,
   SymbolicCoreRejections.dead_var_rejected b rfl⟩

theorem retained_owner :
    (callBody [.owner 0,.nat,.owner 0,.owner 1] 1)[4]? = some (.owner 1) := rfl

theorem returned_owners :
    ownedReturned [.owner 0,.nat,.owner 0,.owner 1] 0 =
      [.owner 1,.owner 0,.owner 1,.nat,.owner 1,.owner 2] := rfl

local macro "case_shape" : term => `(by simp [Graph.nodeAt,
  CommonDataSourceExecution.sourceCore, CommonDataSourceExecution.coreNode,
  SymbolicCommonDataChecks.nodes])

/-- Case branches use the new framed rule, with their shifted open lengths. -/
theorem case_framed_open : SymbolicCommonDataSource.Typing SymbolicCommonDataChecks.nodes
    [.data 0,.nat,.buffer 1] 1 [.var 1] 24 .scalar := by
  apply SymbolicCommonDataSource.Typing.caseTree rfl rfl rfl rfl rfl
  · apply SymbolicCommonDataSource.Typing.bufferLet rfl rfl rfl
    · apply Typing.framedApp (function := 10) (argument := 5) (domain := 8)
        (body := 9) (p := 1) (n := .var 1) case_shape case_shape (by decide)
      · exact ⟨4, case_shape, ⟨.var case_shape, .var rfl⟩⟩
      · exact .owner (k := 2) case_shape rfl
      · exact .free (owner := 3) (k := 0) (body := 2) (slot := 0) case_shape case_shape rfl (by decide) (.literal (v := 9) case_shape (by decide))
    · exact .literal rfl (by decide)
  · apply SymbolicCommonDataSource.Typing.bufferLet rfl rfl rfl
    · apply Typing.framedApp (function := 15) (argument := 7) (domain := 14)
        (body := 9) (p := 1) (n := .var 3) case_shape case_shape (by decide)
      · exact ⟨6, case_shape, ⟨.var case_shape, .var rfl⟩⟩
      · exact .owner (k := 4) case_shape rfl
      · exact .free (owner := 3) (k := 0) (body := 2) (slot := 0) case_shape case_shape rfl (by decide) (.literal (v := 9) case_shape (by decide))
    · exact .drop rfl rfl rfl (.drop rfl rfl rfl (.literal rfl (by decide)))

theorem case_framed_all_lengths (n : Nat) (bound : n < 2^64) :
    CommonDataSourceRules.Typing SymbolicCommonDataChecks.nodes
      [.data 0,.nat n,.buffer 1] 1 [n] 24 .scalar :=
  case_framed_open.instantiate (.cons rfl (.cons bound (.cons rfl .nil))) (.cons rfl .nil)

/-- Both new rules execute before a Data Case in the same source judgment. -/
def commonGraph : CommonDataSource.Graph :=
  ((graph.extract 0 82).map CommonDataSource.Node.core) ++ #[
    .ind 0 [], .core (.var 5), .core (.var 0), .core (.var 1),
    .drop 0 (82+2) 74, .drop 0 (82+3) (82+4),
    .core (.lam false 82 (82+5)),
    .core (.lam false 82 (82+6)),
    .core (.lam false 82 12),
    .caseOf 0 (82+8) [74,82+7] (82+1),
    .core (.lam false 12 (82+9)), .core (.app (82+10) 81)]

private theorem common_lookup (k : Nat) (bound : k < 82) :
    Graph.nodeAt (CommonDataSourceExecution.sourceCore commonGraph) k = Graph.nodeAt graph k := by
  have size : (graph.extract 0 82).size = 82 := by decide
  unfold Graph.nodeAt CommonDataSourceExecution.sourceCore commonGraph
  rw [Array.getElem?_map, Array.getElem?_append_left (by simpa only [Array.size_map, size] using bound),
    Array.getElem?_map, Array.getElem?_extract]
  simp only [show min 82 graph.size - 0 = 82 from rfl, Nat.zero_add, ite_eq_left bound]
  cases graph[k]? <;> rfl

local macro "common_shape" : term => `(by first
  | (rw [common_lookup _ (by decide)]; rfl)
  | rfl
  | decide +kernel)

theorem common_argument : Typing (CommonDataSourceExecution.sourceCore commonGraph)
    [.scalar,.nat,.nat,.nat,.dead] [] 81 .scalar := by
  apply Typing.allocate (function := 77) (argument := 80) (domain := 14)
    (length := 78) (init := 79) (n := .var 3) common_shape common_shape
  · exact ⟨13, common_shape, ⟨.var common_shape, .var common_shape⟩⟩
  · exact common_shape
  · exact ⟨.var common_shape, .var common_shape⟩
  · exact .var common_shape common_shape
  · apply Typing.branch (left := 15) (right := 16) (a := .var 2) (b := .var 4) common_shape
    · exact ⟨.var common_shape, .var common_shape⟩
    · exact ⟨.var common_shape, .var common_shape⟩
    · apply Typing.ownedLend (slot := 0) (n := .var 5) (m := .var 4) (i := .var 3) (SizedCoreExecution.OwnedReadLend.intro common_shape common_shape common_shape common_shape common_shape common_shape common_shape) common_shape common_shape common_shape
      · exact ⟨19, common_shape, 18, common_shape, ⟨.var common_shape, .var common_shape⟩⟩
      · exact ⟨.var common_shape, .var common_shape⟩
      · exact ⟨28, common_shape, ⟨.var common_shape, .var common_shape⟩⟩
      · exact ⟨30, common_shape, ⟨.var common_shape, .var common_shape⟩⟩
      · exact ⟨.var common_shape, .var common_shape⟩
      · exact .var common_shape common_shape
      · apply Typing.framedApp (function := 62) (argument := 68) (domain := 33)
          (p := 1) (n := .var 6) common_shape common_shape (by simp)
        · exact ⟨32, common_shape, ⟨.var common_shape, .var common_shape⟩⟩
        · apply Typing.ownedLet (function := 66) (argument := 67) (domain := 64)
            (slot := 0) (n := .var 6) common_shape common_shape common_shape common_shape common_shape
          · exact ⟨63, common_shape, ⟨.var common_shape, .var common_shape⟩⟩
          · exact .owner common_shape common_shape
        · apply Typing.branch (left := 34) (right := 35) (a := .literal 0) (b := .var 7) common_shape
          · exact ⟨.literal common_shape (by decide), .literal⟩
          · exact ⟨.var common_shape, .var common_shape⟩
          · apply Typing.lend (slot := 0) (n := .var 8) (i := .literal 0) (SizedCoreExecution.ReadLend.intro common_shape common_shape common_shape common_shape common_shape common_shape common_shape) common_shape common_shape common_shape
            · exact ⟨38, common_shape, 37, common_shape, ⟨.var common_shape, .var common_shape⟩⟩
            · exact ⟨46, common_shape, ⟨.var common_shape, .var common_shape⟩⟩
            · exact ⟨.literal common_shape (by decide), .literal⟩
            · exact .var common_shape common_shape
            · apply Typing.free (slot := 1) common_shape common_shape common_shape (by simp)
              exact .free (slot := 0) common_shape common_shape common_shape (by simp) (.scalar common_shape common_shape)
          · apply Typing.free (slot := 1) common_shape common_shape common_shape (by simp)
            exact .free (slot := 0) common_shape common_shape common_shape (by simp) (.scalar common_shape common_shape)
    · exact .free (slot := 0) common_shape common_shape common_shape (by simp) (.literal common_shape (by decide))


theorem common_case : SymbolicCommonDataSource.Typing commonGraph
    [.scalar,.nat,.nat,.nat,.data 0] 1 [] (82+11) .scalar := by
  apply SymbolicCommonDataSource.Typing.bufferLet (fn := 82+10) (arg := 81)
    (ty := 12) (body := 82+9) common_shape common_shape common_shape
  · exact common_argument
  · apply SymbolicCommonDataSource.Typing.caseTree (motive := 82+8)
      (nil := 74) (node := 82+7) (scrutinee := 82+1) (index := 5)
      (body := 82+5) common_shape (by decide +kernel) (by decide +kernel) common_shape rfl
    · exact .literal (n := 99) common_shape (by decide)
    · apply SymbolicCommonDataSource.Typing.drop (owner := 82+3)
        (index := 1) (body := 82+4) common_shape common_shape rfl
      exact .drop (owner := 82+2) (index := 0) (body := 74)
        common_shape common_shape rfl (.literal (n := 99) common_shape (by decide))

theorem common_case_all_lengths (hn : n < 2^64) (hm : m < 2^64) (hi : i < 2^64) :
    CommonDataSourceRules.Typing commonGraph [.scalar,.nat i,.nat m,.nat n,.data 0]
      1 [] (82+11) .scalar :=
  common_case.instantiate (.cons trivial (.cons hi (.cons hm (.cons hn (.cons rfl .nil))))) .nil

/-- Source execution and resource accounting follow from the mixed derivation,
with ordinary input invariants and no assumption that execution succeeds. -/
theorem common_case_total (hn : n < 2^64) (hm : m < 2^64) (hi : i < 2^64)
    (length : trees.length = 1)
    (agreement : RecursiveLexicalFields.Agrees (CommonData.caps trees [])
      [.scalar,.nat i,.nat m,.nat n,.data 0] env)
    (layout : SizedBufferContext.Layout s.buffers [] [])
    (valid : HeapLeases.Valid s.buffers.heap)
    (owned : LinearHeapPrograms.Owns s.buffers.heap
      (RecursiveLexicalFields.footprint (CommonData.caps trees []) ++ frame))
    (fields : RecursiveLexicalFields.Fields s.cells (CommonData.caps trees [])) :
    ∃ v es t, CommonDataSourceExecution.Eval commonGraph env (82+11) s v es t ∧
      HeapLeases.Steps s.buffers.heap es t.buffers.heap ∧ HeapLeases.Valid t.buffers.heap ∧
      CommonData.AccountedPost .scalar t v frame
        (RecursiveLexicalFields.footprint (CommonData.caps trees [])) es :=
  common_case.total_accounted (closed := [.scalar,.nat i,.nat m,.nat n,.data 0])
    (.cons trivial (.cons hi (.cons hm (.cons hn (.cons rfl .nil))))) .nil
    length agreement layout valid owned fields

theorem body_total (hn : n < 2^64) (hm : m < 2^64) (hi : i < 2^64) (value : Nat) :
    ∃ result events t, SizedCoreExecution.Eval graph (SizedCompositionExamples.inputEnv n m i value) 81
      SizedBufferHeap.empty result events t ∧ SizedBufferHeap.Steps SizedBufferHeap.empty events t ∧
      SizedBufferHeap.Valid t ∧ SizedCoreTyping.Post .scalar t result ∧ SizedCoreTyping.Account [] result events :=
  (all_lengths_typed hn hm hi).total_accounted (SizedCompositionExamples.input_agrees n m i value)
    ⟨rfl, by simp⟩ SizedBufferHeap.empty_valid LinearHeapPrograms.empty_owns

theorem every_run_no_live (hn : n < 2^64) (hm : m < 2^64) (hi : i < 2^64)
    (run : SizedCoreExecution.Eval graph (SizedCompositionExamples.inputEnv n m i value) 81
      SizedBufferHeap.empty result events t) : ∀ x, t.heap.live x = false :=
  (all_lengths_typed hn hm hi).closed_scalar_empty (SizedCompositionExamples.input_agrees n m i value) run

theorem structural_total (hn : n < 2^64) (hm : m < 2^64) (hi : i < 2^64)
    (same : operands.length = 4) :
    ∃ term bound, SizedMir.Structural.Typed [.scalar,.natural,.natural,.natural] term .scalar ∧
      (∀ fuel, bound ≤ fuel → SizedErasure.compileTarget graph fuel [true,true,true,true] 81 = some term) ∧
      ∀ l b exit, ∃ fragment,
        SizedMir.Linear.compile operands [.scalar,.natural,.natural,.natural] l b exit term = some fragment ∧
        fragment.locals.size = SizedMir.Linear.localCost term ∧
        fragment.blocks.size = SizedMir.Linear.blockCost term := by
  exact SymbolicMirStructuralBridge.typing_compiles_closed body_typed (inputs_close hn hm hi)
    (SizedCompositionExamples.input_agrees n m i 0)
    (by simpa [SizedCompositionExamples.inputEnv, SizedErasure.compactEnv] using same)

theorem producer_retained_rejected (shape : Graph.nodeAt g root = .var 1) :
    ¬ Typing g (producer [.owner 0,.owner 1] 1) sizes root kind :=
  SymbolicCoreRejections.dead_var_rejected shape rfl

theorem empty_prefix_context : callBody [.owner 0,.owner 1] 0 =
    [.owner 0,.owner 1,.owner 2] := rfl

theorem full_prefix_context : callBody [.owner 0,.owner 1,.owner 0] 2 =
    [.owner 0,.dead,.dead,.dead] := rfl

end Jihoo.SymbolicCompositionChecks
