import Jihoo.SymbolicCommonDataSource

namespace Jihoo.CommonDataBufferChecks
open SymbolicCommonDataContext SymbolicCommonDataSource

/-- Allocate before branching, retain the Buffer across actual Data inspection,
then free it in either branch and return a Data result. -/
def nodes : CommonDataSource.Graph := #[
  .ind 0 [], .core .i64, .core (.var 0), .core (.var 1), .core (.var 2),
  .core (.integer 9), .core (.buffer 3), .core (.alloc 3 5), .con 0 0 [],
  .core (.free 2 8), .con 0 1 [3,2], .core (.free 4 10),
  .core (.lam false 0 11), .core (.lam false 0 12), .core (.lam false 0 0),
  .caseOf 0 14 [9,13] 3, .core (.lam false 6 15), .core (.app 16 7)]

local macro "shape" : term => `(by simp [ScopedLend.Graph.nodeAt,
  CommonDataSourceExecution.sourceCore, CommonDataSourceExecution.coreNode,nodes])

theorem symbolic_lifecycle : Typing nodes [.data 0,.nat] 1 [] 17 .data := by
  apply Typing.allocate (n := .var 1) rfl rfl rfl
  · exact ⟨3,shape,⟨.var shape,.var rfl⟩⟩
  · rfl
  · exact ⟨.var shape,.var rfl⟩
  · exact .literal (v := 9) shape (by decide)
  · apply Typing.caseTree rfl rfl rfl rfl rfl
    · exact .freeBuffer (slot := 0) rfl rfl rfl (by decide) (.empty rfl)
    · exact .freeBuffer (slot := 0) rfl rfl rfl (by decide) (.construct rfl rfl rfl rfl rfl)

theorem all_lengths (n : Nat) (bound : n < 2^64) :
    CommonDataSourceRules.Typing nodes [.data 0,.nat n] 1 [] 17 .data :=
  symbolic_lifecycle.instantiate (.cons rfl (.cons bound .nil)) .nil

theorem aliases_and_survivors :
    consumeBuffer 3 [.data 0,.buffer 2,.buffer 3,.nat,.buffer 3,.buffer 4,.data 1] =
      [.data 0,.buffer 2,.dead,.nat,.dead,.buffer 3,.data 1] ∧
    freshBuffer 2 [.data 0,.buffer 2,.data 1,.nat,.buffer 2] =
      [.buffer 2,.data 0,.buffer 3,.data 1,.nat,.buffer 3] := by decide

/-- A split application reserves the allocated Buffer while Case/Drop compute
Data, then frees it in the common continuation. -/
def delayedNodes : CommonDataSource.Graph := nodes ++ #[
  .drop 0 3 2, .core (.lam false 0 18), .core (.lam false 0 19),
  .caseOf 0 14 [8,20] 3, .core (.free 3 2), .core (.lam false 0 22),
  .core (.app 23 21), .core (.lam false 6 24), .core (.app 25 7)]

local macro "delayed_shape" : term => `(by simp [ScopedLend.Graph.nodeAt,
  CommonDataSourceExecution.sourceCore,CommonDataSourceExecution.coreNode,delayedNodes,nodes])

theorem delayed_free : Typing delayedNodes [.data 0,.nat] 1 [] 26 .data := by
  apply Typing.allocate (n := .var 1) rfl rfl rfl
  · exact ⟨3,delayed_shape,⟨.var delayed_shape,.var rfl⟩⟩
  · rfl
  · exact ⟨.var delayed_shape,.var rfl⟩
  · exact .literal (v := 9) delayed_shape (by decide)
  · apply Typing.dataLetSplit (activeCount := 1) (retainedCount := 0)
      (usedSizes := []) (savedSizes := [.var 2]) rfl rfl rfl rfl rfl
    · apply Typing.caseTree rfl rfl rfl rfl rfl
      · exact .empty rfl
      · exact .drop rfl rfl rfl (.dataVar rfl rfl)
    · exact .freeBuffer (slot := 0) rfl rfl rfl (by decide) (.dataVar rfl rfl)

open CommonData RecursiveLexicalFields RecursiveFieldOwnership HeapLeases LinearHeapPrograms

theorem all_lengths_total (n : Nat) (bound : n < 2^64)
    (length : trees.length = 1)
    (agreement : Agrees (caps trees []) [.data 0,.nat n] env)
    (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees []) ++ frame))
    (fields : Fields s.cells (caps trees [])) :
    ∃ v es t, CommonDataSourceExecution.Eval nodes env 17 s v es t ∧
      Steps s.buffers.heap es t.buffers.heap ∧ Valid t.buffers.heap ∧
      AccountedPost .data t v frame (footprint (caps trees [])) es :=
  symbolic_lifecycle.total_accounted (closed := [.data 0,.nat n]) (.cons rfl (.cons bound .nil)) .nil
    length agreement empty_layout valid owned fields

theorem every_run_accounted (n : Nat) (bound : n < 2^64)
    (length : trees.length = 1)
    (agreement : Agrees (caps trees []) [.data 0,.nat n] env)
    (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees []) ++ frame))
    (fields : Fields s.cells (caps trees []))
    (run : CommonDataSourceExecution.Eval nodes env 17 s v es t) :
    Steps s.buffers.heap es t.buffers.heap ∧ Valid t.buffers.heap ∧
      AccountedPost .data t v frame (footprint (caps trees [])) es :=
  symbolic_lifecycle.every_run_accounted (closed := [.data 0,.nat n]) (.cons rfl (.cons bound .nil)) .nil
    length agreement empty_layout valid owned fields run

def selectedNodes : CommonDataSource.Graph := nodes ++ #[
  .core (.var 3), .core (.free 18 10), .core (.free 4 19)]

/-- Select the second Buffer, preserve the first, then return both Data fields. -/
theorem selected_buffer : SymbolicCommonDataSource.Typing selectedNodes
    [.data 1,.data 0,.buffer 3,.buffer 2,.buffer 3,.nat] 2 [.literal 3,.var 5] 20 .data := by
  apply SymbolicCommonDataSource.Typing.freeBuffer (slot := 1) rfl rfl rfl (by decide)
  exact .freeBuffer (slot := 0) rfl rfl rfl (by decide) (.construct rfl rfl rfl rfl rfl)

/-- The stale alias fails even with another Buffer available: the size bound
alone cannot reject this Free. -/
theorem consumed_alias_rejected : ¬ CommonDataSourceRules.Typing nodes
    (CommonData.consumeBuffer 2 [.data 1,.data 0,.buffer 2,.buffer 2,.buffer 3]) 2 [1] 11 .data := by
  intro h
  have ht : CommonDataSource.nodeAt nodes 11 = .core (.free 4 10) := rfl
  have ho : CommonDataSource.nodeAt nodes 4 = .core (.var 2) := rfl
  cases h
  case freeBuffer ownerShape lookup bound freeShape body =>
    cases ht.symm.trans freeShape
    cases ho.symm.trans ownerShape
    change some RecursiveLexicalFields.Entry.dead = some (.buffer _) at lookup
    cases lookup
  all_goals simp_all

theorem second_alias_rejected : ¬ CommonDataSourceRules.Typing selectedNodes
    (CommonData.consumeBuffer 2 [.data 1,.data 0,.buffer 2,.buffer 2,.buffer 3]) 2 [1] 19 .data := by
  intro h
  have ht : CommonDataSource.nodeAt selectedNodes 19 = .core (.free 18 10) := rfl
  have ho : CommonDataSource.nodeAt selectedNodes 18 = .core (.var 3) := rfl
  cases h
  case freeBuffer ownerShape lookup bound freeShape body =>
    cases ht.symm.trans freeShape
    cases ho.symm.trans ownerShape
    change some RecursiveLexicalFields.Entry.dead = some (.buffer _) at lookup
    cases lookup
  all_goals simp_all

def wrongSize : CommonDataSource.Graph := #[
  .core (.natural 1),.core (.natural 2),.core (.buffer 1),.core (.integer 0),
  .core (.alloc 0 3),.con 0 0 [],.core (.var 0),.core (.free 6 5),
  .core (.lam false 2 7),.core (.app 8 4)]

theorem wrong_size_rejected : ¬ CommonDataSourceRules.Typing wrongSize [] 0 [] 9 .data := by
  intro h
  have ht : CommonDataSource.nodeAt wrongSize 9 = .core (.app 8 4) := rfl
  have hf : CommonDataSource.nodeAt wrongSize 8 = .core (.lam false 2 7) := rfl
  have hd : CommonDataSource.nodeAt wrongSize 2 = .core (.buffer 1) := rfl
  have ha : CommonDataSource.nodeAt wrongSize 4 = .core (.alloc 0 3) := rfl
  cases h
  case allocate lam ty alloc annotation len init appShape body =>
    cases ht.symm.trans appShape
    cases hf.symm.trans lam
    cases ha.symm.trans alloc
    have two : DependentBufferIndices.BufferLength
        (CommonData.coreGraph (CommonDataSourceRules.graph wrongSize))
        (SizedBufferContext.naturalEnv (RecursiveBodyProjection.context 0 [])) 2 2 :=
      ⟨1,by rw [← CommonDataSourceExecution.sourceCore_eq]; simp [CommonDataSourceExecution.sourceCore,CommonDataSourceExecution.coreNode,ScopedLend.Graph.nodeAt,wrongSize],
        .literal (by rw [← CommonDataSourceExecution.sourceCore_eq]; simp [CommonDataSourceExecution.sourceCore,CommonDataSourceExecution.coreNode,ScopedLend.Graph.nodeAt,wrongSize]) (by decide)⟩
    have one : DependentBufferIndices.Eval
        (CommonData.coreGraph (CommonDataSourceRules.graph wrongSize))
        (SizedBufferContext.naturalEnv (RecursiveBodyProjection.context 0 [])) 0 1 :=
      .literal (by rw [← CommonDataSourceExecution.sourceCore_eq]; simp [CommonDataSourceExecution.sourceCore,CommonDataSourceExecution.coreNode,ScopedLend.Graph.nodeAt,wrongSize]) (by decide)
    have a := annotation.unique two
    have b := len.deterministic one
    omega
  all_goals simp_all

end Jihoo.CommonDataBufferChecks
