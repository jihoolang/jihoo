import Jihoo.CommonDataBufferChecks

/-! Prefix-partitioned Buffer producers followed by recursive Data consumers.
The producer releases one input and returns another; the third stays framed. -/
namespace Jihoo.CommonDataBufferProducerChecks
open SymbolicCommonDataContext SymbolicCommonDataSource

def nodes : CommonDataSource.Graph := #[
  .ind 0 [], .core .i64, .core (.var 0), .core (.var 1), .core (.var 2),
  .core (.var 3), .core (.var 4), .core (.var 5), .core (.integer 9),
  .core (.buffer 6), .core (.free 3 4), .con 0 0 [],
  .core (.free 6 11), .core (.free 2 12), .core (.var 6),
  .con 0 1 [3,2], .core (.free 4 15), .core (.free 14 16),
  .core (.lam false 0 17), .core (.lam false 0 18), .core (.lam false 0 0),
  .caseOf 0 20 [13,19] 3, .core (.lam false 9 21), .core (.app 22 10)]

def inputs : Context := [.data 0,.buffer 1,.buffer 2,.buffer 3,.nat,.nat]
def sizes : SymbolicCoreContext.Sizes := [.var 4,.var 4,.var 5]

local macro "shape" : term => `(by simp [ScopedLend.Graph.nodeAt,
  CommonDataSourceExecution.sourceCore,CommonDataSourceExecution.coreNode,nodes])

theorem symbolic_producer : SymbolicCoreTyping.Typing (CommonDataSourceExecution.sourceCore nodes)
    (SymbolicCoreContext.producer (project 1 inputs) 2) (sizes.take 2) 10 (.owner (.var 4)) := by
  apply SymbolicCoreTyping.Typing.free (owner := 3) (body := 4) (k := 1) (slot := 0) shape shape rfl (by decide)
  exact .owner (k := 2) shape rfl

theorem symbolic_call : Typing nodes inputs 1 sizes 23 .data := by
  apply Typing.bufferApp (p := 2) (n := .var 4) rfl rfl rfl (by decide)
  · exact ⟨6,shape,⟨.var shape,.var rfl⟩⟩
  · exact symbolic_producer
  · apply Typing.caseTree rfl rfl rfl rfl rfl
    · exact .freeBuffer (slot := 0) rfl rfl rfl (by decide)
        (.freeBuffer (slot := 0) rfl rfl rfl (by decide) (.empty rfl))
    · exact .freeBuffer (slot := 1) rfl rfl rfl (by decide)
        (.freeBuffer (slot := 0) rfl rfl rfl (by decide) (.construct rfl rfl rfl rfl rfl))

/-- Data computation can finish before the consumer chooses to release either
Buffer; both survive the split Data application and its additional binder. -/
def delayedNodes : CommonDataSource.Graph := nodes ++ #[
  .drop 0 3 2, .core (.lam false 0 24), .core (.lam false 0 25),
  .caseOf 0 20 [11,26] 3, .core (.free 7 2), .core (.free 3 28),
  .core (.lam false 0 29), .core (.app 30 27),
  .core (.lam false 9 31), .core (.app 32 10)]

local macro "delayed_shape" : term => `(by simp [ScopedLend.Graph.nodeAt,
  CommonDataSourceExecution.sourceCore,CommonDataSourceExecution.coreNode,delayedNodes,nodes])

theorem delayed_free : Typing delayedNodes inputs 1 sizes 33 .data := by
  apply Typing.bufferApp (p := 2) (n := .var 4) rfl rfl rfl (by decide)
  · exact ⟨6,delayed_shape,⟨.var delayed_shape,.var rfl⟩⟩
  · apply SymbolicCoreTyping.Typing.free (owner := 3) (body := 4) (k := 1) (slot := 0) delayed_shape delayed_shape rfl (by decide)
    exact .owner (k := 2) delayed_shape rfl
  · apply Typing.dataLetSplit (activeCount := 1) (retainedCount := 0)
      (usedSizes := []) (savedSizes := [.var 5,.var 6]) rfl rfl rfl rfl rfl
    · apply Typing.caseTree rfl rfl rfl rfl rfl
      · exact .empty rfl
      · exact .drop rfl rfl rfl (.dataVar rfl rfl)
    · exact .freeBuffer (slot := 0) rfl rfl rfl (by decide)
        (.freeBuffer (slot := 0) rfl rfl rfl (by decide) (.dataVar rfl rfl))

local macro "direct_shape" : term => `(by simp [ScopedLend.Graph.nodeAt,
  CommonDataSourceExecution.sourceCore,CommonDataSourceExecution.coreNode,CommonDataBufferChecks.nodes])

/-- The old direct Alloc fixture also derives through the new p=0 rule. -/
theorem direct_alloc : Typing CommonDataBufferChecks.nodes [.data 0,.nat] 1 [] 17 .data := by
  apply Typing.bufferApp (p := 0) (n := .var 1) rfl rfl rfl (by decide)
  · exact ⟨3,direct_shape,⟨.var direct_shape,.var rfl⟩⟩
  · exact .allocation (length := 3) (init := 5) direct_shape ⟨.var direct_shape,.var rfl⟩ (.literal (v := 9) direct_shape (by decide))
  · apply Typing.caseTree rfl rfl rfl rfl rfl
    · exact .freeBuffer (slot := 0) rfl rfl rfl (by decide) (.empty rfl)
    · exact .freeBuffer (slot := 0) rfl rfl rfl (by decide) (.construct rfl rfl rfl rfl rfl)

theorem captured_context : bufferCall 1 2
    [.data 0,.buffer 1,.buffer 2,.buffer 3,.nat,.buffer 2] =
      [.buffer 1,.data 0,.dead,.dead,.buffer 2,.nat,.dead] := by decide

theorem producer_retained_rejected : ¬ SizedCoreTyping.Typing
    (CommonDataSourceExecution.sourceCore nodes)
    (SizedBufferContext.producer (RecursiveBodyProjection.context 1
      [.data 0,.buffer 1,.buffer 2,.buffer 3,.nat n]) 2) [n] 5 (.owner n) := by
  intro h
  have nodeShape : ScopedLend.Graph.nodeAt (CommonDataSourceExecution.sourceCore nodes) 5 = .var 3 := shape
  cases h <;> try simp_all
  case owner =>
    simp_all [SizedBufferContext.producer,SizedBufferContext.mapOwners,
      RecursiveBodyProjection.context,RecursiveBodyProjection.entry]
  case lend => cases ‹SizedCoreExecution.ReadLend _ _ _ _ _ _ _ _› <;> simp_all
  case ownedLend => cases ‹SizedCoreExecution.OwnedReadLend _ _ _ _ _ _ _ _ _ _› <;> simp_all

def staleNodes : CommonDataSource.Graph := nodes ++ #[
  .core (.free 4 11), .core (.free 5 11)]

/-- The released input's old alias is dead although two owners survive. -/
theorem consumed_alias_rejected : ¬ CommonDataSourceRules.Typing staleNodes
    (CommonData.bufferCall 1 2 [.data 0,.buffer 1,.buffer 2,.buffer 3,.nat n])
    1 [n,7] 24 .data := by
  intro h
  have ht : CommonDataSource.nodeAt staleNodes 24 = .core (.free 4 11) := rfl
  have ho : CommonDataSource.nodeAt staleNodes 4 = .core (.var 2) := rfl
  cases h
  case freeBuffer ownerShape lookup bound freeShape body =>
    cases ht.symm.trans freeShape
    cases ho.symm.trans ownerShape
    change some RecursiveLexicalFields.Entry.dead = some (.buffer _) at lookup
    cases lookup
  all_goals simp_all

/-- Returning an input owner does not reauthorize its old lexical alias. -/
theorem returned_alias_rejected : ¬ CommonDataSourceRules.Typing staleNodes
    (CommonData.bufferCall 1 2 [.data 0,.buffer 1,.buffer 2,.buffer 3,.nat n])
    1 [n,7] 25 .data := by
  intro h
  have ht : CommonDataSource.nodeAt staleNodes 25 = .core (.free 5 11) := rfl
  have ho : CommonDataSource.nodeAt staleNodes 5 = .core (.var 3) := rfl
  cases h
  case freeBuffer ownerShape lookup bound freeShape body =>
    cases ht.symm.trans freeShape
    cases ho.symm.trans ownerShape
    change some RecursiveLexicalFields.Entry.dead = some (.buffer _) at lookup
    cases lookup
  all_goals simp_all

def closed (n m : Nat) : List RecursiveLexicalFields.Entry :=
  [.data 0,.buffer 1,.buffer 2,.buffer 3,.nat n,.nat m]

theorem closing (bound : n < 2^64) (other : m < 2^64) : Closes inputs (closed n m) :=
  .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons bound (.cons other .nil)))))

theorem inventory : SymbolicCoreContext.SizesEval (naturalEnv (closed n m)) sizes [n,n,m] :=
  .cons rfl (.cons rfl (.cons rfl .nil))

open CommonData RecursiveLexicalFields RecursiveFieldOwnership HeapLeases LinearHeapPrograms

theorem all_lengths_total (bound : n < 2^64) (other : m < 2^64) (length : trees.length = 1)
    (agreement : Agrees (caps trees owners) (closed n m) env)
    (layout : SizedBufferContext.Layout s.buffers owners [n,n,m])
    (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) :
    ∃ v es t, CommonDataSourceExecution.Eval nodes env 23 s v es t ∧
      Steps s.buffers.heap es t.buffers.heap ∧ Valid t.buffers.heap ∧
      AccountedPost .data t v frame (footprint (caps trees owners)) es :=
  symbolic_call.total_accounted (closing bound other) inventory length agreement layout valid owned fields

theorem every_run_accounted (bound : n < 2^64) (other : m < 2^64) (length : trees.length = 1)
    (agreement : Agrees (caps trees owners) (closed n m) env)
    (layout : SizedBufferContext.Layout s.buffers owners [n,n,m])
    (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners))
    (run : CommonDataSourceExecution.Eval nodes env 23 s v es t) :
    Steps s.buffers.heap es t.buffers.heap ∧ Valid t.buffers.heap ∧
      AccountedPost .data t v frame (footprint (caps trees owners)) es :=
  symbolic_call.every_run_accounted (closing bound other) inventory length agreement layout valid owned fields run

end Jihoo.CommonDataBufferProducerChecks
