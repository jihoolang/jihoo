import Jihoo.SymbolicCommonDataSource
import Jihoo.CommonDataSourceRulesChecks

namespace Jihoo.SymbolicCommonDataChecks
open SymbolicCommonDataContext SymbolicCommonDataSource
open SymbolicCoreContext (shiftSizes)

/-- The same open Buffer length is checked before and after both Case binders. -/
def nodes : CommonDataSource.Graph := #[
  .ind 0 [], .core .i64, .core (.integer 9),
  .core (.var 0), .core (.var 1), .core (.var 2), .core (.var 3), .core (.var 4),
  .core (.buffer 4), .core (.free 3 2), .core (.lam false 8 9), .core (.app 10 5),
  .core (.lam false 1 2), .core (.app 12 11),
  .core (.buffer 6), .core (.lam false 14 9), .core (.app 15 7),
  .drop 0 4 2, .drop 0 5 17, .core (.lam false 1 18), .core (.app 19 16),
  .core (.lam false 0 20), .core (.lam false 0 21), .core (.lam false 0 1),
  .caseOf 0 23 [13,22] 3]

local macro "case_shape" : term => `(by simp [ScopedLend.Graph.nodeAt,
  CommonDataSourceExecution.sourceCore, CommonDataSourceExecution.coreNode, nodes])

theorem case_open : Typing nodes [.data 0,.nat,.buffer 1] 1 [.var 1] 24 .scalar := by
  apply Typing.caseTree rfl rfl rfl rfl rfl
  · apply Typing.bufferLet rfl rfl rfl
    · exact .ownedLet (function := 10) (argument := 5) (domain := 8) (k := 2) (body := 9) (slot := 0) case_shape case_shape case_shape rfl rfl
        ⟨4,case_shape,⟨.var case_shape,.var rfl⟩⟩
        (.free (owner := 3) (k := 0) (body := 2) (slot := 0) case_shape case_shape rfl (by decide) (.literal (root := 2) (v := 9) case_shape (by decide)))
    · exact .literal rfl (by decide)
  · apply Typing.bufferLet rfl rfl rfl
    · exact .ownedLet (function := 15) (argument := 7) (domain := 14) (k := 4) (body := 9) (slot := 0) case_shape case_shape case_shape rfl rfl
        ⟨6,case_shape,⟨.var case_shape,.var rfl⟩⟩
        (.free (owner := 3) (k := 0) (body := 2) (slot := 0) case_shape case_shape rfl (by decide) (.literal (root := 2) (v := 9) case_shape (by decide)))
    · exact .drop rfl rfl rfl (.drop rfl rfl rfl (.literal rfl (by decide)))

theorem case_all_lengths (n : Nat) (bound : n < 2^64) :
    CommonDataSourceRules.Typing nodes [.data 0,.nat n,.buffer 1] 1 [n] 24 .scalar :=
  case_open.instantiate (.cons rfl (.cons bound (.cons rfl .nil))) (.cons rfl .nil)

theorem case_two_closings :
    CommonDataSourceRules.Typing nodes [.data 0,.nat 0,.buffer 1] 1 [0] 24 .scalar ∧
    CommonDataSourceRules.Typing nodes [.data 0,.nat 17,.buffer 1] 1 [17] 24 .scalar :=
  ⟨case_all_lengths 0 (by decide),case_all_lengths 17 (by decide)⟩

def mixed : Context := [.data 0,.data 1,.buffer 2,.buffer 3,.nat,.data 0,.buffer 2]

def splitNodes : CommonDataSource.Graph := #[
  .ind 0 [], .core .i64, .core (.integer 9),
  .core (.var 0), .core (.var 1), .core (.var 2), .core (.var 3), .core (.var 4), .core (.var 5),
  .core (.free 3 2), .core (.buffer 7), .core (.lam false 10 9), .core (.app 11 5),
  .core (.lam false 1 4), .core (.app 13 12),
  .core (.buffer 8), .core (.lam false 15 9), .core (.app 16 7),
  .con 0 1 [4,6], .core (.lam false 1 18), .core (.app 19 17),
  .core (.lam false 0 20), .core (.app 21 14)]

local macro "split_shape" : term => `(by simp [ScopedLend.Graph.nodeAt,
  CommonDataSourceExecution.sourceCore, CommonDataSourceExecution.coreNode, splitNodes])

theorem split_open : Typing splitNodes mixed 2 [.var 4,.var 4] 22 .data := by
  apply Typing.dataLetSplit (activeCount := 1) (retainedCount := 1)
    (usedSizes := [.var 4]) (savedSizes := [.var 4]) rfl rfl rfl rfl rfl
  · apply Typing.bufferLet rfl rfl rfl
    · exact .ownedLet (function := 11) (argument := 5) (domain := 10) (k := 2) (body := 9) (slot := 0) split_shape split_shape split_shape rfl rfl
        ⟨7,split_shape,⟨.var split_shape,.var rfl⟩⟩
        (.free (owner := 3) (k := 0) (body := 2) (slot := 0) split_shape split_shape rfl (by decide) (.literal (root := 2) (v := 9) split_shape (by decide)))
    · exact .dataVar rfl rfl
  · apply Typing.bufferLet rfl rfl rfl
    · exact .ownedLet (function := 16) (argument := 7) (domain := 15) (k := 4) (body := 9) (slot := 0) split_shape split_shape split_shape rfl rfl
        ⟨8,split_shape,⟨.var split_shape,.var rfl⟩⟩
        (.free (owner := 3) (k := 0) (body := 2) (slot := 0) split_shape split_shape rfl (by decide) (.literal (root := 2) (v := 9) split_shape (by decide)))
    · exact .construct rfl rfl rfl rfl rfl

theorem split_all_lengths (n : Nat) (bound : n < 2^64) :
    CommonDataSourceRules.Typing splitNodes
      [.data 0,.data 1,.buffer 2,.buffer 3,.nat n,.data 0,.buffer 2] 2 [n,n] 22 .data :=
  split_open.instantiate
    (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons bound (.cons rfl (.cons rfl .nil)))))))
    (.cons rfl (.cons rfl .nil))

theorem context_transitions :
    bindContext [.data 0,.nat,.buffer 1] = [.data 1,.data 0,.dead,.nat,.buffer 2] ∧
    argumentContext 1 1 1 mixed = [.data 0,.dead,.buffer 1,.dead,.nat,.data 0,.buffer 1] ∧
    capturedContext 1 1 1 mixed = [.data 0,.dead,.data 1,.dead,.buffer 2,.nat,.dead,.dead] ∧
    shiftSizes (shiftSizes [.var 1]) = [.var 3] ∧ shiftSizes [.var 4] = [.var 5] := by decide

/-- An unshifted Case index points at a Data field, not the original natural. -/
theorem case_wrong_index : ¬ SymbolicCoreTyping.Index (CommonDataSourceExecution.sourceCore nodes)
    (project 2 (bindContext [.data 0,.nat,.buffer 1])) 4 (.var 1) := by
  intro h
  cases h.available with
  | var lookup => change (some SymbolicCoreContext.Entry.dead) = some .nat at lookup; contradiction

theorem split_wrong_index : ¬ SymbolicCoreTyping.Index (CommonDataSourceExecution.sourceCore splitNodes)
    (project 2 (capturedContext 1 1 1 mixed)) 7 (.var 4) := by
  intro h
  cases h.available with
  | var lookup => change (some (SymbolicCoreContext.Entry.owner 0)) = some .nat at lookup; contradiction

/-- Both aliases of the consumed parent are dead, while field order is retained. -/
theorem parent_aliases : (bindContext [.data 0,.data 0,.nat])[2]? = some .dead ∧
    (bindContext [.data 0,.data 0,.nat])[3]? = some .dead := by decide

theorem split_aliases : (capturedContext 1 1 1 mixed)[1]? = some .dead ∧
    (capturedContext 1 1 1 mixed)[6]? = some .dead ∧
    (capturedContext 1 1 1 mixed)[3]? = some .dead ∧
    (capturedContext 1 1 1 mixed)[7]? = some .dead := by decide

theorem parent_use_rejected : ¬ Typing nodes (bindContext [.data 0,.data 0,.nat]) 1 [] 5 .data := by
  intro h
  have shape : CommonDataSource.nodeAt nodes 5 = .core (.var 2) := rfl
  cases h <;> simp_all [bindContext,retireEntry]
  all_goals subst_vars; simp_all

theorem consumed_data_rejected : ¬ Typing splitNodes (capturedContext 1 1 1 mixed) 1 [] 4 .data := by
  intro h
  have shape : CommonDataSource.nodeAt splitNodes 4 = .core (.var 1) := rfl
  cases h <;> simp_all [capturedContext,capturedEntry,mixed]
  all_goals subst_vars; simp_all

theorem consumed_buffer_rejected : ¬ SymbolicCoreTyping.Typing
    (CommonDataSourceExecution.sourceCore splitNodes) (project 2 (capturedContext 1 1 1 mixed))
    [.var 5] 6 (.owner (.var 5)) := by
  intro h
  have shape : ScopedLend.Graph.nodeAt (CommonDataSourceExecution.sourceCore splitNodes) 6 = .var 3 := split_shape
  generalize he : SymbolicCoreContext.Result.owner (.var 5) = result at h
  cases h <;> simp_all [project,projectEntry,capturedContext,capturedEntry,mixed]
  all_goals subst_vars
  all_goals rename_i read _; cases read <;> simp_all

/-- All the old non-Buffer rules remain constructively usable. -/
theorem computed_nil : Typing CommonDataSourceRulesChecks.nodes [.data 0] 1 [] 24 .data :=
  .caseTree rfl rfl rfl rfl rfl
    (.dataLet rfl rfl rfl (.empty rfl) (.drop rfl rfl rfl (.empty rfl)))
    (.construct rfl rfl rfl rfl rfl)


/-- Used and saved inventories refer to DIFFERENT natural parameters. -/
def distinctNodes : CommonDataSource.Graph := splitNodes.set! 8 (.core (.var 8))
local macro "distinct_shape" : term => `(by simp [ScopedLend.Graph.nodeAt,
  CommonDataSourceExecution.sourceCore, CommonDataSourceExecution.coreNode, distinctNodes, splitNodes])

theorem distinct_split_open : Typing distinctNodes (mixed ++ [.nat]) 2 [.var 4,.var 7] 22 .data := by
  apply Typing.dataLetSplit (activeCount := 1) (retainedCount := 1)
    (usedSizes := [.var 4]) (savedSizes := [.var 7]) rfl rfl rfl rfl rfl
  · apply Typing.bufferLet rfl rfl rfl
    · exact .ownedLet (function := 11) (argument := 5) (domain := 10) (k := 2) (body := 9) (slot := 0) distinct_shape distinct_shape distinct_shape rfl rfl
        ⟨7,distinct_shape,⟨.var distinct_shape,.var rfl⟩⟩
        (.free (owner := 3) (k := 0) (body := 2) (slot := 0) distinct_shape distinct_shape rfl (by decide) (.literal (root := 2) (v := 9) distinct_shape (by decide)))
    · exact .dataVar rfl rfl
  · apply Typing.bufferLet rfl rfl rfl
    · exact .ownedLet (function := 16) (argument := 7) (domain := 15) (k := 4) (body := 9) (slot := 0) distinct_shape distinct_shape distinct_shape rfl rfl
        ⟨8,distinct_shape,⟨.var distinct_shape,.var rfl⟩⟩
        (.free (owner := 3) (k := 0) (body := 2) (slot := 0) distinct_shape distinct_shape rfl (by decide) (.literal (root := 2) (v := 9) distinct_shape (by decide)))
    · exact .construct rfl rfl rfl rfl rfl

theorem distinct_split_lengths (n m : Nat) (bn : n < 2^64) (bm : m < 2^64) :
    CommonDataSourceRules.Typing distinctNodes
      [.data 0,.data 1,.buffer 2,.buffer 3,.nat n,.data 0,.buffer 2,.nat m] 2 [n,m] 22 .data :=
  distinct_split_open.instantiate
    (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons bn (.cons rfl (.cons rfl (.cons bm .nil))))))))
    (.cons rfl (.cons rfl .nil))

theorem distinct_split_zero_nonzero :
    CommonDataSourceRules.Typing distinctNodes
      [.data 0,.data 1,.buffer 2,.buffer 3,.nat 0,.data 0,.buffer 2,.nat 17] 2 [0,17] 22 .data :=
  distinct_split_lengths 0 17 (by decide) (by decide)

theorem wrong_motive_rejected : ¬ Typing nodes [.data 0,.nat,.buffer 1] 1 [.var 1] 24 .data := by
  intro h
  have closed := h.instantiate (closed := [.data 0,.nat 0,.buffer 1]) (concrete := [0])
    (.cons rfl (.cons (show 0 < 2^64 by decide) (.cons rfl .nil))) (.cons rfl .nil)
  have motive := closed.case_motive (show CommonDataSource.nodeAt nodes 24 = .caseOf 0 23 [13,22] 3 from rfl)
  contradiction

theorem wrong_branch_rejected : ¬ Typing CommonDataSourceRulesChecks.nodes [.data 0] 1 [] 42 .scalar := by
  intro h
  exact CommonDataSourceRulesChecks.node_kind_mismatch (h.instantiate (.cons rfl .nil) .nil)

theorem missing_index_rejected : ¬ SymbolicCoreTyping.Index (CommonDataSourceExecution.sourceCore nodes)
    (project 0 [.nat]) 4 (.var 8) := by
  intro h
  cases h.available with
  | var lookup => change (none : Option SymbolicCoreContext.Entry) = some .nat at lookup; contradiction

end Jihoo.SymbolicCommonDataChecks
