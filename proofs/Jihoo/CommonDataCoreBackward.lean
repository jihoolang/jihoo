import Jihoo.CommonDataCoreCompilerCompleteness

/-! Exact backward simulation for the fixed binary Tree common target.
This does not establish CommonData to MIR or native refinement. -/
namespace Jihoo.CommonDataCoreErasure
open RecursiveLexicalFields RecursiveFieldRuntime CommonDataSourceRules
open HeapLeases LinearHeapPrograms CommonDataErasure RecursiveBodyProjection
open CommonDataCoreSupports SymbolicCommonDataContext
open CommonData RecursiveFieldOwnership

variable {root : Nat}

/-- Target entry alone reconstructs source entry, including both child bindings. -/
theorem Bridge.enter_backward (h : Bridge slots mask source compacted)
    (pos : position slots k = some j)
    (entered : RecursiveLexicalFields.enter s compacted j 0 = some (target,parent)) :
    ∃ opened, RecursiveLexicalFields.enter s source k 0 = some (opened,parent) ∧
      Bridge (true :: true :: slots) (false :: false :: mask) opened target := by
  have lookup := h.common.lookup pos
  cases found : compacted[j]? with
  | none => simp [RecursiveLexicalFields.enter, found] at entered
  | some value =>
    cases value <;> try { simp [RecursiveLexicalFields.enter, found] at entered }
    case data ref =>
      cases ref with
      | none => simp [RecursiveLexicalFields.enter, found] at entered
      | some x =>
        by_cases live : s.heap.live x = true
        · cases cellFound : s.cells x with
          | none => simp [RecursiveLexicalFields.enter, found, live, cellFound] at entered
          | some cell =>
            simp [RecursiveLexicalFields.enter, found, live, cellFound] at entered
            rcases entered with ⟨rfl, rfl⟩
            exact ⟨bindValues 0 cell source,
              by simp [RecursiveLexicalFields.enter, ← lookup, found, live, cellFound], h.data.data⟩
        · simp [RecursiveLexicalFields.enter, found, live] at entered

/-- No source success, typing, or target determinism premise is needed. -/
theorem Lower.backward (lower : Lower g slots mask term target)
    (agreement : Bridge slots mask source compacted)
    (run : Eval compacted target s v es t) :
    CommonDataSourceExecution.Eval g source term s v es t := by
  induction lower generalizing source compacted s v es t with
  | scalarLet shape fn ty arg body ih =>
    cases run
    exact .bufferLet shape fn ty (arg.backward agreement.core (by assumption))
      (ih agreement.scalar (by assumption))
  | ownerLet shape fn ty arg body ih =>
    cases run
    exact .allocate shape fn ty (arg.backward agreement.core (by assumption))
      (ih agreement.owner (by assumption))
  | literal shape => cases run; exact .literal shape
  | empty shape => cases run; exact .empty shape
  | var shape pos =>
    cases run
    exact .dataVar shape ((agreement.common.lookup pos).symm.trans (by assumption))
  | construct shape left lp right rp =>
    cases run
    exact .construct shape left ((agreement.common.lookup lp).symm.trans (by assumption))
      right ((agreement.common.lookup rp).symm.trans (by assumption))
  | letData shape fn ty arg body ia ib =>
    cases run
    exact .dataLet shape fn ty (ia agreement (by assumption)) (ib agreement.data (by assumption))
  | drop shape owner pos body ih =>
    cases run
    exact .drop shape owner ((agreement.common.lookup pos).symm.trans (by assumption))
      (by assumption) (ih agreement (by assumption))
  | freeBuffer shape owner pos body ih =>
    cases run
    exact .freeBuffer shape owner ((agreement.common.lookup pos).symm.trans (by assumption))
      (ih agreement (by assumption))
  | caseTree shape motive branch scrutinee pos nil node ia ib =>
    cases run with
    | emptyCase found run =>
      exact .emptyCase shape motive branch scrutinee
        ((agreement.common.lookup pos).symm.trans found) (ia agreement run)
    | nodeCase entered run =>
      obtain ⟨opened, entered, related⟩ := agreement.enter_backward pos entered
      exact .nodeCase shape motive branch scrutinee entered (ib related run)

theorem Lower.adequate (lower : Lower g slots mask term target)
    (agreement : Bridge slots mask source compacted) :
    Eval compacted target s v es t ↔ CommonDataSourceExecution.Eval g source term s v es t :=
  ⟨lower.backward agreement, lower.preserves agreement⟩

theorem compileTarget_adequate
    (success : compileTarget g fuel slots mask root = some target)
    (agreement : Bridge slots mask source compacted) :
    Eval compacted target s v es t ↔ CommonDataSourceExecution.Eval g source root s v es t :=
  (compileTarget_sound success).adequate agreement

/-- Every observed target run inherits source safety and full resource accounting. -/
theorem compileTarget_every_run_accounted
    (success : compileTarget g fuel slots mask root = some target)
    (bridge : Bridge slots mask source compacted)
    (typed : SymbolicCommonDataSource.Typing g ctx count sizes root kind)
    (closing : Closes ctx closed)
    (inventory : SymbolicCoreContext.SizesEval (naturalEnv closed) sizes concrete)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) closed source)
    (layout : SizedBufferContext.Layout s.buffers owners concrete) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners))
    (run : Eval compacted target s v es t) :
    Steps s.buffers.heap es t.buffers.heap ∧ Valid t.buffers.heap ∧
      AccountedPost kind t v frame (footprint (caps trees owners)) es :=
  typed.every_run_accounted closing inventory length agreement layout valid owned fields
    ((compileTarget_sound success).backward bridge run)

/-- One compiled target for all sufficient fuel, exact adequacy, totality, and
safety/accounting of every target run under the existing closing assumptions. -/
theorem compile_closed_adequate_accounted
    (typed : SymbolicCommonDataSource.Typing g ctx count sizes root kind)
    (compaction : CommonDataErasure.Env slots source compacted)
    (closing : Closes ctx closed)
    (inventory : SymbolicCoreContext.SizesEval (naturalEnv closed) sizes concrete)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) closed source)
    (layout : SizedBufferContext.Layout s.buffers owners concrete) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) :
    ∃ target bound,
      (∀ fuel, bound ≤ fuel → compileTarget g fuel slots
        (CommonDataEnvironmentCompaction.coreMask source) root = some target) ∧
      (∀ s v es t, Eval compacted target s v es t ↔
        CommonDataSourceExecution.Eval g source root s v es t) ∧
      (∃ v es t, Eval compacted target s v es t) ∧
      (∀ v es t, Eval compacted target s v es t →
        Steps s.buffers.heap es t.buffers.heap ∧ Valid t.buffers.heap ∧
        AccountedPost kind t v frame (footprint (caps trees owners)) es) := by
  obtain ⟨target, lower⟩ := typing_lowers typed (supports_of_closing closing agreement compaction)
  obtain ⟨bound, complete⟩ := lower.compileTarget_complete
  have bridge := Bridge.of_common compaction
  obtain ⟨v, es, t, run, _⟩ :=
    typed.total_accounted closing inventory length agreement layout valid owned fields
  refine ⟨target, bound, complete, fun _ _ _ _ => lower.adequate bridge,
    ⟨v, es, t, lower.preserves bridge run⟩, ?_⟩
  intro v es t observed
  exact typed.every_run_accounted closing inventory length agreement layout valid owned fields
    (lower.backward bridge observed)

end Jihoo.CommonDataCoreErasure
