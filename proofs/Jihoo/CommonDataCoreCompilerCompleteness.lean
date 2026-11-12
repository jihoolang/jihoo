import Jihoo.CommonDataCoreCompiler
import Jihoo.SymbolicCoreCompactionCompiler
import Jihoo.CommonDataCoreClosing

/-! Completeness is structural, not a successful-run premise. Typing supplies a
finite lowering derivation; closing and ownership supply execution/accounting. -/
namespace Jihoo.CommonDataCoreErasure
open RecursiveLexicalFields RecursiveBodyProjection CommonDataErasure
open CommonDataCoreSupports SymbolicCommonDataContext
open CommonData RecursiveFieldOwnership HeapLeases LinearHeapPrograms

theorem Lower.compile_complete (h : Lower g slots mask root target) :
    ∃ bound, ∀ fuel, bound ≤ fuel → compile g fuel slots mask root = some ⟨target, h⟩ := by
  induction h with
  | scalarLet shape lam ty a b ib =>
    obtain ⟨na, ha⟩ := a.compile_complete
    obtain ⟨nb, hb⟩ := ib
    refine ⟨max na nb + 1, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [compile]
      split <;> rename_i heq
      all_goals first | cases shape.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      split <;> rename_i heq
      all_goals first | cases lam.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      split <;> rename_i heq
      all_goals first | cases ty.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      simp [ha fuel (by omega), hb fuel (by omega)]
  | ownerLet shape lam ty a b ib =>
    obtain ⟨na, ha⟩ := a.compile_complete
    obtain ⟨nb, hb⟩ := ib
    refine ⟨max na nb + 1, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [compile]
      split <;> rename_i heq
      all_goals first | cases shape.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      split <;> rename_i heq
      all_goals first | cases lam.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      split <;> rename_i heq
      all_goals first | cases ty.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      simp [ha fuel (by omega), hb fuel (by omega)]
  | literal shape =>
    refine ⟨1, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [compile]
      split <;> rename_i heq
      all_goals first | cases shape.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      rfl
  | empty shape =>
    refine ⟨1, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [compile]
      split <;> rename_i heq
      all_goals first | cases shape.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      rfl
  | var shape pos =>
    refine ⟨1, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [compile]
      split <;> rename_i heq
      all_goals first | cases shape.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      split <;> rename_i heq
      all_goals first | cases pos.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      rfl
  | construct shape left lp right rp =>
    refine ⟨1, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [compile]
      split <;> rename_i heq
      all_goals first | cases shape.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      split
      all_goals first
        | rename_i h1 h2; cases left.symm.trans h1; cases right.symm.trans h2
        | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      split
      all_goals first
        | rename_i h1 h2; cases lp.symm.trans h1; cases rp.symm.trans h2
        | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      rfl
  | letData shape lam ty a b ia ib =>
    obtain ⟨na, ha⟩ := ia
    obtain ⟨nb, hb⟩ := ib
    refine ⟨max na nb + 1, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [compile]
      split <;> rename_i heq
      all_goals first | cases shape.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      split <;> rename_i heq
      all_goals first | cases lam.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      split <;> rename_i heq
      all_goals first | cases ty.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      simp [ha fuel (by omega), hb fuel (by omega)]
  | drop shape variableShape pos b ib =>
    obtain ⟨nb, hb⟩ := ib
    refine ⟨nb + 1, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [compile]
      split <;> rename_i heq
      all_goals first | cases shape.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      split <;> rename_i heq
      all_goals first | cases variableShape.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      split <;> rename_i heq
      all_goals first | cases pos.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      simp [hb fuel (by omega)]
  | freeBuffer shape variableShape pos b ib =>
    obtain ⟨nb, hb⟩ := ib
    refine ⟨nb + 1, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [compile]
      split <;> rename_i heq
      all_goals first | cases shape.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      split <;> rename_i heq
      all_goals first | cases variableShape.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      split <;> rename_i heq
      all_goals first | cases pos.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      simp [hb fuel (by omega)]
  | caseTree shape motive branch variableShape pos a b ia ib =>
    obtain ⟨na, ha⟩ := ia
    obtain ⟨nb, hb⟩ := ib
    refine ⟨max na nb + 1, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [compile]
      split <;> rename_i heq
      all_goals first | cases shape.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      split
      all_goals first
        | rename_i h1 h2; cases motive.symm.trans h1; cases branch.symm.trans h2
        | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      split <;> rename_i heq
      all_goals first | cases variableShape.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      split <;> rename_i heq
      all_goals first | cases pos.symm.trans heq | (simp_all <;> (exfalso; apply_assumption <;> rfl))
      simp [ha fuel (by omega), hb fuel (by omega)]

/-- One fixed target, for every fuel above a structural bound. -/
theorem Lower.compileTarget_complete (h : Lower g slots mask root target) :
    ∃ bound, ∀ fuel, bound ≤ fuel → compileTarget g fuel slots mask root = some target := by
  obtain ⟨bound, complete⟩ := h.compile_complete
  exact ⟨bound, fun fuel enough => by simp [compileTarget, complete fuel enough]⟩

theorem typing_compiles
    (typed : SymbolicCommonDataSource.Typing g ctx count sizes root kind)
    (supported : Supports ctx slots mask) :
    ∃ target bound, ∀ fuel, bound ≤ fuel → compileTarget g fuel slots mask root = some target := by
  obtain ⟨target, lower⟩ := typing_lowers typed supported
  obtain ⟨bound, complete⟩ := lower.compileTarget_complete
  exact ⟨target, bound, complete⟩

/-- No target success or source run is assumed. The existing closing, layout,
ownership, field and environment invariants suffice for compilation and a run. -/
theorem compile_closed_total_accounted
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
      ∃ v es t, Eval compacted target s v es t ∧ Steps s.buffers.heap es t.buffers.heap ∧
      Valid t.buffers.heap ∧ AccountedPost kind t v frame (footprint (caps trees owners)) es := by
  obtain ⟨target, lower, run⟩ := closed_total_accounted typed compaction closing inventory
    length agreement layout valid owned fields
  obtain ⟨bound, complete⟩ := lower.compileTarget_complete
  exact ⟨target, bound, complete, run⟩

end Jihoo.CommonDataCoreErasure
