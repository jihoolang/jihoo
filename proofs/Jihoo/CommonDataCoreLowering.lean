import Jihoo.CommonDataCoreErasure
import Jihoo.CommonDataCoreSupports

/-! Structural lowering follows symbolic typing, independently of execution. -/
namespace Jihoo.CommonDataCoreErasure
open CommonDataCoreSupports SymbolicCommonDataContext
open RecursiveLexicalFields RecursiveFieldOwnership HeapLeases LinearHeapPrograms CommonData

/-- Both Core branches and all common continuations receive structural witnesses.
The premises describe lexical retention only, never compiler success. -/
theorem typing_lowers
    (typed : SymbolicCommonDataSource.Typing g ctx count sizes term kind)
    (supported : Supports ctx slots mask) :
    ∃ target, Lower g slots mask term target := by
  induction typed generalizing slots mask with
  | literal shape bound => exact ⟨_, .literal shape⟩
  | empty shape => exact ⟨_, .empty shape⟩
  | dataVar shape lookup =>
    exact ⟨_, .var shape (position_of_kept (supported.data_kept lookup))⟩
  | construct shape left li right ri =>
    exact ⟨_, .construct shape left (position_of_kept (supported.data_kept li))
      right (position_of_kept (supported.data_kept ri))⟩
  | bufferLet shape fn ty arg body ih =>
    obtain ⟨a, ha⟩ := SymbolicCoreCompaction.typing_erases arg supported.project
    obtain ⟨b, hb⟩ := ih supported.continuation
    exact ⟨_, .scalarLet shape fn ty ha hb⟩
  | allocate shape fn ty annotation alloc len init body ih =>
    obtain ⟨a, ha⟩ := SymbolicCoreCompaction.index_erases len supported.project
    obtain ⟨v, hv⟩ := SymbolicCoreCompaction.scalar_erases init supported.project
    obtain ⟨b, hb⟩ := ih supported.freshBuffer
    exact ⟨_, .ownerLet shape fn ty
      (.allocate (CommonDataBufferErasure.core_shape alloc) ha hv) hb⟩
  | bufferApp shape fn ty limit annotation arg body ih =>
    obtain ⟨a, ha⟩ := SymbolicCoreCompaction.typing_erases arg supported.project.mapOwners
    obtain ⟨b, hb⟩ := ih supported.bufferCall
    exact ⟨_, .ownerLet shape fn ty ha hb⟩
  | freeBuffer shape owner lookup bound body ih =>
    obtain ⟨b, hb⟩ := ih supported.consumeBuffer
    exact ⟨_, .freeBuffer shape owner (position_of_kept (supported.buffer_kept lookup)) hb⟩
  | dataLet shape fn ty arg body ia ib =>
    obtain ⟨a, ha⟩ := ia supported
    obtain ⟨b, hb⟩ := ib supported.dataContinuation
    exact ⟨_, .letData shape fn ty ha hb⟩
  | dataLetSplit counts sizes shape fn ty arg body ia ib =>
    obtain ⟨a, ha⟩ := ia supported.argumentContext
    obtain ⟨b, hb⟩ := ib supported.capturedContext
    exact ⟨_, .letData shape fn ty ha hb⟩
  | drop shape owner lookup body ih =>
    obtain ⟨b, hb⟩ := ih supported.removeHead
    exact ⟨_, .drop shape owner (position_of_kept (supported.data_kept lookup)) hb⟩
  | caseTree shape motive branch scrutinee lookup nil node ia ib =>
    obtain ⟨a, ha⟩ := ia supported.removeHead
    obtain ⟨b, hb⟩ := ib supported.bindContext
    exact ⟨_, .caseTree shape motive branch scrutinee
      (position_of_kept (supported.data_kept lookup)) ha hb⟩

/-- One target works for every closing runtime and source execution. -/
theorem typing_preserves
    (typed : SymbolicCommonDataSource.Typing g ctx count sizes term kind)
    (supported : Supports ctx slots mask) :
    ∃ target, Lower g slots mask term target ∧
      ∀ source compacted, Bridge slots mask source compacted →
      ∀ s v es t, CommonDataSourceExecution.Eval g source term s v es t →
        Eval compacted target s v es t := by
  obtain ⟨target, lower⟩ := typing_lowers typed supported
  exact ⟨target, lower, fun _ _ bridge _ _ _ _ run => lower.preserves bridge run⟩

/-- Typed totality, exact events, heap validity and Data/Buffer resource accounting.
The target is obtained from symbolic typing, not supplied as an arbitrary Lower
certificate. The independent bridge supplies only environment correspondence. -/
theorem typing_total_accounted
    (typed : SymbolicCommonDataSource.Typing g ctx count sizes term kind)
    (supported : Supports ctx slots mask)
    (bridge : Bridge slots mask source compacted)
    (closing : Closes ctx closed)
    (inventory : SymbolicCoreContext.SizesEval (naturalEnv closed) sizes concrete)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) closed source)
    (layout : SizedBufferContext.Layout s.buffers owners concrete) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) :
    ∃ target, Lower g slots mask term target ∧ ∃ v es t,
      Eval compacted target s v es t ∧ Steps s.buffers.heap es t.buffers.heap ∧
      Valid t.buffers.heap ∧ AccountedPost kind t v frame (footprint (caps trees owners)) es := by
  obtain ⟨target, lower⟩ := typing_lowers typed supported
  obtain ⟨v,es,t,run,steps,valid,post⟩ :=
    typed.total_accounted closing inventory length agreement layout valid owned fields
  exact ⟨target,lower,v,es,t,lower.preserves bridge run,steps,valid,post⟩

end Jihoo.CommonDataCoreErasure
