import Jihoo.CommonDataCoreLowering

/-! Closing and ordinary CommonData compaction supply the entire lowering
interface. The Core mask is computed from runtime shape, including stale aliases. -/
namespace Jihoo.CommonDataCoreErasure
open RecursiveLexicalFields RecursiveBodyProjection CommonDataErasure
open CommonDataCoreSupports SymbolicCommonDataContext
open CommonData RecursiveFieldOwnership HeapLeases LinearHeapPrograms

private theorem retained {k : Nat} {v : Value} (h : CommonDataErasure.Env slots source compacted)
    (found : source[k]? = some v) (observable : v ≠ .ghost) : slots[k]? = some true := by
  induction h generalizing k with
  | nil => simp at found
  | keep h ih => cases k with
    | zero => rfl
    | succ k => exact ih found
  | erase h ih => cases k with
    | zero => exact False.elim (observable (Option.some.inj found).symm)
    | succ k => exact ih found

/-- No additional static or execution certificate is required at the endpoint. -/
theorem supports_of_closing {resources : List Capability} (closing : Closes ctx closed)
    (agreement : Agrees resources closed source)
    (compaction : CommonDataErasure.Env slots source compacted) :
    Supports ctx slots (CommonDataEnvironmentCompaction.coreMask source) := by
  intro k e found
  obtain ⟨c, hc, related⟩ := closing.lookup found
  obtain ⟨v, hv, value⟩ := agreement.lookup hc
  have keep (nonGhost : v ≠ .ghost) := retained compaction hv nonGhost
  have coreKeep {w : SizedErasure.Value} (equal : RecursiveBodyProjection.value v = w.embed) :
      (CommonDataEnvironmentCompaction.coreMask source)[k]? = some true := by
    apply (CommonDataEnvironmentCompaction.core_related source).retained_of_lookup (v := w)
    simp [environment, List.getElem?_map, hv, equal]
  cases e <;> cases c <;> cases v <;>
    simp_all [SymbolicCommonDataContext.Entry.Closes, RecursiveLexicalFields.Rel,
      CommonDataCoreSupports.EntrySupports]
  all_goals first
    | exact coreKeep (w := .nat _) rfl
    | exact coreKeep (w := .scalar _) rfl
    | exact coreKeep (w := .owner _) rfl

/-- Complete typed endpoint. Both structural lowering and its bridge are derived;
only the existing closing, ownership and common environment invariants remain. -/
theorem closed_total_accounted
    (typed : SymbolicCommonDataSource.Typing g ctx count sizes term kind)
    (compaction : CommonDataErasure.Env slots source compacted)
    (closing : Closes ctx closed)
    (inventory : SymbolicCoreContext.SizesEval (naturalEnv closed) sizes concrete)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) closed source)
    (layout : SizedBufferContext.Layout s.buffers owners concrete) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) :
    ∃ target, Lower g slots (CommonDataEnvironmentCompaction.coreMask source) term target ∧
      ∃ v es t, Eval compacted target s v es t ∧ Steps s.buffers.heap es t.buffers.heap ∧
      Valid t.buffers.heap ∧ AccountedPost kind t v frame (footprint (caps trees owners)) es :=
  typing_total_accounted typed (supports_of_closing closing agreement compaction)
    (Bridge.of_common compaction) closing inventory length agreement layout valid owned fields

end Jihoo.CommonDataCoreErasure
