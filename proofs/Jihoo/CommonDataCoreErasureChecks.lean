import Jihoo.CommonDataCoreClosing
import Jihoo.CommonDataBufferProducerChecks
import Jihoo.SymbolicCompositionChecks

/-! Regression coverage reuses source-typed fixtures, deriving their compact
witnesses without assuming any lowering certificate or successful execution. -/
namespace Jihoo.CommonDataCoreErasureChecks
open CommonDataCoreErasure CommonDataCoreSupports

private theorem producer_support : Supports CommonDataBufferProducerChecks.inputs
    [true,true,true,true,true,true] [false,true,true,true,true,true] := by
  intro k e h
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 => cases h; trivial
  | k+6 => simp [CommonDataBufferProducerChecks.inputs] at h

/-- A prefix producer releases one input, returns another and preserves a third
across Data Case/Drop and a split Data application before its final Free. -/
theorem producer_case_split_lowers : ∃ target,
    Lower CommonDataBufferProducerChecks.delayedNodes
      [true,true,true,true,true,true] [false,true,true,true,true,true] 33 target :=
  typing_lowers CommonDataBufferProducerChecks.delayed_free producer_support

private theorem dynamic_support : Supports [.data 0,.nat]
    [true,true] [false,true] := by
  intro k e h
  match k with
  | 0 | 1 => cases h; trivial
  | k+2 => simp at h

theorem dynamic_allocate_case_lowers : ∃ target,
    Lower CommonDataBufferChecks.nodes [true,true] [false,true] 17 target :=
  typing_lowers CommonDataBufferChecks.symbolic_lifecycle dynamic_support

theorem dynamic_allocate_split_free_lowers : ∃ target,
    Lower CommonDataBufferChecks.delayedNodes [true,true] [false,true] 26 target :=
  typing_lowers CommonDataBufferChecks.delayed_free dynamic_support

private theorem effectful_support : Supports [.data 0,.nat,.buffer 1]
    [true,true,true] [false,true,true] := by
  intro k e h
  match k with
  | 0 | 1 | 2 => cases h; trivial
  | k+3 => simp at h

/-- Core applications free a Buffer before returning a scalar, after Data Case
has inserted its two retained fields. Their Core indices omit those fields. -/
theorem case_effectful_application_lowers : ∃ target,
    Lower SymbolicCommonDataChecks.nodes [true,true,true] [false,true,true] 24 target :=
  typing_lowers SymbolicCompositionChecks.case_framed_open effectful_support

private theorem composed_support : Supports [.scalar,.nat,.nat,.nat,.data 0]
    [true,true,true,true,true] [true,true,true,true,false] := by
  intro k e h
  match k with
  | 0 | 1 | 2 | 3 | 4 => cases h; trivial
  | k+5 => simp at h

/-- Full dynamic-length allocation, branches, owned-lend, framed application,
read-lend and frees compose with Data Case/Drop in one compact target. -/
theorem branch_owned_lend_case_preserves : ∃ target,
    Lower SymbolicCompositionChecks.commonGraph
      [true,true,true,true,true] [true,true,true,true,false] 93 target ∧
    ∀ source compacted, Bridge [true,true,true,true,true] [true,true,true,true,false]
      source compacted → ∀ s v es t,
      CommonDataSourceExecution.Eval SymbolicCompositionChecks.commonGraph source 93 s v es t →
      Eval compacted target s v es t :=
  typing_preserves SymbolicCompositionChecks.common_case composed_support

/-- All-length execution/accounting for the composed fixture derives both the
Core mask and environment bridge; no target run or Lower premise is supplied. -/
theorem branch_owned_lend_case_total (hn : n < 2^64) (hm : m < 2^64) (hi : i < 2^64)
    (compaction : CommonDataErasure.Env slots source compacted)
    (length : trees.length = 1)
    (agreement : RecursiveLexicalFields.Agrees (CommonData.caps trees [])
      [.scalar,.nat i,.nat m,.nat n,.data 0] source)
    (layout : SizedBufferContext.Layout s.buffers [] [])
    (valid : HeapLeases.Valid s.buffers.heap)
    (owned : LinearHeapPrograms.Owns s.buffers.heap
      (RecursiveLexicalFields.footprint (CommonData.caps trees []) ++ frame))
    (fields : RecursiveLexicalFields.Fields s.cells (CommonData.caps trees [])) :
    ∃ target, Lower SymbolicCompositionChecks.commonGraph slots
      (CommonDataEnvironmentCompaction.coreMask source) 93 target ∧ ∃ v es t,
      Eval compacted target s v es t ∧ HeapLeases.Steps s.buffers.heap es t.buffers.heap ∧
      HeapLeases.Valid t.buffers.heap ∧ CommonData.AccountedPost .scalar t v frame
        (RecursiveLexicalFields.footprint (CommonData.caps trees [])) es :=
  closed_total_accounted SymbolicCompositionChecks.common_case compaction
    (closed := [.scalar,.nat i,.nat m,.nat n,.data 0])
    (.cons trivial (.cons hi (.cons hm (.cons hn (.cons rfl .nil))))) .nil
    length agreement layout valid owned fields

/-- Concrete Data remains in the common runtime while its Core view is ghost. -/
theorem interleaved_bridge : Bridge [true,true,true] [false,true,true]
    [.data ref,.nat n,.buffer x] [.data ref,.nat n,.buffer x] :=
  ⟨.keep (.keep (.keep .nil)),
    .consGhost (.consKeep (.nat n) (.consKeep (.owner x) .nil))⟩

theorem distinct_index_spaces :
    CommonDataErasure.position [true,true,true] 2 = some 2 ∧
    SizedErasure.rank [false,true,true] 2 = 1 := by decide

end Jihoo.CommonDataCoreErasureChecks
