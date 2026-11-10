import Jihoo.ScalarCallerEvaluation
import Jihoo.BoundedMir

/-! Bounded translation validation for one closed source/MIR pair. The exporter
association is trusted. Matching result and allocator lifecycle is not a theorem
about all compiler inputs, physical addresses, or full read/write traces. -/
namespace Jihoo.MirCallerValidation

structure Accepted (g : ScopedLend.Graph.Graph) (root type : Nat) (code : BoundedMir.Code) where
  source : ScalarCallerEvaluation.Accepted g root type
  mir : BoundedMir.Accepted code
  same_value : source.value = mir.outcome.value
  same_lifecycle : ScalarCallerEvaluation.lifecycle source.events = mir.outcome.events

def admit (g : ScopedLend.Graph.Graph) (root type : Nat) (code : BoundedMir.Code) (fuel : Nat) :
    Option (Accepted g root type code) := do
  let source ← ScalarCallerEvaluation.admit g root type
  let mir ← BoundedMir.admit code fuel
  if hv : source.value = mir.outcome.value then
    if he : ScalarCallerEvaluation.lifecycle source.events = mir.outcome.events then
      some ⟨source, mir, hv, he⟩
    else none
  else none

/-- A checked pair has a real specified-MIR instruction execution, rather than
only a claimed result or an execution of atomic heap-operation placeholders. -/
theorem mir_execution (a : Accepted g root type code) :
    BoundedMir.Steps code (.running (BoundedMir.initial code)) a.mir.outcome.events
      (.returned a.source.value a.mir.outcome.frame) := by
  rw [a.same_value]
  exact BoundedMir.accepted_execution a.mir

/-- Every complete MIR run of this closed pair has the original source scalar
and allocation/free lifecycle. Initialization stores, other writes and reads are
not included in this comparison. Final MIR no-live-object status is checked
independently, not inferred from lifecycle equality alone. -/
theorem all_returns (a : Accepted g root type code)
    (run : BoundedMir.Steps code (.running (BoundedMir.initial code)) events (.returned value frame)) :
    ∃ sourceEvents sourceState,
      ScalarCoreCallers.CoreRuns g [] root [] [] HeapLeases.empty value sourceEvents sourceState ∧
      ScalarCallerEvaluation.sourceLifecycle sourceEvents = events ∧
      BoundedMir.heapEmpty frame = true := by
  obtain ⟨valueEq, frameEq, eventsEq⟩ := BoundedMir.accepted_all_returns a.mir run
  obtain ⟨sourceEvents, sourceState, sourceRun, _, lifecycle⟩ :=
    ScalarCallerEvaluation.accepted_original_lifecycle a.source
  refine ⟨sourceEvents, sourceState, ?_, ?_, ?_⟩
  · rw [valueEq, ← a.same_value]; exact sourceRun
  · exact lifecycle.trans (a.same_lifecycle.trans eventsEq.symm)
  · rw [frameEq]; exact a.mir.no_live_heap

/-- Conversely, every source run in the recognized closed fragment has a MIR
execution with the same scalar and allocator lifecycle, not just one selected
source witness. -/
theorem all_source_runs (a : Accepted g root type code)
    (sourceRun : ScalarCoreCallers.CoreRuns g [] root [] [] HeapLeases.empty value events state) :
    BoundedMir.Steps code (.running (BoundedMir.initial code))
      (ScalarCallerEvaluation.sourceLifecycle events) (.returned value a.mir.outcome.frame) := by
  obtain ⟨valueEq, lifeEq⟩ := ScalarCallerEvaluation.accepted_all_source a.source sourceRun
  rw [valueEq, lifeEq, a.same_lifecycle]
  exact mir_execution a

end Jihoo.MirCallerValidation
