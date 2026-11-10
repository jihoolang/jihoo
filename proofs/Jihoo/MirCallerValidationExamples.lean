import Jihoo.MirCallerValidation
import Jihoo.BoundedMirExamples
import Jihoo.ScopedLendGraphExamples

namespace Jihoo.MirCallerValidation.Examples
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open ScopedLend

/-- Original constructor graph for one literal Buffer1 allocation, inlined
read/free callee, and scalar result return. The MIR fixture retains native IDs. -/
def graph : Graph.Graph := Graph.Examples.graph ++ #[
  .integer 11, .alloc 0 16, .lam false 2 4, .app 15 4,
  .app 18 19, .lam false 1 20, .app 21 17]

def accepted : MirCallerValidation.Accepted graph 22 2 BoundedMir.Examples.single :=
  (admit graph 22 2 BoundedMir.Examples.single 100).get (by decide +kernel)

theorem scalar_result : accepted.source.value = 11 := by decide +kernel

theorem lifecycle_includes_extent : accepted.mir.outcome.events = [.alloc 0 16, .free 0] := by decide +kernel

theorem actual_cfg_execution :
    BoundedMir.Steps BoundedMir.Examples.single
      (.running (BoundedMir.initial BoundedMir.Examples.single)) [.alloc 0 16, .free 0]
      (.returned 11 accepted.mir.outcome.frame) := by
  simpa only [scalar_result, lifecycle_includes_extent] using mir_execution accepted

theorem all_mir_returns_match_source
    (run : BoundedMir.Steps BoundedMir.Examples.single
      (.running (BoundedMir.initial BoundedMir.Examples.single)) events (.returned value frame)) :
    ∃ sourceEvents state,
      ScalarCoreCallers.CoreRuns graph [] 22 [] [] HeapLeases.empty value sourceEvents state ∧
      ScalarCallerEvaluation.sourceLifecycle sourceEvents = events ∧ BoundedMir.heapEmpty frame = true :=
  all_returns accepted run

def wrongReturn : BoundedMir.Code :=
  { BoundedMir.Examples.single with blocks := (BoundedMir.Examples.single.blocks.set! 6
    ⟨#[⟨⟨0, false⟩, .use (.constant (.i64 77))⟩], .ret⟩) }

theorem wrong_return_still_memory_safe : (BoundedMir.admit wrongReturn 100).isSome = true := by decide +kernel

theorem mismatched_return_rejected : (admit graph 22 2 wrongReturn 100).isNone = true := by decide +kernel

def wrongExtent : BoundedMir.Code :=
  { BoundedMir.Examples.single with blocks := (BoundedMir.Examples.single.blocks.set! 0
    ⟨#[⟨⟨1, false⟩, .bin .mul (.constant (.u64 1)) (.constant (.u64 8))⟩,
       ⟨⟨2, false⟩, .bin .add (.copy ⟨1, false⟩) (.constant (.u64 0))⟩],
      .malloc (.copy ⟨2, false⟩) ⟨3, false⟩ 1⟩) }

theorem wrong_extent_still_memory_safe : (BoundedMir.admit wrongExtent 100).isSome = true := by decide +kernel

theorem mismatched_extent_rejected : (admit graph 22 2 wrongExtent 100).isNone = true := by decide +kernel

theorem insufficient_fuel_rejected : (admit graph 22 2 BoundedMir.Examples.single 1).isNone = true := by decide +kernel

theorem unchecked_source_rejected :
    (admit (graph.set! 16 (.integer (2^63))) 22 2 BoundedMir.Examples.single 100).isNone = true := by decide +kernel

end Jihoo.MirCallerValidation.Examples
