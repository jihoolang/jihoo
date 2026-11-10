import Jihoo.ScalarCallerEvaluation
import Jihoo.ScalarCoreCallerExamples

namespace Jihoo.ScalarCallerEvaluation.Examples
open HeapLeases ScalarCoreCallers
abbrev graph := ScalarCoreCallers.Examples.graph

def accepted : ScalarCallerEvaluation.Accepted graph 42 2 :=
  (admit graph 42 2).get (by decide)

theorem executable_result : accepted.value = 99 := rfl

theorem executable_lifecycle : lifecycle accepted.events =
    [.alloc 0 16, .alloc 1 16, .free 0, .alloc 2 16, .free 1, .free 2] := rfl

theorem executable_original : ∃ es s, CoreRuns graph [] 42 [] [] empty 99 es s ∧
    LeaseErasure.erase s = accepted.heap ∧ LeaseErasure.sourceTrace es = LeaseErasure.targetTrace accepted.events :=
  accepted_original accepted

theorem final_heap_empty : ∀ x, accepted.heap.live x = false := accepted_heap_empty accepted

theorem missing_owner_rejected : select [10, 20] 2 = none := rfl

theorem middle_selection : select [10, 20, 30] 1 = some (20, [10, 30]) := rfl

theorem dead_load_rejected : evalReader (LeaseErasure.erase empty) 0 .load = none := rfl

theorem dead_scalar_call_rejected : evalCall (LeaseErasure.erase empty) 0 (.scalar 99) .free = none := rfl

theorem leaked_capability_rejected :
    evalProgram (.finish (.literal 7)) [0] [] (LeaseErasure.erase empty) = none := rfl

theorem missing_scalar_rejected :
    evalProgram (.finish (.scalar 0)) [] [] (LeaseErasure.erase empty) = none := rfl

end Jihoo.ScalarCallerEvaluation.Examples
