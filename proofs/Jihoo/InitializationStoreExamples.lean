import Jihoo.InitializationStore
import Jihoo.InitializationExamples

namespace Jihoo.Initialization.Store.Examples
open Jihoo.Initialization Jihoo.LoweringEnvironment

private def empty : Memory Nat := fun _ => none

 theorem absent_read_fault :
    execute (fun _ _ _ => some [7]) [⟨[1], [1]⟩] empty = .uninitialized := rfl

 theorem initialized_read_order :
    readMany (enter none [11, 22]) [2, 1, 2] = some [22, 11, 22] := rfl

 theorem trap_remains_possible :
    execute (fun _ _ _ => none) [⟨[1], [2]⟩] (enter none [7]) = .trap := rfl

 theorem wrong_result_arity_remains_possible :
    execute (fun _ _ _ => some []) [⟨[1], [2]⟩] (enter none [7]) = .badResult := rfl

 theorem duplicate_write_keeps_last :
    (match execute (fun _ _ _ => some [7, 8]) [⟨[], [1, 1]⟩] empty with
      | .normal memory => memory 1 | _ => none) = some 8 := rfl

 theorem operations_distinguish_positions :
    (match execute (fun i _ _ => some [i + 7]) [⟨[], [1]⟩, ⟨[], [1]⟩] empty with
      | .normal memory => memory 1 | _ => none) = some 8 := rfl

 theorem captured_argument_values :
    readMany (enter none (5 :: pack [.ghost, .value 11, .hypothesis 22 [33]]))
      [1, 2, 3, 4] = some [5, 11, 22, 33] := rfl

 theorem concrete_cycle_no_fault (values : Nat → Nat)
    (reach : ValueReach Initialization.Examples.loop
      (seed [] values) pc memory)
    (member : (pc, b) ∈ Initialization.Examples.loop) :
    execute operation b.actions memory ≠ .uninitialized :=
  accepted_no_uninitialized Initialization.Examples.cycle_accepted seed_covers reach member

end Jihoo.Initialization.Store.Examples
