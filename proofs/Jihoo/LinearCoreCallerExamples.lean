import Jihoo.LinearCoreCallers
import Jihoo.ScopedLendGraphExamples

namespace Jihoo.LinearCoreCallers.Examples
open HeapLeases ScopedLend LinearHeapPrograms

/-- Two owners with equal payloads, consume the older lexical name first.
The scalar call-result binder remains in the lexical context but is not an owner. -/
def graph : Graph.Graph := Graph.Examples.graph ++ #[
  .integer 42,       --16
  .alloc 0 16,       --17
  .integer 17,       --18 terminal
  .var 1,           --19 x before first call; y after result binder
  .app 15 19,       --20 consume variable
  .lam false 2 18,   --21 last result binder
  .app 21 20,       --22 consume y
  .lam false 2 22,   --23 first result binder
  .app 23 20,       --24 consume x
  .lam false 1 24,   --25 y binder
  .app 25 17,       --26 allocate y
  .lam false 1 26,   --27 x binder
  .app 27 17]       --28 allocate x

def accepted : Accepted graph 28 2 := (admit graph 28 2).get (by decide)

theorem concrete_program : accepted.program =
    .allocate 42 (.allocate 42 (.call 1 graph 15 3 (.call 0 graph 15 3 .done))) := rfl

theorem total : ∃ es t, CoreRuns graph [] 28 [] empty es t := accepted_total accepted

theorem all_runs_empty (run : CoreRuns graph [] 28 [] empty es t) :
    ∀ x, t.live x = false := (accepted_all_runs accepted run).2.2.2.2

theorem fresh_shifts : fresh [none, some 0, none, some 1] =
    [some 0, none, some 1, none, some 2] := rfl

theorem consume_retains_tombstone : consumed 1 [some 0, some 1] = [some 0, none] := rfl

theorem consume_compacts_not_names : consumed 0 [some 0, none, some 1] = [none, none, some 0] := rfl

theorem allocation_never_revives_consumed_name :
    fresh (none :: consumed 1 [some 0, some 1]) = [some 0, none, some 1, none] := rfl

theorem older_name_first : ownerSlot graph [some 0, some 1] 19 = some 1 := rfl

theorem newer_name_after_result : ownerSlot graph [none, some 0, none] 19 = some 0 := rfl

theorem result_not_owner : ownerSlot #[.var 0] [none, some 0, none] 0 = none := rfl

theorem consumed_not_owner : ownerSlot #[.var 2] [none, some 0, none] 0 = none := rfl

theorem reuse_rejected : (admit (graph.set! 19 (.var 0)) 28 2).isSome = false := by decide

theorem leaked_owner_rejected : (admit (graph.set! 24 (.integer 17)) 28 2).isSome = false := by decide

theorem erased_owner_rejected : (admit (graph.set! 25 (.lam true 1 24)) 28 2).isSome = false := by decide

theorem nonliteral_initializer_rejected :
    (admit (graph.set! 17 (.alloc 0 4)) 28 2).isSome = false := by decide

theorem wrong_length_rejected :
    (admit (graph.set! 17 (.alloc 6 16)) 28 2).isSome = false := by decide

theorem callee_captures_outer_owner_rejected :
    (admit (graph.set! 4 (.var 2)) 28 2).isSome = false := by decide

theorem invalid_type_rejected : (admit graph 28 1).isSome = false := by decide

theorem zero_budget_rejected : project 32 0 graph [] 28 = none := rfl

theorem small_depth_rejected : project 2 512 graph [] 28 = none := by decide

end Jihoo.LinearCoreCallers.Examples
