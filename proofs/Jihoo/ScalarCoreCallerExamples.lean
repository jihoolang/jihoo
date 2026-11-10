import Jihoo.ScalarCoreCallers
import Jihoo.ScopedLendGraphExamples

namespace Jihoo.ScalarCoreCallers.Examples
open HeapLeases ScopedLend LinearHeapPrograms

/-- First callee returns 99 independently of its payload 11; y and z return
22 and 33. An owner allocation occurs between the first and second calls. -/
def graph : Graph.Graph := Graph.Examples.graph ++ #[
  .integer 99,       --16
  .lam false 5 16,   --17 constant reader
  .lend 4 17 13,     --18
  .lam false 1 18,   --19 constant-result callee
  .integer 11,       --20
  .integer 22,       --21
  .integer 33,       --22
  .alloc 0 20,       --23 x
  .alloc 0 21,       --24 y
  .alloc 0 22,       --25 z
  .var 3,           --26 return oldest scalar result
  .lam false 2 26,   --27 third result binder
  .app 15 10,       --28 consume z (Var1)
  .app 27 28,       --29
  .lam false 2 29,   --30 second result binder
  .var 2,           --31 y under z and first result
  .app 15 31,       --32 consume y
  .app 30 32,       --33
  .lam false 1 33,   --34 z binder
  .app 34 25,       --35 allocate z
  .lam false 2 35,   --36 first result binder
  .app 19 10,       --37 consume x (Var1)
  .app 36 37,       --38
  .lam false 1 38,   --39 y binder
  .app 39 24,       --40 allocate y
  .lam false 1 40,   --41 x binder
  .app 41 23]       --42 allocate x

def accepted : Accepted graph 42 2 := (admit graph 42 2).get (by decide)

def target : Target.Program := .allocate 11 (.allocate 22
  (.call 1 (.scalar 99) .free (.allocate 33
    (.call 1 .load .free (.call 0 .load .free (.finish (.scalar 2)))))))

theorem original_graph_compiles : lower accepted.program = some target := rfl

def h0 := LeaseErasure.erase empty
def h1 := LeaseErasure.allocate h0 11
def h2 := LeaseErasure.allocate h1 22
def h3 := LeaseErasure.finish h2 0 99 .free
def h4 := LeaseErasure.allocate h3 33
def h5 := LeaseErasure.finish h4 1 22 .free
def h6 := LeaseErasure.finish h5 2 33 .free

def events : List LeaseErasure.Event :=
  [.alloc 0 11, .alloc 1 22, .free 0, .alloc 2 33, .read 1 22, .free 1, .read 2 33, .free 2]

theorem concrete_run : Target.Runs target [] [] h0 99 events h6 :=
  .allocate (.allocate (.call (.there .here) (.run rfl .scalar)
    (.allocate (.call (.there .here) (.run rfl (.load rfl))
      (.call .here (.run rfl (.load rfl)) (.finish rfl))))))

theorem old_payload_is_not_returned_result : h6.payload 0 = 11 := rfl

theorem every_target_returns_oldest (run : Target.Runs target [] [] h0 v es h) : v = 99 :=
  (run.deterministic concrete_run).1

theorem original_result_effects_heap :
    ∃ es s, CoreRuns graph [] 42 [] [] empty 99 es s ∧ LeaseErasure.erase s = h6 ∧
      LeaseErasure.sourceTrace es = LeaseErasure.targetTrace events :=
  accepted_target_reflect accepted original_graph_compiles concrete_run

theorem all_resources_freed : ∀ x, h6.live x = false :=
  (accepted_target_safe accepted original_graph_compiles concrete_run).2.1

theorem scalar_binding_preserved_by_allocation :
    scalarBindings (fresh [.scalar 0, .owner 0, .dead]) [99] = [none, some 99, none, none] := rfl

theorem older_scalars_shift_only_on_call :
    scalarBindings (consumed 0 [.scalar 0, .owner 0, .scalar 1]) [33, 22, 99] =
      [some 33, some 22, none, some 99] := rfl

theorem distinct_roles : consumed 1 [.owner 0, .scalar 0, .owner 1, .dead] =
    [.scalar 0, .owner 0, .scalar 1, .dead, .dead] := rfl

def latest : Accepted (graph.set! 26 (.var 0)) 42 2 :=
  (admit (graph.set! 26 (.var 0)) 42 2).get (by decide)

def middle : Accepted (graph.set! 26 (.var 1)) 42 2 :=
  (admit (graph.set! 26 (.var 1)) 42 2).get (by decide)

theorem latest_returns_newest_slot : latest.program =
    .allocate 11 (.allocate 22 (.call 1 (graph.set! 26 (.var 0)) 19 3
      (.allocate 33 (.call 1 (graph.set! 26 (.var 0)) 15 3
        (.call 0 (graph.set! 26 (.var 0)) 15 3 (.finish (.scalar 0))))))) := rfl

theorem middle_returns_previous_slot : middle.program =
    .allocate 11 (.allocate 22 (.call 1 (graph.set! 26 (.var 1)) 19 3
      (.allocate 33 (.call 1 (graph.set! 26 (.var 1)) 15 3
        (.call 0 (graph.set! 26 (.var 1)) 15 3 (.finish (.scalar 1))))))) := rfl

theorem dead_owner_cannot_return : (admit (graph.set! 26 (.var 2)) 42 2).isSome = false := by decide

theorem scalar_cannot_be_consumed : (admit (graph.set! 31 (.var 1)) 42 2).isSome = false := by decide

theorem old_consumed_owner_cannot_return : (admit (graph.set! 26 (.var 5)) 42 2).isSome = false := by decide

theorem missing_scalar_cannot_return : (admit (graph.set! 26 (.var 6)) 42 2).isSome = false := by decide

theorem live_owner_cannot_return : resultAt #[.var 0] [.owner 0] 0 = none := rfl

theorem leaked_owner_rejected : (admit (graph.set! 29 (.integer 7)) 42 2).isSome = false := by decide

theorem erased_result_binder_rejected : (admit (graph.set! 27 (.lam true 2 26)) 42 2).isSome = false := by decide

theorem wrong_root_type_rejected : (admit graph 42 1).isSome = false := by decide

end Jihoo.ScalarCoreCallers.Examples
