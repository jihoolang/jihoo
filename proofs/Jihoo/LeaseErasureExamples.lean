import Jihoo.LeaseErasure
import Jihoo.LinearCoreCallerExamples

namespace Jihoo.LeaseErasure.Examples
open HeapLeases ScopedLend LinearHeapPrograms

abbrev graph := LinearCoreCallers.Examples.graph
abbrev accepted := LinearCoreCallers.Examples.accepted

def program : LeaseErasure.Program :=
  .allocate 42 (.allocate 42 (.call 1 .load .free (.call 0 .load .free .done)))

theorem original_graph_compiles : lower accepted.program = some program := rfl

def h0 := erase empty
def h1 := allocate h0 42
def h2 := allocate h1 42
def h3 := finish h2 0 42 .free
def h4 := finish h3 1 42 .free

def trace : List LeaseErasure.Event :=
  [.alloc 0 42, .alloc 1 42, .read 0 42, .free 0, .read 1 42, .free 1]

theorem concrete_target_run : Runs program [] h0 trace h4 :=
  .allocate (.allocate (.call (.there .here)
    (.run rfl (.load rfl)) (.call .here (.run rfl (.load rfl)) .done)))

theorem original_source_correspondence :
    ∃ es s, LinearCoreCallers.CoreRuns graph [] 28 [] empty es s ∧
      erase s = h4 ∧ sourceTrace es = targetTrace trace :=
  accepted_target_reflect accepted original_graph_compiles concrete_target_run

theorem every_target_run_same (run : Runs program [] h0 es h) : es = trace ∧ h = h4 := by
  obtain ⟨rfl, rfl⟩ := concrete_target_run.deterministic run
  exact ⟨rfl, rfl⟩

theorem all_target_runs_empty (run : Runs program [] h0 es h) : ∀ x, h.live x = false :=
  (accepted_target_safe accepted original_graph_compiles run).2

theorem target_effect_order : targetTrace trace =
    [.alloc 0 42, .alloc 1 42, .read 42, .free 0, .read 42, .free 1] := rfl

theorem target_object_order : trace[2]? = some (.read 0 42) ∧ trace[4]? = some (.read 1 42) := ⟨rfl,rfl⟩

def sourceState := ScopedLend.Examples.initial

theorem changed_result_source : ScopedLend.Executes sourceState 1
    (.seq (.read 0) (.scalar 99)) .storeResult 99
    [.beginLease 1 1, .read 1 42, .close 1, .write 1 99, .free 1]
    (finalState sourceState 1 99 .storeResult) :=
  .lend (.seq (.read (k := 0) (l := 1) (x := 1) rfl rfl) .scalar)

theorem changed_result_target : Calls (erase sourceState) 1
    (.seq .load (.scalar 99)) .storeResult 99
    [.read 1 42, .write 1 99, .free 1] (finish (erase sourceState) 1 99 .storeResult) :=
  .run rfl (.seq (.load rfl) .scalar)

theorem changed_result_observations :
    sourceTrace [.beginLease 1 1, .read 1 42, .close 1, .write 1 99, .free 1] =
    targetTrace [.read 1 42, .write 1 99, .free 1] := rfl

theorem changed_result_payload : (finish (erase sourceState) 1 99 .storeResult).payload 1 = 99 := rfl

theorem scalar_value_preserved : ∃ events, Calls (erase sourceState) 1
    (lowerReader (.seq (.read 0) (.scalar 99))) .storeResult 99 events
    (erase (finalState sourceState 1 99 .storeResult)) := call_forward changed_result_source rfl

theorem erased_lease_counters : erase {sourceState with nextLease := 1000, lease := fun _ => none} = erase sourceState := rfl

theorem direct_read_without_token : Reads (erase sourceState) 1 .load 42 [.read 1 42] := .load rfl

theorem read_dead_rejected : ¬ Reads h4 0 .load v es := by
  intro h
  cases h with | load live => contradiction

theorem free_dead_rejected : ¬ Step h4 (.free 0) h := by
  intro step
  cases step with | free live => contradiction

/-- Token erasure does not make arbitrary target writes reflect into source
lease-safe writes. Only compiled checked programs receive the all-run theorem. -/
theorem target_can_write_borrowed_object :
    Step (erase sourceState) (.write 0 99) {erase sourceState with payload := put sourceState.payload 0 99} :=
  .write rfl

theorem source_cannot_write_borrowed_object : ¬ HeapLeases.Step sourceState (.write 0 99) s := by
  intro step
  cases step with
  | write live available => exact available 0 rfl

theorem unsupported_callee_rejected :
    (lower (.call 0 #[] 0 0 .done)).isNone = true := by decide

end Jihoo.LeaseErasure.Examples
