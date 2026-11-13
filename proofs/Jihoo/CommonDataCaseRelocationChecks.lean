import Jihoo.CommonDataCaseRelocation
import Jihoo.CommonDataCaseCfgChecks

namespace Jihoo.CommonDataCaseRelocation.Checks
open ReferenceCfg ReferenceCalls CommonDataCaseCfg
open CommonDataCaseCfg.Checks

/-- Counterexample: merely appending one block makes the old default valid. -/
def unsafeAppend : Program :=
  #[{body stop stop with code :=
    { (body stop stop).code with base :=
      { (body stop stop).code.base with blocks :=
        (body stop stop).code.base.blocks ++ #[stop] } } }]

def badTag : Array (Option Value) := poisoned.set! 1 (some (.i64 2))
def dispatch : State := ⟨0, ⟨0,1,badTag,heap⟩, []⟩

theorem old_default_fails :
    ReferenceCalls.tick (program stop stop) dispatch = none := by decide +kernel

theorem append_changes_failure :
    ReferenceCalls.tick unsafeAppend dispatch =
      some ⟨.running (stateAt heap badTag 5 []), []⟩ := by decide +kernel

theorem safe_default :
    CommonDataCaseRelocation.walk (linked #[stop] #[stop,stop] stop stop 7) 2 0
      ⟨0, ⟨1,1,badTag,heap⟩, []⟩ = none := by decide +kernel

/-- Two distinct children expose an accidental swap. -/
theorem reversed_target_order_wrong :
    ([4,5] : List Nat).map (fun k => (nodeLocals poisoned 0 1 2)[k]?) ≠
      [some (some (.pointer 2 0)), some (some (.pointer 1 0))] := by decide +kernel

theorem node_collision : (nodeLocals poisoned 0 1 2)[4]? ≠ poisoned[4]? := by decide +kernel
theorem nil_collision : (nilLocals poisoned)[6]? ≠ poisoned[6]? := by decide +kernel

def copied : Array (Option Value) := poisoned.set! 0 (some .null) |>.push (some (.pointer 0 0))

theorem copy_collision : (copied.set! 0 (some (.pointer 0 0)))[0]? ≠ copied[0]? := by decide +kernel

theorem relocated_copied_node :
    runPrefix (linked #[stop,stop] #[stop] stop stop 9) 11 11 1
      (stateAt heap copied 8 [caller]) =
    some (stateAt heap (nodeLocals (copied.set! 0 (some (.pointer 0 0))) 0 1 2)
      6 [caller], []) := by decide +kernel

theorem copied_node_short :
    runPrefix (linked #[stop] #[stop] stop stop 9) 10 11 1
      (stateAt heap copied 7 [caller]) = none := by decide +kernel

theorem copied_nil_short :
    runPrefix (linked #[stop] #[stop] stop stop 9) 4 5 1
      (stateAt nilHeap copied 7 [caller]) = none := by decide +kernel

theorem copied_stack_short :
    runPrefix (linked #[stop] #[stop] stop stop 9) 11 11 0
      (stateAt heap copied 7 [caller]) = none := by decide +kernel

#print axioms node_entry
#print axioms nil_entry
#print axioms runPrefix_sound
#print axioms nil_prefix
#print axioms node_prefix
#print axioms copy_prefix
#print axioms nil_copied_entry
#print axioms node_copied_entry
#print axioms failure_tick
#print axioms invalid_dispatch
#print axioms relocated_lookup
#print axioms relocate_edges
#print axioms copied_node_live
#print axioms copied_nil_live
#print axioms binder_order
#print axioms BoundedPrefix.steps
#print axioms BoundedPrefix.execute
#print axioms append_changes_failure
end Jihoo.CommonDataCaseRelocation.Checks
