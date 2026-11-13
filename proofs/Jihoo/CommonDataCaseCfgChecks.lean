import Jihoo.CommonDataCaseCfg

namespace Jihoo.CommonDataCaseCfg.Checks
open ReferenceCfg ReferenceCalls CommonDataReference

def stop : Block := ⟨#[], .ret⟩
def heap : ReferenceHeap.Heap := #[
  ReferenceHeap.node (.object 1 0) (.object 2 0), ReferenceHeap.nilObject,
  ReferenceHeap.nilObject, ⟨true, #[some (.scalar 77), some (.scalar 78)]⟩,
  ⟨false, #[some (.scalar 99)]⟩]
/-- Poisoned child locals cannot supply the expected child result. -/
def poisoned : Array (Option Value) := #[some (.pointer 0 0), some .null,
  some .unit, some (.boolean true), some (.i64 999), some .null, none,
  some (.referenceWord (.object 3 1)), some (.u64 456)]
def emptyChildren : Array (Option Value) :=
  #[some (.pointer 0 0), none, none, none, none, none, none]
def caller : Continuation := ⟨99, 88, #[some (.i64 123)], ⟨42, false⟩⟩

theorem node_poisoned : walk stop stop 9 1 (stateAt heap poisoned 0 [caller]) =
    some (stateAt heap (nodeLocals poisoned 0 1 2) 4 [caller], []) := by decide +kernel

theorem node_empty : walk stop stop 9 0 (stateAt heap emptyChildren 0 []) =
    some (stateAt heap (nodeLocals emptyChildren 0 1 2) 4 [], []) := by decide +kernel

theorem node_exact_entry : ∀ n ∈ List.range 9,
    ((walk stop stop n 1 (stateAt heap poisoned 0 [caller])).map
      (fun result => result.1.frame.block)) ≠ some 4 := by decide +kernel

theorem node_short_fuel : runPrefix stop stop 8 9 1 (stateAt heap poisoned 0 [caller]) =
    none := by decide +kernel

theorem stack_bound_checked : walk stop stop 9 0 (stateAt heap poisoned 0 [caller]) =
    none := by decide +kernel

def nilHeap : ReferenceHeap.Heap := #[ReferenceHeap.nilObject,
  ⟨true, #[some (.scalar 77)]⟩, ⟨false, #[some (.scalar 99)]⟩]
theorem nil_exact : walk stop stop 3 1 (stateAt nilHeap poisoned 0 [caller]) =
    some (stateAt (retired nilHeap 0 ReferenceHeap.nilObject) (nilLocals poisoned) 3 [caller],
      [.free 0]) := by decide +kernel

theorem nil_exact_entry : ∀ n ∈ List.range 3,
    ((walk stop stop n 1 (stateAt nilHeap poisoned 0 [caller])).map
      (fun result => result.1.frame.block)) ≠ some 3 := by decide +kernel

theorem nil_short_fuel : runPrefix stop stop 2 3 1 (stateAt nilHeap poisoned 0 [caller]) =
    none := by decide +kernel

theorem dead_root : walk stop stop 3 0
    (stateAt #[⟨false, #[some (.scalar 0)]⟩] emptyChildren 0 []) = none := by decide +kernel

theorem absent_root : walk stop stop 3 0 (stateAt #[] emptyChildren 0 []) =
    none := by decide +kernel

theorem bad_tag : walk stop stop 3 0
    (stateAt #[⟨true, #[some (.scalar 2)]⟩] emptyChildren 0 []) = none := by decide +kernel

theorem scalar_child : walk stop stop 9 0
    (stateAt #[⟨true, #[some (.scalar 1), some (.scalar 0),
      some (.reference (.object 2 0))]⟩] emptyChildren 0 []) = none := by decide +kernel

theorem source_nil : sourceEnter
    (s : CommonData.State) [.data none] 0 2 = some ([.data none], none) := rfl

theorem source_bad_operand : sourceEnter
    (s : CommonData.State) [.scalar 0] 0 2 = none := rfl

#print axioms node_entry
#print axioms nil_entry
#print axioms pending_shell
#print axioms BoundedPrefix.steps
#print axioms BoundedPrefix.execute
#print axioms node_poisoned
#print axioms node_empty
#print axioms nil_exact
end Jihoo.CommonDataCaseCfg.Checks
