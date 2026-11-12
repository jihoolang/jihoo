import Jihoo.TreeDropCfg

namespace Jihoo.TreeDropCfg.Checks
open ReferenceCfg ReferenceCalls CommonDataReference

def nilHeap : ReferenceHeap.Heap := #[ReferenceHeap.nilObject]
theorem nil_exact : run 4 nilHeap 0 =
    some ⟨.unit, stateAt #[deadObject ReferenceHeap.nilObject] (nilLocals 0) 5 [], [.free 0]⟩ := by decide +kernel
theorem nil_short : run 3 nilHeap 0 = none := by decide +kernel

/-- Asymmetric tree, distinct children, an external live buffer and a dead cell. -/
def heap : ReferenceHeap.Heap := #[
  ReferenceHeap.node (.object 1 0) (.object 2 0), ReferenceHeap.nilObject,
  ReferenceHeap.node (.object 3 0) (.object 4 0), ReferenceHeap.nilObject, ReferenceHeap.nilObject,
  ⟨true, #[some (.scalar 77), some (.scalar 78)]⟩,
  ⟨false, #[some (.scalar 99)]⟩]
def finish : ReferenceHeap.Heap := #[
  deadObject (ReferenceHeap.node (.object 1 0) (.object 2 0)), deadObject ReferenceHeap.nilObject,
  deadObject (ReferenceHeap.node (.object 3 0) (.object 4 0)), deadObject ReferenceHeap.nilObject,
  deadObject ReferenceHeap.nilObject, ⟨true, #[some (.scalar 77), some (.scalar 78)]⟩,
  ⟨false, #[some (.scalar 99)]⟩]
def events : List HeapLifecycle.Event := [.free 0, .free 1, .free 2, .free 3, .free 4]
theorem asymmetric_exact : run 36 heap 0 =
    some ⟨.unit, stateAt finish (nodeLocals 0 1 2) 5 [], events⟩ := by decide +kernel
theorem asymmetric_short : run 35 heap 0 = none := by decide +kernel
theorem asymmetric_steps : ReferenceCalls.Steps program (.running (start heap 0)) events
    (.returned .unit (stateAt finish (nodeLocals 0 1 2) 5 [])) :=
  ReferenceCalls.execute_sound asymmetric_exact

def caller : Array (Option Value) := #[some (.i64 123), some (.boolean true), none,
  some (.referenceWord (.object 5 1)), some (.pointer 5 0), some .null, none, some (.u64 456)]
theorem caller_exact : walk 36 3 (start heap 0 [saved caller 3]) =
    some (stateAt finish (caller.set! 6 (some .unit)) 3 [], events) := by decide +kernel
theorem stack_limit_independent : walk 35 1 (start heap 0) = none := by decide +kernel
theorem sufficient_stack : walk 35 2 (start heap 0) =
    some (stateAt finish (nodeLocals 0 1 2) 5 [], events) := by decide +kernel

theorem bad_tag : run 50 #[⟨true, #[some (.scalar 2)]⟩] 0 = none := by decide +kernel
theorem dead_root : run 50 #[deadObject ReferenceHeap.nilObject] 0 = none := by decide +kernel
theorem absent_root : run 50 nilHeap 1 = none := by decide +kernel
theorem shared_child : run 50 #[ReferenceHeap.node (.object 1 0) (.object 1 0), ReferenceHeap.nilObject] 0 = none := by decide +kernel
theorem cycle : run 50 #[ReferenceHeap.node (.object 0 0) (.object 1 0), ReferenceHeap.nilObject] 0 = none := by decide +kernel
theorem null_child : run 50 #[ReferenceHeap.node .null (.object 1 0), ReferenceHeap.nilObject] 0 = none := by decide +kernel
theorem scalar_child : run 50 #[⟨true, #[some (.scalar 1), some (.scalar 0), some (.reference (.object 1 0))]⟩,
    ReferenceHeap.nilObject] 0 = none := by decide +kernel
theorem interior_root : ReferenceCalls.execute 50 program
    (stateAt heap #[some (.pointer 0 1), none, none, none, none, none, none] 0 []) = none := by decide +kernel
theorem null_root : ReferenceCalls.execute 50 program
    (stateAt heap #[some .null, none, none, none, none, none, none] 0 []) = none := by decide +kernel

end Jihoo.TreeDropCfg.Checks
