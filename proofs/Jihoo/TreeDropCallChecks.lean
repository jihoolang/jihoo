import Jihoo.TreeDropCall
import Jihoo.TreeDropCfgChecks

namespace Jihoo.TreeDropCall.Checks
open ReferenceCfg ReferenceCalls

def surrounding : ReferenceCalls.Function := ⟨⟨⟨#[], #[⟨#[], .ret⟩]⟩, #[some .retUnit]⟩, #[]⟩
def caller : ReferenceCalls.Function :=
  ⟨compileDrop ⟨⟨#[.ptr, .i64, .unit], #[⟨#[], .ret⟩]⟩, #[some .retUnit]⟩
    2 (.copy ⟨0, false⟩) 2 0, #[]⟩
def program : Program := #[surrounding, caller, body 2, surrounding]
def entry : State := ⟨1, ⟨1, 0,
  #[some (.pointer 0 0), some (.i64 77), none], TreeDropCfg.Checks.heap⟩, []⟩
def finished : State := resume entry 2 0 TreeDropCfg.Checks.finish

theorem installed : program[2]? = some (body 2) := rfl
/-- Caller 1, recursive Drop 2, unrelated functions 0 and 3. -/
theorem asymmetric_exact : ReferenceCalls.execute 38 program entry =
    some ⟨.unit, finished, TreeDropCfg.Checks.events⟩ := by decide +kernel
theorem short : ReferenceCalls.execute 37 program entry = none := by decide +kernel
theorem body_entry : walk program 37 3 entry =
    some (finished, TreeDropCfg.Checks.events) := by decide +kernel
theorem live_local : finished.frame.locals[1]? = some (some (.i64 77)) := rfl
theorem shared_buffer : finished.frame.heap[5]? = TreeDropCfg.Checks.heap[5]? := rfl
theorem unit_destination : finished.frame.locals[2]? = some (some .unit) := rfl
/-- Merely inserting the old function at ID 2 fails: its recursion still targets 0. -/
theorem unrelocated_rejected : ReferenceCalls.execute 38
    #[surrounding, caller, TreeDropCfg.body, surrounding] entry = none := by decide +kernel
theorem insufficient_stack : walk program 37 2 entry = none := by decide +kernel
end Jihoo.TreeDropCall.Checks
