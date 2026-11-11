import Jihoo.BoundedMirExecutionAdequacy
import Jihoo.BoundedMirExamples

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Jihoo.BoundedMir.ExecutionAdequacyChecks

open Examples

/-- A timeout is not evidence of stuckness: runFor retains the partial state. -/
theorem short_execute_but_successful_prefix :
    execute 21 single (initial single) = none ∧
      (runFor 21 single (.running (initial single))).isSome = true := by
  decide +kernel

def atFuel (fuel : Nat) : Next :=
  (runFor fuel single (.running (initial single))).getD ⟨.running (initial single), []⟩

theorem allocation_prefix :
    (atFuel 3).events = [.alloc 0 16] ∧
      (match (atFuel 3).machine with
      | .running f => some (f.block, f.heap.size)
      | .returned _ _ => none) = some (1, 1) := by decide +kernel

/-- The loop takes both the continuing and terminating switch outcomes. -/
theorem both_loop_branch_outcomes :
    (match (atFuel 10).machine with
    | .running f => some f.block
    | .returned _ _ => none) = some 4 ∧
    (match (atFuel 16).machine with
    | .running f => some f.block
    | .returned _ _ => none) = some 5 := by decide +kernel

theorem read_prefix :
    (atFuel 19).events = [.alloc 0 16] ∧
      (match (atFuel 19).machine with
      | .running f => f.locals[11]?
      | .returned _ _ => none) = some (some (.i64 11)) := by decide +kernel

theorem returned_exact_trace :
    (atFuel 22).machine = .returned 11 accepted.outcome.frame ∧
      (atFuel 22).events = [.alloc 0 16, .free 0] := by decide +kernel

theorem arbitrary_fuel_never_stuck (fuel : Nat) :
    ∃ out, runFor fuel single (.running (initial single)) = some out :=
  concrete_steps.runFor_total fuel

theorem arbitrary_prefix_has_exact_suffix
    (pre : Steps single (.running (initial single)) events middle) :
    ∃ suffix, accepted.outcome.events = events ++ suffix ∧
      Steps single middle suffix (.returned 11 accepted.outcome.frame) :=
  concrete_steps.prefix_completion pre

theorem eventual_execute : ∃ bound, ∀ fuel, bound ≤ fuel →
    execute fuel single (initial single) =
      some ⟨11, accepted.outcome.frame, accepted.outcome.events⟩ :=
  concrete_steps.execute_complete

theorem eventual_runFor : ∃ bound, ∀ fuel, bound ≤ fuel →
    runFor fuel single (.running (initial single)) =
      some ⟨.returned 11 accepted.outcome.frame, accepted.outcome.events⟩ :=
  concrete_steps.runFor_complete

/-- Malformed MIR with an uninitialized return is genuinely stuck. -/
theorem malformed_tick_stuck :
    rawTick uninitializedReturn (initial uninitializedReturn) = none := by decide +kernel

theorem malformed_no_step :
    ¬ Step uninitializedReturn (.running (initial uninitializedReturn)) events target := by
  intro step
  have h := rawTick_complete step
  rw [malformed_tick_stuck] at h
  cases h

theorem malformed_no_termination :
    ¬ Steps uninitializedReturn (.running (initial uninitializedReturn)) events
      (.returned value final) := by
  intro complete
  obtain ⟨_, _, step⟩ := complete.running_progress Steps.nil
  exact malformed_no_step step

theorem malformed_positive_fuel_fails :
    runFor 1 uninitializedReturn (.running (initial uninitializedReturn)) = none := by
  decide +kernel

end Jihoo.BoundedMir.ExecutionAdequacyChecks
