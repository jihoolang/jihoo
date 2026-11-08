import Jihoo.QuantityControl

namespace Jihoo.Quantity.Examples
open Control

-- This resource is used once on either branch, never twice in sequence.
def balanced : Control := .branch (.use 0) (.once (.use 0))
example : balanced.demand 0 = some 1 := by decide
example : (Control.seq (.use 0) (.use 0)).demand 0 = some 2 := by decide
example : (Control.branch (.use 0) .pure).demand 0 = none := by decide
-- Equal total event counts cannot conceal different resources on each branch.
example : (Control.branch (.use 0) (.use 1)).demand 0 = none := by decide
example : (Control.branch (.use 0) (.use 1)).demand 1 = none := by decide
example : (Control.closure (.use 0)).demand 0 = none := by decide
example : (Control.once (.use 0)).demand 0 = some 1 := by decide
example : (Control.repeat (.use 0)).demand 0 = none := by decide
example : (Control.erased (.seq (.use 0) (.use 0))).demand 0 = some 0 := by decide
-- A local owner is consumed in each iteration; no outer owner is captured.
def localLoop : Control := .repeat (.bind (.use 0))
example : localLoop.demand 0 = some 0 := by decide
example : (Control.bind .pure).demand 0 = none := by decide
example : (Control.bind (.seq (.use 0) (.use 0))).demand 0 = none := by decide
-- Shift the outer owner through two local scopes and use each independently.
def nested : Control := .bind (.seq (.use 0) (.bind (.seq (.use 0) (.use 2))))
example : nested.demand 0 = some 1 := by decide
example : nested.demand 1 = some 0 := by decide

theorem nested_run : Finishes nested [0] := by
  exact .bind (.seq .use (.bind (.seq .use .use)))

theorem nested_once : ∀ xs, Finishes nested xs → xs.count 0 = 1 :=
  fun _ run => run.count_eq (by decide)

theorem trap_before : Prefix (.seq .trap (.use 0)) [] := .seqLeft .start
theorem trap_after : Prefix (.seq (.use 0) .trap) [0] := .seqRight .use .start
example : (Control.seq .trap (.use 0)).demand 0 = some 1 := by decide
example : (Control.seq (.use 0) .trap).demand 0 = some 1 := by decide

-- Traps deliberately make an exactly-once claim about all prefixes false.
theorem trap_can_abandon : ∃ c xs, c.demand 0 = some 1 ∧ Prefix c xs ∧ xs.count 0 = 0 :=
  ⟨_, [], by decide, trap_before, rfl⟩

theorem trap_no_completion : ¬ Finishes (.seq .trap (.use 0)) xs := by
  intro h
  cases h with
  | seq impossible _ => cases impossible

-- Every finite repetition prefix can finish a local scope and begin another.
theorem local_iteration : Finishes (.bind (.use 0)) [] := .bind .use

theorem local_loop_no_outer_use (run : Prefix localLoop xs) : 0 ∉ xs :=
  erased_unreachable (by decide) run

-- The semantic branch relation itself allows different demands. Removing the
-- agreement check would invalidate the exact-use theorem, not just acceptance.
theorem unbalanced_runs : Finishes (.branch (.use 0) .pure) [0] ∧
    Finishes (.branch (.use 0) .pure) [] := ⟨.left .use, .right .pure⟩

theorem repeated_capture_runs : Finishes (.repeat (.use 0)) [0, 0] :=
  .repeatNext .use (.repeatNext .use .repeatZero)

end Jihoo.Quantity.Examples
