import Jihoo.BoundedMirRun

/-! Adequacy for terminating deterministic MIR executions. All termination
premises are relational executions, not successful interpreter runs. -/
namespace Jihoo.BoundedMir

/-- A finite prefix of a terminating execution has the same remaining result
and exactly the remaining event suffix. -/
theorem Steps.prefix_completion
    (complete : Steps c start completeEvents (.returned value final))
    (pre : Steps c start prefixEvents middle) :
    ∃ suffix, completeEvents = prefixEvents ++ suffix ∧
      Steps c middle suffix (.returned value final) := by
  induction pre generalizing completeEvents with
  | nil => exact ⟨completeEvents, rfl, complete⟩
  | cons head tail ih =>
    cases complete with
    | nil => cases head
    | cons first rest =>
      obtain ⟨rfl, rfl⟩ := head.deterministic first
      obtain ⟨suffix, eq, run⟩ := ih rest
      exact ⟨suffix, by simp [eq, List.append_assoc], run⟩

/-- Every reachable running machine on a terminating execution can step. -/
theorem Steps.running_progress
    (complete : Steps c start completeEvents (.returned value final))
    (pre : Steps c start prefixEvents (.running f)) :
    ∃ events next, Step c (.running f) events next := by
  obtain ⟨_, _, rest⟩ := complete.prefix_completion pre
  cases rest with
  | cons head _ => exact ⟨_, _, head⟩

/-- The proof-free evaluator implements every relational transition. -/
theorem rawTick_complete (step : Step c (.running f) events target) :
    rawTick c f = some ⟨target, events⟩ := by
  cases step <;> simp_all [rawTick]

theorem tick_complete (step : Step c (.running f) events target) :
    tick c f = some ⟨target, events⟩ := by
  rw [tick_eq_rawTick]
  exact rawTick_complete step

theorem Steps.running_rawTick
    (complete : Steps c start completeEvents (.returned value final))
    (pre : Steps c start prefixEvents (.running f)) :
    ∃ next, rawTick c f = some next := by
  obtain ⟨events, target, step⟩ := complete.running_progress pre
  exact ⟨⟨target, events⟩, rawTick_complete step⟩

/-- Even insufficient fuel yields a successful partial prefix, never a stuck
interpreter, when the initial machine has a terminating relational execution. -/
theorem Steps.runFor_total
    (complete : Steps c start events (.returned value final)) (fuel : Nat) :
    ∃ out, runFor fuel c start = some out := by
  induction fuel generalizing start events with
  | zero => exact ⟨⟨start, []⟩, rfl⟩
  | succ fuel ih =>
    cases start with
    | returned v f => exact ⟨⟨.returned v f, []⟩, rfl⟩
    | running f =>
      cases complete with
      | @cons _ first _ _ _ head tail =>
        obtain ⟨out, hout⟩ := ih tail
        exact ⟨⟨out.machine, first ++ out.events⟩, by
          simp [runFor, rawTick_complete head, hout]⟩

/-- Sufficient fuel recovers exactly the relational return and event trace. -/
theorem Steps.runFor_complete
    (complete : Steps c start events (.returned value final)) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      runFor fuel c start = some ⟨.returned value final, events⟩ := by
  generalize he : Machine.returned value final = finish at complete
  induction complete with
  | nil =>
    cases he
    refine ⟨0, ?_⟩
    intro fuel _
    cases fuel <;> rfl
  | @cons start first middle rest finish head tail ih =>
    obtain ⟨bound, hb⟩ := ih he
    refine ⟨bound + 1, ?_⟩
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      have enough : bound ≤ fuel := by omega
      cases start with
      | running f =>
        simp [runFor, rawTick_complete head, hb fuel enough]
      | returned v f => cases head

/-- Unlike runFor, execute needs enough fuel to include the return step. -/
theorem Steps.execute_complete
    (complete : Steps c (.running f) events (.returned value final)) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      execute fuel c f = some ⟨value, final, events⟩ := by
  generalize hs : Machine.running f = start at complete
  generalize he : Machine.returned value final = finish at complete
  induction complete generalizing f with
  | nil => cases hs.trans he.symm
  | @cons start first middle rest finish head tail ih =>
    cases hs
    cases middle with
    | returned v g =>
      obtain ⟨rfl, eq⟩ := tail.returned_only
      cases he.trans eq
      refine ⟨1, ?_⟩
      intro fuel hf
      cases fuel with
      | zero => omega
      | succ fuel => simp [execute, tick_complete head]
    | running g =>
      obtain ⟨bound, hb⟩ := ih rfl he
      refine ⟨bound + 1, ?_⟩
      intro fuel hf
      cases fuel with
      | zero => omega
      | succ fuel =>
        have enough : bound ≤ fuel := by omega
        simp [execute, tick_complete head, hb fuel enough]

end Jihoo.BoundedMir
