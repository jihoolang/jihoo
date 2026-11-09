import Jihoo.QuantityErasure
namespace Jihoo.Quantity.Erasure.Examples

/-- Two ghost slots straddle a local owner. Both owners keep their identities. -/
def mixed : Control := .scope .erased (.scope .linear
  (.scope .erased (.seq (.use 1) (.use 3))))
theorem mixed_compacts : erase mixed = .scope .linear (.seq (.use 0) (.use 1)) := by decide
theorem mixed_demand : mixed.demand 0 = some 1 := by decide
theorem mixed_finishes : Finishes (erase mixed) [0] := .bind (.seq .use .use)
theorem mixed_target_once (run : Finishes (erase mixed) xs) : xs.count 0 = 1 :=
  finished_count mixed_demand run

def trapAfter : Control := .scope .erased (.seq (.use 1) .trap)
theorem trap_prefix : Prefix (erase trapAfter) [0] := .seqRight .use .start
theorem trap_target_at_most_once (run : Prefix (erase trapAfter) xs) : xs.count 0 ≤ 1 :=
  prefix_count (by decide : trapAfter.demand 0 = some 1) run

def loop : Control := .repeat (.scope .erased (.scope .linear (.use 0)))
theorem loop_compacts : erase loop = .repeat (.scope .linear (.use 0)) := by decide
theorem loop_no_capture (run : Prefix (erase loop) xs) : xs.count 0 = 0 := by
  exact Nat.eq_zero_of_le_zero (prefix_count (by decide : loop.demand 0 = some 0) run)

/-- Retained modes may NOT be compacted as if they were ghost slots. -/
theorem retain_borrowed_unrestricted :
    erase (.scope .borrowed (.scope .unrestricted (.scope .erased (.use 3)))) =
    .scope .borrowed (.scope .unrestricted (.use 2)) := by decide

/-- This counterexample is why checking the erased target is insufficient. -/
theorem target_check_not_source_check : ∃ c,
    c.demand 0 = none ∧ (erase c).demand 0 = some 0 :=
  ⟨.scope .erased (.use 0), by decide, by decide⟩

theorem duplication_survives :
    (erase (.scope .erased (.seq (.use 1) (.use 1)))).demand 0 = some 2 := by decide

theorem capture_still_rejected :
    (erase (.scope .erased (.closure (.use 1)))).demand 0 = none := by decide

end Jihoo.Quantity.Erasure.Examples
