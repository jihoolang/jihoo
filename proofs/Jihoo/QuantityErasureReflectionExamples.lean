import Jihoo.QuantityRuntimeSlots
import Jihoo.QuantityErasureExamples

namespace Jihoo.Quantity.Erasure.ReflectionExamples

/-- A trap inside a ghost computation was never a runtime observation. -/
theorem ghost_trap_completes : Finishes (erase (.erased .trap)) [] ∧
    Finishes (.erased .trap) [] := ⟨.pure, .erased⟩

/-- A runtime trap cannot be converted into successful completion. -/
theorem live_trap_no_completion :
    ¬ ∃ xs, Finishes (erase (.scope .erased (.seq (.use 1) .trap))) xs := by
  rintro ⟨xs, h⟩
  have source := finishes_reflect _ h
  cases source with
  | bind hb => cases hb with | seq _ ht => cases ht

/-- Recover the original run through two removed slots and a retained owner. -/
theorem nested_reflection (h : Finishes (erase Examples.mixed) xs) :
    Finishes Examples.mixed xs := finishes_reflect _ h

/-- Prefix reflection does not assume that a terminating continuation exists. -/
theorem trapped_prefix_reflection : Prefix Examples.trapAfter [0] :=
  prefix_reflect _ Examples.trap_prefix

/-- Equal payload values do not identify the distinct source binder slots. -/
theorem equal_payload_distinct_slots :
    Slots.position [some 7, none, some 7] 0 = some 0 ∧
    Slots.position [some 7, none, some 7] 2 = some 1 := by decide

theorem compact_lookup_example :
    (Slots.compact [none, some 11, none, some 23])[1]? = some 23 := by decide

theorem missing_slot_example :
    Slots.position [some 7, none, some 9] 1 = none ∧
    Slots.position [some 7, none, some 9] 3 = none := by decide

/-- Reflection is existential: erasing events does not make their histories
injective. A stronger history-reconstruction claim would be false. -/
theorem erased_histories_not_injective :
    Prefix (.use 0) [] ∧ Prefix (.use 0) [0] ∧
    ([] : List Nat).filterMap Substitution.dropBorrow =
      [0].filterMap Substitution.dropBorrow := ⟨.start, .use, rfl⟩

end Jihoo.Quantity.Erasure.ReflectionExamples
