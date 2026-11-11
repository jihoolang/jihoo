import Jihoo.SizedMirLinearValueBounds
import Jihoo.BoundedMirArguments

/-! The checked scalar ABI establishes actual operand contents and their declared
representation kinds. External pointers are still rejected by entryFrame. -/
namespace Jihoo.BoundedMir

set_option linter.unusedSimpArgs false

inductive ArgumentsRel (R : α → β → Prop) : List α → List β → Prop where
  | nil : ArgumentsRel R [] []
  | cons : R a b → ArgumentsRel R as bs → ArgumentsRel R (a :: as) (b :: bs)

theorem ArgumentsRel.imp (related : ArgumentsRel R as bs)
    (change : ∀ a b, R a b → S a b) : ArgumentsRel S as bs := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (change _ _ head) ih

theorem ArgumentsRel.of_map_right (related : ArgumentsRel R as (bs.map f)) :
    ArgumentsRel (fun a b => R a (f b)) as bs := by
  induction bs generalizing as with
  | nil => cases related; exact .nil
  | cons b bs ih => cases related with
    | cons head tail => exact .cons head (ih tail)

theorem bindArguments_preserves
    (run : bindArguments c slots values frame = some out)
    (untouched : slot ∉ slots) : out.locals[slot]? = frame.locals[slot]? := by
  induction slots generalizing values frame with
  | nil => cases values <;> simp_all [bindArguments]
  | cons first rest ih =>
    cases values with
    | nil => simp [bindArguments] at run
    | cons value values =>
      simp only [bindArguments] at run
      split at run
      · have tail := ih run (fun member => untouched (List.mem_cons_of_mem first member))
        have different : slot ≠ first := fun same => untouched (by simp [same])
        exact tail.trans (by by_cases h : first < frame.locals.size <;> simp [Array.set!, Array.setIfInBounds, h, Ne.symm different])
      · contradiction

/-- Successful distinct-slot binding remembers every value and declaration,
not only arity and control state. -/
theorem bindArguments_values
    (run : bindArguments c slots values frame = some out)
    (distinct : slots.Nodup) :
    ArgumentsRel (fun slot value => out.locals[slot]? = some (some value) ∧
      c.locals[slot]? = some (valueType value) ∧ argumentValueValid value = true) slots values := by
  induction slots generalizing values frame with
  | nil =>
    cases values with
    | nil => exact .nil
    | cons => simp [bindArguments] at run
  | cons first rest ih =>
    cases values with
    | nil => simp [bindArguments] at run
    | cons value values =>
      simp only [bindArguments] at run
      split at run
      next guard =>
        have conditions : argumentValueValid value = true ∧
            c.locals[first]? = some (valueType value) ∧ first < frame.locals.size := by
          simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using guard
        have kept := bindArguments_preserves run (List.nodup_cons.mp distinct).1
        refine .cons ⟨?_, conditions.2.1, conditions.1⟩ (ih run (List.nodup_cons.mp distinct).2)
        exact kept.trans (by simp [Array.set!, Array.setIfInBounds, conditions.2.2])
      next => contradiction

theorem entryFrame_values
    (run : entryFrame c entry values = some frame) :
    ArgumentsRel (fun slot value => frame.locals[slot]? = some (some value) ∧
      c.locals[slot]? = some (valueType value) ∧ argumentValueValid value = true)
      entry.argumentSlots.toList values := by
  have distinct := entryValid_distinct (entryFrame_signature run)
  unfold entryFrame at run
  split at run
  · exact bindArguments_values run distinct
  · contradiction

end Jihoo.BoundedMir

namespace Jihoo.SizedMir.Entry
open BoundedMir

def operands (slots : List Nat) : List Operand := slots.map fun slot => .copy ⟨slot, false⟩

theorem values_related
    (bound : ArgumentsRel (fun slot value => f.locals[slot]? = some (some (toMir value))) slots env) :
    EnvRel env (operands slots) f := by
  induction bound with
  | nil => exact .nil
  | cons head _ ih =>
    apply EnvRel.keep _ ih
    simp [operand, head]

theorem values_kinds
    (bound : ArgumentsRel (fun slot value => types[slot]? = some (valueType (toMir value))) slots env) :
    InputKindsAgree types (operands slots) env := by
  induction bound with
  | nil => rfl
  | @cons slot value slots env head _ ih =>
    cases value <;>
      simp_all [InputKindsAgree, inputKinds, operands, operandType, toMir, valueType, toKind, kindOf]

theorem values_bounded
    (bound : ArgumentsRel (fun (_ : Nat) value => argumentValueValid (toMir value) = true) slots env) :
    Linear.EnvBounded env := by
  induction bound with
  | nil => intro value member; simp at member
  | @cons slot value slots env head _ ih =>
    apply Linear.EnvBounded.cons ih
    cases value <;> simp_all [toMir, argumentValueValid, Linear.ValueBounded]

/-- These are conclusions of actual checked ABI admission, not independent
assumptions about a manually constructed initial frame. -/
theorem checked_arguments
    (run : entryFrame c entry (env.map toMir) = some frame) :
    EnvRel env (operands entry.argumentSlots.toList) frame ∧
    InputKindsAgree c.locals (operands entry.argumentSlots.toList) env ∧
    Linear.EnvBounded env := by
  have bound := entryFrame_values run
  have related : ArgumentsRel (fun slot value => frame.locals[slot]? = some (some (toMir value)))
      entry.argumentSlots.toList env := by
    exact (bound.imp (fun _ _ h => h.1)).of_map_right
  have kinds : ArgumentsRel (fun slot value => c.locals[slot]? = some (valueType (toMir value)))
      entry.argumentSlots.toList env := by
    exact (bound.imp (fun _ _ h => h.2.1)).of_map_right
  have widths : ArgumentsRel (fun (_ : Nat) value => argumentValueValid (toMir value) = true)
      entry.argumentSlots.toList env := by
    exact (bound.imp (fun _ _ h => h.2.2)).of_map_right
  exact ⟨values_related related, values_kinds kinds, values_bounded widths⟩

end Jihoo.SizedMir.Entry
