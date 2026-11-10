import Jihoo.CorePayloadAdequacy
import Jihoo.CorePrimitiveExamples

/-! The examples distinguish removal of proof payloads from skipping runtime
work. The general reflection theorems do not require these closed fixtures. -/
namespace Jihoo.CoreBridge.Raw.Beta.PayloadErasure.Examples
open Evaluation PrimitiveExamples

/-- Both sides retain the erased binder and application. Only the proof and
annotation payload changes; its overflowing arithmetic is not runtime work. -/
theorem different_proof_payloads_same_runtime :
    PayloadErasure.erase erasedOverflow = PayloadErasure.erase simpleEvidence := evidence_payloads_agree

/-- Runtime arguments are strict even when their result is discarded. -/
theorem runtime_argument_still_traps : Trap (PayloadErasure.erase discardTrap) :=
  trap_erasure discard_argument_traps

/-- Selecting the first array entry cannot skip later runtime entry evaluation. -/
theorem later_array_entry_still_traps : Trap (PayloadErasure.erase arrayTrap) :=
  trap_erasure unselected_element_traps

/-- Source typing is not asserted of the intermediate erased carrier: replacing
an erased proposition domain by U64 intentionally leaves its source mode rule. -/
theorem erased_lambda_not_source_typed :
    ¬ HasType (fun _ => none) (PayloadErasure.erase (.lam true (.lt (.natural 0) (.natural 1)) (.integer 7))) A := by
  intro h
  simp only [PayloadErasure.erase] at h
  have hh := h.lam_inversion
  simp [proposition] at hh

/-- Noninjectivity is expected: endpoint equality must be equality after
payload erasure, not equality of the original annotations. -/
theorem annotations_not_injective :
    PayloadErasure.erase (.lam false .u64 (.var 0)) = PayloadErasure.erase (.lam false .i64 (.var 0)) ∧
      (.lam false .u64 (.var 0) : Raw) ≠ .lam false .i64 (.var 0) := by
  constructor
  · simp only [PayloadErasure.erase]
  · intro h; cases h

/-- Retained nested runtime binders still use capture-avoiding substitution. -/
theorem retained_binder_capture :
    PayloadErasure.erase ((Raw.lam false .u64 (.app (.var 1) (.var 0))).subst (single (.var 2))) =
      .lam false .u64 (.app (.var 3) (.var 0)) := by
  simp [subst, single, liftSub, rename, PayloadErasure.erase]

/-- The same proof-payload equivalence controls every integer result, not just
one hand-selected execution. -/
theorem proof_payloads_all_integer_results (z : Int) :
    Evaluation.Steps erasedOverflow (.integer z) ↔
      Evaluation.Steps simpleEvidence (.integer z) :=
  equal_erasure_integer evidence_payloads_agree

theorem proof_payloads_all_trap_outcomes :
    (∃ u, Evaluation.Steps erasedOverflow u ∧ Trap u) ↔
      (∃ u, Evaluation.Steps simpleEvidence u ∧ Trap u) :=
  equal_erasure_trap evidence_payloads_agree

theorem runtime_erased_all_results (z : Int) :
    Evaluation.Steps (PayloadErasure.erase strictScalar) (.integer z) ↔
      Evaluation.Steps strictScalar (.integer z) := integer_execution_iff

theorem ready_prefix_array_reflection (v : Raw)
    (run : Evaluation.Steps (PayloadErasure.erase (.elements [.integer 1, strictScalar])) v) :
    ∃ u, Evaluation.Steps (.elements [.integer 1, strictScalar]) u ∧ PayloadErasure.erase u = v :=
  steps_reflection run

theorem erased_overflow_one_step : StepsN 1 (PayloadErasure.erase erasedOverflow) (.integer 7) := by
  exact .next (by simpa only [erase] using step_erasure erased_overflow_computes) .refl

/-- The source witness retains its true annotation while the erased endpoint
is the exact integer. No intermediate source typing of erased Raw is needed. -/
theorem original_overflow_one_step : StepsN 1 erasedOverflow (.integer 7) :=
  .next erased_overflow_computes .refl

end Jihoo.CoreBridge.Raw.Beta.PayloadErasure.Examples
