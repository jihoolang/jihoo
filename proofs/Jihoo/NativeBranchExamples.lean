import Jihoo.NativeCheckerSoundness

/-! Executable branch/absurd regressions in the existing full native syntax.
Branch computation remains neutral; these examples check admission and the
proof-binder scope guard, not new conversion equations. -/
namespace Jihoo.NativeKernel.Checker.BranchExamples

private def zero : Term := .natural 0
private def one : Term := .natural 1
private def two : Term := .natural 2
private def predicate : Term := .lam false .u64 (.eq (.var 0) (.var 0))
private def impossible : Context := [⟨.lt zero zero, true⟩]
private def outer : Context := [⟨.u64, false⟩]

/-- A symbolic family indexed by branch evidence, and a function returning
its evidence-dependent type. Removing that evidence slot must fail. -/
private def escaping : Context :=
  [⟨.pi true (.eq zero zero) (.app (.var 1) (.var 0)), false⟩,
   ⟨.pi true (.eq zero zero) (.univ 0), false⟩]

theorem ifLt_scalars : infer 16 [] false (.ifLt zero one (.natural 7) (.natural 8)) = some .u64 := by cbv

theorem ifEq_scalars : infer 16 [] false (.ifEq zero zero (.integer 7) (.integer 8)) = some .i64 := by cbv

theorem true_evidence_available_in_ghost : infer 16 [] true
    (.ifLt zero one (.var 0) (.decide zero one)) = some (.lt zero one) := by cbv

theorem true_evidence_unavailable_as_code : infer 16 [] false
    (.ifLt zero one (.var 0) (.decide zero one)) = none := by cbv

theorem true_evidence_justifies_code_index : infer 24 [] false
    (.ifLt zero two (.index (.elements 2 [.integer (-7), .integer 9]) zero (.var 0))
      (.integer 0)) = some .i64 := by cbv

theorem true_equality_justifies_transport : check 32 [] false
    (.ifEq (.natural 7) (.natural 7)
      (.transport predicate (.var 0) (.refl (.natural 7))) (.refl (.natural 7)))
    (.eq (.natural 7) (.natural 7)) = true := by cbv

theorem mismatched_branches_rejected : infer 16 [] false
    (.ifLt zero one (.natural 7) (.integer 8)) = none := by cbv

theorem wrong_condition_type_rejected : infer 16 [] false
    (.ifLt (.integer 0) one (.natural 7) (.natural 8)) = none := by cbv

theorem branch_evidence_escape_rejected : infer 32 escaping true
    (.ifEq zero zero (.app (.var 1) (.var 0)) (.natural 7)) = none := by cbv

theorem outer_variable_lowered_without_capture : infer 24 outer false
    (.ifLt (.var 0) one (.refl (.var 1)) (.refl (.var 0))) =
      some (.eq (.var 0) (.var 0)) := by cbv

theorem returned_function_reweakening : infer 32 outer false
    (.ifLt (.var 0) one
      (.lam false .u64 (.refl (.var 2))) (.lam false .u64 (.refl (.var 1)))) =
      some (.pi false .u64 (.eq (.var 1) (.var 1))) := by cbv

theorem absurd_code_scalar : infer 16 impossible false (.absurd .u64 (.var 0)) = some .u64 := by cbv

theorem absurd_code_array : infer 16 impossible false (.absurd (.array two) (.var 0)) =
    some (.array two) := by cbv

theorem absurd_refinement : infer 24 impossible false (.absurd (.refine predicate) (.var 0)) =
    some (.refine predicate) := by cbv

theorem absurd_computed_zero_bound : infer 16 [⟨.lt zero (.uadd zero zero), true⟩] false
    (.absurd .i64 (.var 0)) = some .i64 := by cbv

theorem absurd_nonzero_bound_rejected : infer 16 [] false
    (.absurd .u64 (.decide zero one)) = none := by cbv

theorem absurd_nonproof_rejected : infer 16 [] false (.absurd .u64 (.integer 0)) = none := by cbv

theorem absurd_nontype_rejected : infer 16 impossible false (.absurd (.natural 7) (.var 0)) = none := by cbv

theorem absurd_function_result_rejected : infer 24 impossible false
    (.absurd (.pi false .u64 .u64) (.var 0)) = none := by cbv

theorem absurd_function_ghost_check_accepted : infer 24 impossible true
    (.absurd (.pi false .u64 .u64) (.var 0)) = some (.pi false .u64 .u64) := by cbv

/-- Proven variable rigidity admits the native neutral-type case. -/
theorem absurd_neutral_type_accepted : infer 24
    [⟨.lt zero zero, true⟩, ⟨.univ 0, false⟩] false
    (.absurd (.var 1) (.var 0)) = some (.var 1) := by cbv

/-- Neutral application heads remain outside the conservative gate. -/
theorem absurd_neutral_application_gap : infer 24
    [⟨.lt zero zero, true⟩, ⟨.pi false .u64 (.univ 0), false⟩] false
    (.absurd (.app (.var 1) zero) (.var 0)) = none := by cbv

theorem absurd_highest_input_universe : infer 24 impossible false
    (.absurd (.univ 31) (.var 0)) = some (.univ 31) := by cbv

theorem zero_fuel_branch_rejected : infer 0 [] false
    (.ifLt zero one (.natural 7) (.natural 8)) = none := rfl

theorem admitted_branch_typed : HasType [] false
    (.ifLt zero one (.natural 7) (.natural 8)) .u64 := infer_sound ifLt_scalars

theorem admitted_absurd_typed : HasType impossible false (.absurd .u64 (.var 0)) .u64 :=
  infer_sound absurd_code_scalar

end Jihoo.NativeKernel.Checker.BranchExamples
