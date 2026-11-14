import Jihoo.NativeCheckerSoundness

/-! Bounded iteration and Nat induction in the existing native syntax.
Fold/Loop remain neutral for conversion; these theorems verify typing alone. -/
namespace Jihoo.NativeKernel.Checker.LoopExamples

private def zero : Term := .natural 0
private def one : Term := .natural 1
private def two : Term := .natural 2
private def u64Motive : Term := .lam false .u64 .u64
private def i64Motive : Term := .lam false .u64 .i64

private def u64Step (n : Term) : Term :=
  .lam false .u64 (.lam true (.lt (.var 0) (n.rename Nat.succ))
    (.lam false .u64 (.uadd (.var 0) one)))

private def i64Step (n : Term) : Term :=
  .lam false .u64 (.lam true (.lt (.var 0) (n.rename Nat.succ))
    (.lam false .i64 (.arith .add (.var 0) (.integer 1))))

private def proofMotive : Term := .lam false .u64 (.lt (.var 0) (.uadd (.var 0) one))

/-- The step uses its induction hypothesis, not a fresh closed decision. -/
private def proofStep (n : Term) : Term :=
  .lam false .u64 (.lam true (.lt (.var 0) (n.rename Nat.succ))
    (.lam true (.lt (.var 1) (.uadd (.var 1) one))
      (.ltAdd (.var 2) (.uadd (.var 2) one) one (.var 0))))

private def induction : Term := .lam false .u64
  (.loop (.var 0) proofMotive (.decide zero one) (proofStep (.var 0)))

private def refinementMotive : Term :=
  .lam false .u64 (.refine (.lam false .u64 (.eq (.var 0) (.var 1))))

private def refinementInit : Term :=
  .pack (.lam false .u64 (.eq (.var 0) zero)) zero (.refl zero)

private def refinementStep (n : Term) : Term :=
  .lam false .u64 (.lam true (.lt (.var 0) (n.rename Nat.succ))
    (.lam false (.refine (.lam false .u64 (.eq (.var 0) (.var 2))))
      (.pack (.lam false .u64 (.eq (.var 0) (.uadd (.var 3) one)))
        (.uadd (.var 2) one) (.refl (.uadd (.var 2) one)))))

theorem fold_i64 : infer 48 [] false (.fold two (.integer 0) (i64Step two)) = some .i64 := by cbv

theorem fold_wrong_unsigned_accumulator : infer 48 [] false (.fold two zero (u64Step two)) = none := by cbv

theorem fold_wrong_count : infer 48 [] false (.fold (.integer 2) (.integer 0) (i64Step two)) = none := by cbv

theorem loop_u64 : check 48 [] false (.loop two u64Motive zero (u64Step two)) .u64 = true := by cbv

theorem loop_i64 : check 48 [] false (.loop two i64Motive (.integer 0) (i64Step two)) .i64 = true := by cbv

theorem loop_refinement : check 64 [] false
    (.loop two refinementMotive refinementInit (refinementStep two))
    (.refine (.lam false .u64 (.eq (.var 0) two))) = true := by cbv

theorem nat_induction_proof : check 64 [] true induction
    (.pi false .u64 (.lt (.var 0) (.uadd (.var 0) one))) = true := by cbv

theorem nat_induction_typed : HasType [] true induction
    (.pi false .u64 (.lt (.var 0) (.uadd (.var 0) one))) := check_sound nat_induction_proof

theorem concrete_induction : check 64 [] true
    (.loop two proofMotive (.decide zero one) (proofStep two)) (.lt two (.natural 3)) = true := by cbv

theorem loop_wrong_initial_type : infer 48 [] false
    (.loop two u64Motive (.integer 0) (u64Step two)) = none := by cbv

theorem loop_wrong_step_type : infer 48 [] false
    (.loop two u64Motive zero (i64Step two)) = none := by cbv

theorem loop_type_motive_rejected : infer 48 [] true
    (.loop two (.lam false .u64 (.univ 0)) .u64 (u64Step two)) = none := by cbv

theorem loop_array_layout_rejected : infer 48 [] false
    (.loop two (.lam false .u64 (.array (.var 0))) (.elements 0 []) (u64Step two)) = none := by cbv

theorem loop_function_accumulator_rejected : infer 48 [] false
    (.loop two (.lam false .u64 (.pi false .u64 .u64))
      (.lam false .u64 (.var 0)) (u64Step two)) = none := by cbv

theorem loop_owned_accumulator_pending : infer 48 [] false
    (.loop two (.lam false .u64 (.node .buffer [one]))
      (.node .alloc [one, .integer 0]) (u64Step two)) = none := by cbv

theorem proof_accumulator_must_be_erased : infer 48 [] true
    (.loop two proofMotive (.decide zero one)
      (.lam false .u64 (.lam true (.lt (.var 0) two)
        (.lam false (.lt (.var 1) (.uadd (.var 1) one)) (.var 0))))) = none := by cbv

theorem false_induction_entry_rejected : infer 48 [] true
    (.loop two proofMotive (.decide zero zero) (proofStep two)) = none := by cbv

theorem false_induction_step_rejected : infer 48 [] true
    (.loop two proofMotive (.decide zero one)
      (.lam false .u64 (.lam true (.lt (.var 0) two)
        (.lam true (.lt (.var 1) (.uadd (.var 1) one)) (.var 0))))) = none := by cbv

theorem scalar_loop_not_unrolled : check 48 [] true (.refl two)
    (.eq (.loop two u64Motive zero (u64Step two)) two) = false := by cbv

theorem pure_profile_rejects_owned_body : repeatPure
    (.lam false .u64 (.lam true (.lt (.var 0) two)
      (.lam false .i64 (.node .free [.node .alloc [one, .integer 0], .var 0])))) = false := by cbv

theorem pure_profile_rejects_effectful_function_expression : repeatPure
    (.node .free [.node .alloc [one, .integer 0], i64Step two]) = false := by cbv

theorem zero_fuel_loop_rejected : infer 0 [] false (.loop two u64Motive zero (u64Step two)) = none := rfl

end Jihoo.NativeKernel.Checker.LoopExamples
