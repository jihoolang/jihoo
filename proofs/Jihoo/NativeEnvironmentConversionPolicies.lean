import Jihoo.NativeEnvironmentConversionShapes

/-! Positive runtime head certificates that remain valid when the checked
prefix grows. Negating all Pi conversions alone has no such property when a
formerly unresolved global acquires a definition. -/
namespace Jihoo.NativeKernel.EnvironmentDelta.Basis

def nonFunctionOp : Op → Bool
  | .universe _ | .prop | .u64 | .i64 | .array | .lt | .eq | .refine
  | .buffer | .ref | .back _ | .ind _ _ => true
  | _ => false

def nonFunctionHead : Term → Bool
  | .var _ => true
  | .node op _ => nonFunctionOp op

def NonFunction (env : Environment) (term : Term) : Prop :=
  ∃ normal, Conv env term normal ∧ nonFunctionHead normal = true

theorem nonFunctionOp_rigid (head : nonFunctionOp op = true) : rigid op = true := by
  cases op <;> simp_all [nonFunctionOp, rigid, GlobalEnvironment.ordinary,
    ACU.fullRigid, NativeKernel.Conversion.rigid, ACU.arithmeticRigid]

theorem nonFunctionOp_not_pi (head : nonFunctionOp op = true) : op ≠ .pi erased := by
  intro same
  subst op
  contradiction

theorem NonFunction.ofHead (head : nonFunctionHead term = true) : NonFunction env term :=
  ⟨term, .refl _, head⟩

theorem NonFunction.of_conversion (converted : Conv env a b) (result : NonFunction env b) : NonFunction env a := by
  obtain ⟨normal, reduced, head⟩ := result
  exact ⟨normal, converted.trans reduced, head⟩

theorem NonFunction.extend (result : NonFunction before term) (extension : Environment.Extends before after) :
    NonFunction after term := by
  obtain ⟨normal, reduced, head⟩ := result
  exact ⟨normal, reduced.extend extension, head⟩

theorem NonFunction.not_pi (result : NonFunction env term) (converted : Conv env term (.pi erased domain body))
    (admissible : Admissible env) : False := by
  obtain ⟨normal, reduced, head⟩ := result
  have clash := reduced.symm.trans converted
  cases normal with
  | var index => exact Conv.full_variable_node_separate rfl clash admissible
  | node op arguments =>
      exact Conv.full_rigid_disjoint (nonFunctionOp_rigid head) rfl (nonFunctionOp_not_pi head) clash admissible

theorem NonFunction.pi_rejected (admissible : Admissible env) :
    ¬NonFunction env (.pi erased domain body) := by
  intro result
  exact result.not_pi (.refl _) admissible

theorem legacy_nonFunctionHead (head : NativeKernel.nonFunctionHead term = true) : nonFunctionHead term = true := by
  fun_cases NativeKernel.nonFunctionHead term <;>
    simp_all only [NativeKernel.nonFunctionHead, nonFunctionHead, nonFunctionOp, Bool.false_eq_true]

end Jihoo.NativeKernel.EnvironmentDelta.Basis
