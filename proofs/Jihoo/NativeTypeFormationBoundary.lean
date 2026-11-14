import Jihoo.NativeEnvironmentTypeUniqueness

/-! Raw result conversion does not imply formation of the converted type.
This is a regularity boundary, not a false-proposition inhabitant. Declaration
admission separately checks that the annotation actually has a sort. -/
namespace Jihoo.NativeKernel.Environment.TypeFormationBoundary

def badType : Term := .uadd .u64 (.natural 0)

theorem converted_value_typed : HasType env ctx mode (.natural 0) badType :=
  (HasType.natural (by decide)).convert (.symm (.acu (.zero .u64)))

theorem bad_type_unformed (wf : UnifiedProgram.EnvWellFormed env) : ¬ HasType env ctx mode badType type := by
  intro typed
  have impossible := typed.uaddView.1
  have separated := (HasType.u64 (env := env) (ctx := ctx) (ghost := true)).unique wf impossible
  exact EnvironmentDelta.Basis.Conv.full_rigid_disjoint (op := .universe 0) (op' := .u64)
    rfl rfl (by intro same; cases same) separated wf.admissible

theorem arbitrary_result_formation_false : ¬ (∀ {term type}, HasType empty [] true term type →
    ∃ sort : SortTag, HasType empty [] true type sort.term) := by
  intro assumed
  obtain ⟨_,formed⟩ := assumed converted_value_typed
  exact bad_type_unformed UnifiedProgram.UnifiedProgramChecked.empty.wellFormed formed

example : Checker.check 16 empty [] true (.natural 0) badType = true := by cbv
example : Checker.sort 16 empty [] badType = none := by cbv
example : UnifiedProgram.checkProgram 16 16 [⟨badType,.natural 0⟩] [] = none := by cbv

end Jihoo.NativeKernel.Environment.TypeFormationBoundary
