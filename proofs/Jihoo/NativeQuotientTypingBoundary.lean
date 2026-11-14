import Jihoo.NativeEnvironmentContextualPreservation

/-! Symmetric arithmetic quotient paths are not typing-preserving evaluation.
An actual typed U64 term has a QPar/QStar successor which cannot have any type.
The forward MixedRed preservation theorem is unaffected. -/
namespace Jihoo.NativeKernel.Environment.QuotientTypingBoundary

def source : Term := .strict .u64 (.natural 0)
def target : Term := .strict (.uadd .u64 (.natural 0)) (.natural 0)

private def StrictLeft (env : Environment) (ctx : Context) (mode : Bool) : Term → Prop
  | .strict left _ => ∃ type, HasType env ctx mode left type
  | _ => True

private theorem strictLeft (typed : HasType env ctx mode term type) : StrictLeft env ctx mode term := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun ctx mode term _ _ => StrictLeft env ctx mode term)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case strict left right _ _ => exact ⟨_,left⟩
  case dataElim =>
    rename_i family entry analysis ctx motive proof ghost scrutinee indices types branches found isData boxed size motiveTyped scrutineeTyped generated branchTyped allowed ihm ihs ihb
    cases analysis <;> trivial

theorem source_typed : HasType env ctx mode source .u64 :=
  .strict .u64 (.natural (by decide))

theorem target_untypable (wf : UnifiedProgram.EnvWellFormed env) : ¬ HasType env ctx mode target type := by
  intro typed
  obtain ⟨_,left⟩ := strictLeft typed
  have bad := left.uaddView.1
  have separated := (HasType.u64 (env := env) (ctx := ctx) (ghost := true)).unique wf bad
  exact EnvironmentDelta.Basis.Conv.full_rigid_disjoint (op := .universe 0) (op' := .u64)
    rfl rfl (by intro same; cases same) separated wf.admissible

theorem quotient_parallel_step : ACU.QPar source target :=
  .arithmetic (.node .strict (.cons (.symm (.zero .u64)) (.cons (.refl _) .nil)))

theorem quotient_star_step : ACU.QStar source target := .cons quotient_parallel_step .refl

/-- Even restricting the source and result type to U64 cannot repair the
subject-reduction claim for these deliberately symmetric quotient paths. -/
theorem quotient_u64_preservation_false : ¬ (∀ {a b}, ACU.QPar a b →
    HasType empty [] true a .u64 → HasType empty [] true b .u64) := by
  intro assumed
  exact target_untypable (UnifiedProgram.UnifiedProgramChecked.empty.wellFormed) (assumed quotient_parallel_step source_typed)

theorem quotient_star_u64_preservation_false : ¬ (∀ {a b}, ACU.QStar a b →
    HasType empty [] true a .u64 → HasType empty [] true b .u64) := by
  intro assumed
  exact target_untypable (UnifiedProgram.UnifiedProgramChecked.empty.wellFormed) (assumed quotient_star_step source_typed)

end Jihoo.NativeKernel.Environment.QuotientTypingBoundary
