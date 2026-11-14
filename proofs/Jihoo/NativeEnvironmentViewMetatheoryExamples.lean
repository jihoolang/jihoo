import Jihoo.NativeEnvironmentContextualPreservation

/-! View metatheory uses the same checked boxed-family history and actual
borrowed-field telescopes; no loan or heap execution theorem is assumed. -/
namespace Jihoo.NativeKernel.Environment.ViewMetatheoryExamples

private abbrev box : Term := .node (.ind 0 0) []
private abbrev buffer : Term := .buffer (.natural 2)
private def declaration : FamilyDeclaration := ⟨true,0,0,[.pi false buffer box],0⟩
private def entry : CheckedFamily := ⟨declaration,[⟨[⟨false,buffer,none⟩],[]⟩],true⟩
private def checkedEnv : Environment := ⟨#[],#[entry]⟩
private theorem history : UnifiedProgram.UnifiedProgramChecked [] [declaration] checkedEnv :=
  UnifiedProgram.checkProgram_sound
    (by cbv : UnifiedProgram.checkProgram 32 32 [] [declaration] = some checkedEnv)
private def value : Term := .node (.con 0 0 1) [.alloc (.natural 2) (.integer 0)]
private def branch : Term := .lam false (.ref buffer) (.natural 0)
private def viewed (motive : Term) : Term := .node (.view false 0 1) [motive,branch,.borrow value]

private theorem constantTyped : HasType checkedEnv [] true (viewed .u64) .u64 :=
  Checker.check_sound (by cbv : Checker.check 32 checkedEnv [] true (viewed .u64) .u64 = true)

theorem constant_result_unique (other : HasType checkedEnv [] mode (viewed .u64) T) :
    Conversion.Conv checkedEnv .u64 T := constantTyped.unique history.wellFormed other

theorem constant_weakened : HasType checkedEnv [⟨.u64,true⟩] true
    ((viewed .u64).rename Nat.succ) .u64 := by
  simpa only [Term.rename,renameArgs] using constantTyped.ghostWeaken history.wellFormed .u64 true

private def dependentMotive : Term := .lam false (.ref box) (.buffer (.var 1))
private def dependentBranch : Term := .lam false (.ref buffer) (.alloc (.var 1) (.integer 0))
private def dependentView : Term := .node (.view false 0 1)
  [dependentMotive,dependentBranch,.borrow value]

/-- The ambient length moves through motive, borrowed-field telescope, and
branch allocation by the proved reading/substitution algebra. -/
theorem dependent_length_instantiated : HasType checkedEnv [] true
    (dependentView.subst (single (.natural 7))) (.buffer (.natural 7)) := by
  have typed : HasType checkedEnv [⟨.u64,true⟩] true dependentView (.buffer (.var 0)) :=
    Checker.check_sound (by cbv : Checker.check 40 checkedEnv [⟨.u64,true⟩] true dependentView (.buffer (.var 0)) = true)
  simpa only [subst_buffer,Term.subst,NativeKernel.single] using typed.ghostInstantiate history.wellFormed
    (HasType.natural (by decide) : HasType checkedEnv [] true (.natural 7) .u64)

private def reducibleMotive : Term := .app (.lam false .u64 .u64) (.natural 0)

theorem motive_contextual_computation : HasType checkedEnv [] true (viewed .u64) .u64 := by
  have typed : HasType checkedEnv [] true (viewed reducibleMotive) .u64 :=
    Checker.check_sound (by cbv : Checker.check 40 checkedEnv [] true (viewed reducibleMotive) .u64 = true)
  have beta : ACU.MixedRed reducibleMotive .u64 := by
    simpa only [reducibleMotive,Term.subst,substArgs] using
      (ACU.MixedRed.compute (.beta false .u64 .u64 (.natural 0)))
  exact typed.ghostMixedRed history.wellFormed
    (.node (.view false 0 1) (.cons beta (.cons (.refl _) (.cons (.refl _) .nil))))

/-- The hidden dependent bit is fixed by the actual motive typing, across
modes and independently convertible owner domains. -/
theorem motive_dependency_unique
    (left : HasType checkedEnv ctx mode motive (viewMotiveType dependent owner))
    (right : HasType checkedEnv ctx otherMode motive (viewMotiveType dependent' owner')) : dependent = dependent' :=
  viewMotiveType_dependency_unique history.wellFormed (left.unique history.wellFormed right)

private def globalMotive : Term := .node (.global 0) []
private def aliasEnv : Environment := ⟨#[⟨.univ 0,.u64⟩],#[entry]⟩
private theorem aliasHistory : UnifiedProgram.UnifiedProgramChecked [⟨.univ 0,.u64⟩] [declaration] aliasEnv :=
  UnifiedProgram.checkProgram_sound
    (by cbv : UnifiedProgram.checkProgram 32 32 [⟨.univ 0,.u64⟩] [declaration] = some aliasEnv)

/-- Global motive unfolding inside View retains its original, independently checked alias type. -/
theorem delta_view_original_alias_type : HasType aliasEnv [] true (viewed .u64) globalMotive := by
  have source : HasType aliasEnv [] true (viewed globalMotive) globalMotive :=
    Checker.check_sound (by cbv : Checker.check 32 aliasEnv [] true (viewed globalMotive) globalMotive = true)
  exact source.ghostNormalize aliasHistory
    (by cbv : Conversion.normalize? aliasEnv 32 (viewed globalMotive) = some (viewed .u64))

/-- A typed finite delta path may be used independently of the concrete search fuel. -/
theorem delta_view_contextual_path : HasType aliasEnv [] true (viewed .u64) globalMotive := by
  have source : HasType aliasEnv [] true (viewed globalMotive) globalMotive :=
    Checker.check_sound (by cbv : Checker.check 32 aliasEnv [] true (viewed globalMotive) globalMotive = true)
  apply source.ghostForward aliasHistory
  exact .node (.view false 0 1) (.cons
    (.delta (env := aliasEnv) (index := 0) (declaration := ⟨.univ 0,.u64⟩) rfl)
    (.cons .refl (.cons .refl .nil)))

end Jihoo.NativeKernel.Environment.ViewMetatheoryExamples
