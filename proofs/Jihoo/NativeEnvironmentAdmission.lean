import Jihoo.NativeEnvironmentCheckerSoundness
import Jihoo.NativeFamilyEnvironment
import Jihoo.NativeOwnershipAdmission

/-! Closed native boundaries recompute global/family admission before using
the unified checker. `inferProgram` certifies typing; `checkDeclarationProgram`
also derives the body mode and enforces the closed code quantity gate. External
records and signatures are never trusted. -/
namespace Jihoo.NativeKernel.Environment

def inferProgram (fuel : Nat) (definitions : List GlobalDeclaration)
    (families : List FamilyDeclaration) (ghost : Bool) (term : Term) :
    Option (Environment × Term) := do
  let env ← FamilyEnvironment.checkProgram fuel definitions families
  let type ← Checker.infer fuel env [] ghost term
  pure (env, type)

theorem inferProgram_sound {definitions : List GlobalDeclaration} {families : List FamilyDeclaration}
    (h : inferProgram fuel definitions families ghost term = some (env, type)) :
    FamilyEnvironment.ProgramChecked definitions families env ∧ HasType env [] ghost term type := by
  unfold inferProgram at h
  cases admitted : FamilyEnvironment.checkProgram fuel definitions families with
  | none => simp [admitted] at h
  | some result =>
      simp only [admitted, Bind.bind, Option.bind] at h
      cases inferred : Checker.infer fuel result [] ghost term with
      | none => simp [inferred] at h
      | some actual =>
          simp only [inferred] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact ⟨FamilyEnvironment.checkProgram_sound admitted, Checker.infer_sound inferred⟩

/-- Executable admission of one closed declaration over a recomputed history.
Callers supply source declarations, never trusted external signatures or modes. -/
def checkDeclarationProgram (fuel quantityFuel : Nat) (definitions : List GlobalDeclaration)
    (familyDeclarations : List FamilyDeclaration) (declaration : GlobalDeclaration) : Bool :=
  match FamilyEnvironment.checkProgram fuel definitions familyDeclarations with
  | none => false
  | some env => NativeOwnershipAdmission.check fuel quantityFuel env declaration

theorem checkDeclarationProgram_sound {definitions : List GlobalDeclaration}
    {familyDeclarations : List FamilyDeclaration}
    (h : checkDeclarationProgram fuel quantityFuel definitions familyDeclarations declaration = true) :
    ∃ env, FamilyEnvironment.ProgramChecked definitions familyDeclarations env ∧
      NativeOwnershipAdmission.Valid env declaration := by
  cases admitted : FamilyEnvironment.checkProgram fuel definitions familyDeclarations with
  | none => simp [checkDeclarationProgram, admitted] at h
  | some env =>
      have accepted : NativeOwnershipAdmission.check fuel quantityFuel env declaration = true := by
        simpa only [checkDeclarationProgram, admitted] using h
      exact ⟨env, FamilyEnvironment.checkProgram_sound admitted, NativeOwnershipAdmission.check_sound accepted⟩

end Jihoo.NativeKernel.Environment
