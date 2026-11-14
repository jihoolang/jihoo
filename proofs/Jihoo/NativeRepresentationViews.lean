import Jihoo.NativePlainIndices

namespace Jihoo.NativeKernel.Environment.Representation
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}
open Environment.Conversion

def BorrowOwnedView (env : Environment) (ctx : Context) : Term → Prop
  | .borrow owner => ∃ ownerType, Owned env ownerType ∧ HasType env ctx true owner ownerType
  | _ => True

private theorem case_not_borrow (analysis : Bool) (family count : Nat) (arguments : List Term) :
    BorrowOwnedView env ctx (.node (if analysis then .caseOf family count else .elim family count) arguments) := by
  cases analysis <;> trivial

theorem borrow_owned_view (typed : HasType env ctx mode term type) : BorrowOwnedView env ctx term := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun ctx _ term _ _ => BorrowOwnedView env ctx term)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case ghostBorrow =>
    rename_i typed _
    exact ⟨_,Owned.buffer (.refl _),typed⟩
  case ghostBorrowOwned =>
    rename_i typed owned _
    exact ⟨_,owned,typed⟩
  case dataElim =>
    exact case_not_borrow _ _ _ _

theorem owned_not_u64 (wf : UnifiedProgram.EnvWellFormed env) (owned : Owned env type) : ¬ Conv env type .u64 := by
  intro converted
  cases owned with
  | buffer buffer =>
      exact EnvironmentDelta.Basis.Conv.full_rigid_disjoint (op := .buffer) (op' := .u64) rfl rfl
        (by intro equality; cases equality) (.trans (.symm buffer) converted) wf.admissible
  | family found boxed family =>
      exact EnvironmentDelta.Basis.Conv.full_rigid_disjoint (op := .ind _ _) (op' := .u64) rfl rfl
        (by intro equality; cases equality) (.trans (.symm family) converted) wf.admissible

theorem PlainIndices.lambdaBody (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (plain : PlainIndices env ctx (.lam erased domain body)) :
    PlainIndices env (⟨domain,erased⟩ :: ctx) body := by
  cases plain with
  | index typed => exact False.elim (u64_not_lambda history typed (.refl _))
  | node head _ => simp [plainNode] at head
  | lam body => exact body

theorem PlainIndices.children (plain : PlainIndices env ctx (.node op arguments))
    (binders : ∀ index, op.binders index = 0)
    (notIndex : ¬ HasType env ctx true (.node op arguments) .u64) :
    ∀ child ∈ arguments, PlainIndices env ctx child := by
  cases plain with
  | index typed => exact False.elim (notIndex typed)
  | node _ children => exact children
  | lam => have impossible := binders 1; contradiction
  | ifLt => have impossible := binders 2; contradiction
  | ifEq => have impossible := binders 2; contradiction

end Jihoo.NativeKernel.Environment.Representation
