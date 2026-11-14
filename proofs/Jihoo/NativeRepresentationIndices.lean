import Jihoo.NativeEnvironmentContextualPreservation
import Jihoo.NativeEnvironmentTypeUniqueness
import Jihoo.NativeEnvironmentPlainSeparation

/-! A U64 index is not assumed to be a bounded literal or syntactically plain.
Its exclusion from type/function heads follows from genuine forward common
reducts, actual ghost preservation, and independent typing inversion. -/
namespace Jihoo.NativeKernel.Environment.Representation
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}
open Environment.Conversion

theorem sort_not_u64 (admissible : EnvironmentDelta.Admissible env) (sort : SortTag) :
    ¬ Conv env sort.term .u64 := by
  cases sort with
  | prop =>
      intro converted
      exact EnvironmentDelta.Basis.Conv.full_rigid_disjoint (op := .prop) (op' := .u64)
        rfl rfl (by intro equality; cases equality) converted admissible
  | type level =>
      intro converted
      exact EnvironmentDelta.Basis.Conv.full_rigid_disjoint (op := .universe level) (op' := .u64)
        rfl rfl (by intro equality; cases equality) converted admissible

/-- A rigid source head survives actual forward reduction with its arity. -/
theorem u64_no_rigid_head (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx mode term .u64) (rigid : EnvironmentDelta.Basis.rigid op = true)
    (reject : ∀ arguments, ¬ HasType env ctx true (.node op arguments) .u64) :
    ¬ Conv env term (.node op arguments) := by
  intro converted
  obtain ⟨common, first, second⟩ := converted.church_rosser history.wellFormed.admissible
  obtain ⟨children, rfl, _⟩ := forward_rigid_shape second rigid rfl
  exact reject children (typed.ghostForward history first)

theorem u64_not_buffer (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx mode term .u64) : ¬ Conv env term (.buffer n) := by
  apply u64_no_rigid_head history typed rfl
  intro arguments impossible
  have view := impossible.principalView
  cases arguments with
  | nil => exact view
  | cons index rest =>
      cases rest with
      | nil => exact sort_not_u64 history.wellFormed.admissible (.type 0) view
      | cons => exact view

theorem u64_not_ref (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx mode term .u64) : ¬ Conv env term (.ref owner) := by
  apply u64_no_rigid_head history typed rfl
  intro arguments impossible
  have view := impossible.principalView
  cases arguments with
  | nil => exact view
  | cons index rest =>
      cases rest with
      | nil => exact sort_not_u64 history.wellFormed.admissible (.type 0) view
      | cons => exact view

theorem u64_not_back (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx mode term .u64) : ¬ Conv env term (.back erased owner motive) := by
  apply u64_no_rigid_head history typed rfl
  intro arguments impossible
  have view := impossible.principalView
  cases arguments with
  | nil => exact view
  | cons first rest => cases rest with
    | nil => exact view
    | cons second rest => cases rest with
      | nil => exact sort_not_u64 history.wellFormed.admissible (.type 0) view
      | cons => exact view

theorem u64_not_pi (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx mode term .u64) : ¬ Conv env term (.pi erased domain result) := by
  apply u64_no_rigid_head history typed rfl
  intro arguments impossible
  have view := impossible.principalView
  cases arguments with
  | nil => exact view
  | cons first rest => cases rest with
    | nil => exact view
    | cons second rest => cases rest with
      | nil =>
          obtain ⟨left, right, _, _, converted⟩ := view
          exact sort_not_u64 history.wellFormed.admissible (left.pi right) converted
      | cons => exact view

theorem u64_not_family (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx mode term .u64) :
    ¬ Conv env term (.node (.ind family count) indices) := by
  apply u64_no_rigid_head history typed rfl
  intro arguments impossible
  obtain ⟨entry, _, converted⟩ := impossible.principalView
  cases data : entry.declaration.data with
  | false => exact sort_not_u64 history.wellFormed.admissible .prop (by simpa only [data, Bool.false_eq_true, reduceIte, SortTag.term] using converted)
  | true => exact sort_not_u64 history.wellFormed.admissible (.type 0) (by simpa only [data, Bool.false_eq_true, reduceIte, SortTag.term] using converted)

theorem u64_not_lambda (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx mode term .u64) : ¬ Conv env term (.lam erased domain body) := by
  apply u64_no_rigid_head history typed rfl
  intro arguments impossible
  have view := impossible.principalView
  cases arguments with
  | nil => exact view
  | cons first rest => cases rest with
    | nil => exact view
    | cons second rest => cases rest with
      | nil =>
          obtain ⟨_, _, converted⟩ := view
          exact EnvironmentDelta.Basis.Conv.full_rigid_disjoint rfl rfl (by intro equality; cases equality) converted history.wellFormed.admissible
      | cons => exact view

end Jihoo.NativeKernel.Environment.Representation
