import Jihoo.NativeEnvironmentConversionBasis
import Jihoo.NativeACUInjectivityAPI

/-! Checked-environment shape consequences of actual delta/ACU confluence.
Global itself is not rigid: a checked definition may unfold to a Pi or any
other constructor. All public separation premises exclude that invalid case. -/
namespace Jihoo.NativeKernel.EnvironmentDelta.Basis

def rigid (op : Op) : Bool := GlobalEnvironment.ordinary op && ACU.fullRigid op

private theorem reflected_children
    (related : NativeKernel.Conversion.ListRel ACU.Conv
      (EnvironmentDelta.expandArgs env xs) (EnvironmentDelta.expandArgs env ys)) :
    NativeKernel.Conversion.ListRel (Conv env) xs ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact .nil
      | cons => simp only [EnvironmentDelta.expandArgs] at related; cases related
  | cons x xs ih =>
      cases ys with
      | nil => simp only [EnvironmentDelta.expandArgs] at related; cases related
      | cons y ys =>
          simp only [EnvironmentDelta.expandArgs] at related
          cases related with
          | cons first rest => exact .cons (.ofProjected first) (ih rest)

theorem Conv.full_rigid_node_injective (converted : Conv env (.node op xs) (.node op' ys))
    (left : rigid op = true) (right : rigid op' = true) (admissible : Admissible env) :
    op = op' ∧ NativeKernel.Conversion.ListRel (Conv env) xs ys := by
  have leftParts := Bool.and_eq_true_iff.mp left
  have rightParts := Bool.and_eq_true_iff.mp right
  have actual := converted.toProjected admissible
  change ACU.Conv (expand env (.node op xs)) (expand env (.node op' ys)) at actual
  rw [expand_ordinary leftParts.1, expand_ordinary rightParts.1] at actual
  obtain ⟨same, children⟩ := actual.full_rigid_node_injective leftParts.2 rightParts.2
  exact ⟨same, reflected_children children⟩

theorem Conv.full_rigid_disjoint (left : rigid op = true) (right : rigid op' = true)
    (different : op ≠ op') (converted : Conv env (.node op xs) (.node op' ys))
    (admissible : Admissible env) : False :=
  different (converted.full_rigid_node_injective left right admissible).1

theorem Conv.full_variable_node_separate (head : rigid op = true)
    (converted : Conv env (.var x) (.node op xs)) (admissible : Admissible env) : False := by
  have parts := Bool.and_eq_true_iff.mp head
  have actual := converted.toProjected admissible
  change ACU.Conv (expand env (.var x)) (expand env (.node op xs)) at actual
  rw [expand_ordinary parts.1] at actual
  exact ACU.Conv.full_variable_node_separate parts.2 (by simpa only [expand] using actual)

theorem Conv.array_injective (converted : Conv env (.array a) (.array b)) (admissible : Admissible env) :
    Conv env a b := by
  obtain ⟨_, children⟩ := converted.full_rigid_node_injective rfl rfl admissible
  cases children with | cons first rest => exact first

theorem Conv.eq_injective (converted : Conv env (.eq a b) (.eq a' b')) (admissible : Admissible env) :
    Conv env a a' ∧ Conv env b b' := by
  obtain ⟨_, children⟩ := converted.full_rigid_node_injective rfl rfl admissible
  cases children with | cons first rest => cases rest with | cons second rest => exact ⟨first, second⟩

theorem Conv.lt_injective (converted : Conv env (.lt a b) (.lt a' b')) (admissible : Admissible env) :
    Conv env a a' ∧ Conv env b b' := by
  obtain ⟨_, children⟩ := converted.full_rigid_node_injective rfl rfl admissible
  cases children with | cons first rest => cases rest with | cons second rest => exact ⟨first, second⟩

theorem Conv.refine_injective (converted : Conv env (.refine a) (.refine b)) (admissible : Admissible env) :
    Conv env a b := by
  obtain ⟨_, children⟩ := converted.full_rigid_node_injective rfl rfl admissible
  cases children with | cons first rest => exact first

theorem Conv.natural_injective (converted : Conv env (.natural a) (.natural b)) (admissible : Admissible env) :
    a = b := by
  have actual := converted.toProjected admissible
  change ACU.Conv (expand env (.natural a)) (expand env (.natural b)) at actual
  exact ACU.Conv.full_natural_injective (by simpa only [expand, expandArgs] using actual)

theorem Conv.full_universe_injective (converted : Conv env (.univ a) (.univ b)) (admissible : Admissible env) :
    a = b := by
  have same : SortTag.type a = SortTag.type b := converted.sort_injective admissible
  exact SortTag.type.inj same

end Jihoo.NativeKernel.EnvironmentDelta.Basis
