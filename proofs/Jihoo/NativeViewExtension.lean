import Jihoo.NativeViewSyntax
import Jihoo.NativeEnvironmentPrefix

/-! Positive lookup transport for authenticated borrowed-field plans. Unknown
family lookups fail; extending a checked prefix preserves each successful plan. -/
namespace Jihoo.NativeKernel.Environment
set_option linter.unusedSimpArgs false

theorem viewFieldPlan_extend (extension : Environment.Extends before after)
    (h : viewFieldPlan before family field = some plan) :
    viewFieldPlan after family field = some plan := by
  unfold viewFieldPlan at h ⊢
  simp only [Option.map] at h ⊢
  repeat' first | split at h | contradiction | (solve | simp_all)
  all_goals
    have transported := extension.families _ _ (by assumption)
    simp_all [transported]

theorem viewPlan_extend (extension : Environment.Extends before after)
    (h : viewPlan before family fields = some plans) : viewPlan after family fields = some plans := by
  unfold viewPlan at h ⊢
  induction fields generalizing plans with
  | nil => exact h
  | cons field fields ih =>
    simp only [List.mapM_cons] at h ⊢
    cases head : viewFieldPlan before family field with
    | none => simp [head] at h
    | some plan =>
      simp only [head,Bind.bind,Option.bind] at h
      cases tail : fields.mapM (viewFieldPlan before family) with
      | none => simp [tail] at h
      | some rest =>
        simp only [tail,Bind.bind,Option.bind,pure,Option.some.injEq] at h
        subst plans
        simp only [viewFieldPlan_extend extension head,ih tail,Bind.bind,Option.bind,pure]

theorem viewCaseType_extend (extension : Environment.Extends before after)
    (generated : viewCaseType before family constructor params depth signature ps motive recursion dependent = some type) :
    viewCaseType after family constructor params depth signature ps motive recursion dependent = some type := by
  unfold viewCaseType at generated ⊢
  split at generated
  · contradiction
  · rename_i valid
    simp only [valid,ite_false]
    cases planned : viewPlan before family (signature.fields.drop params) with
    | none => simp [planned] at generated
    | some plans =>
      simp only [planned,Bind.bind,Option.bind] at generated
      cases generated
      simp only [viewPlan_extend extension planned,Bind.bind,Option.bind,Bool.false_eq_true,ite_false]

private theorem viewMapM_keep {α β : Type} {values : List β} (xs : List α) (f g : α → Option β)
    (keep : ∀ x ∈ xs,∀ value,f x = some value → g x = some value)
    (generated : xs.mapM f = some values) : xs.mapM g = some values := by
  induction xs generalizing values with
  | nil => exact generated
  | cons x xs ih =>
    simp only [List.mapM_cons] at generated ⊢
    cases head : f x with
    | none => simp [head] at generated
    | some value =>
      simp only [head,Bind.bind,Option.bind] at generated
      cases tail : xs.mapM f with
      | none => simp [tail] at generated
      | some rest =>
        simp only [tail,Bind.bind,Option.bind,pure,Option.some.injEq] at generated
        subst values
        simp only [keep x (by simp) value head,
          ih (fun x member => keep x (by simp [member])) tail,Bind.bind,Option.bind,pure]

theorem viewCaseTypes_extend (extension : Environment.Extends before after)
    (generated : viewCaseTypes before family params depth signatures ps motive recursion dependent = some types) :
    viewCaseTypes after family params depth signatures ps motive recursion dependent = some types := by
  unfold viewCaseTypes at generated ⊢
  apply viewMapM_keep _ _ _ _ generated
  intro pair _ type found
  exact viewCaseType_extend extension found

end Jihoo.NativeKernel.Environment
