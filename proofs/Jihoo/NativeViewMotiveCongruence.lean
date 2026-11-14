import Jihoo.NativeViewBindingAlgebra

/-! Structural full actual-ACU congruence of borrowed-view motives. The concrete
field plan never depends on the motive; all proof and borrow slots are retained. -/
namespace Jihoo.NativeKernel.Environment
set_option linter.unusedSimpArgs false

theorem viewHypothesisType_motive_congr (closed : Conversion.Closed env) (h : Conversion.Conv env motive motive') :
    Conversion.Conv env (viewHypothesisType fields motive dependent position q)
      (viewHypothesisType fields motive' dependent position q) := by
  cases dependent with
  | false => exact h.renaming _ closed
  | true => exact .node .app (.cons (h.renaming _ closed) (.cons (.refl _) .nil))

theorem viewHypothesisTelescope_congr (closed : Conversion.Closed env) (hm : Conversion.Conv env motive motive')
    (hb : Conversion.Conv env body body') (positions : List Nat) (offset : Nat) :
    Conversion.Conv env (viewHypothesisTelescope fields offset positions motive dependent body)
      (viewHypothesisTelescope fields offset positions motive' dependent body') := by
  induction positions generalizing offset with
  | nil => exact hb
  | cons position positions ih =>
    simp only [viewHypothesisTelescope,List.zipIdx_cons,List.foldr_cons]
    exact .node (.pi false) (.cons (viewHypothesisType_motive_congr closed hm) (.cons (ih (offset + 1)) .nil))

theorem viewCaseResult_motive_congr (closed : Conversion.Closed env) (h : Conversion.Conv env motive motive') :
    Conversion.Conv env (viewCaseResult family constructor fields hypotheses ps motive borrowed dependent)
      (viewCaseResult family constructor fields hypotheses ps motive' borrowed dependent) := by
  cases dependent with
  | false => exact h.renaming _ closed
  | true => exact .node .app (.cons (h.renaming _ closed) (.cons (.refl _) .nil))

theorem viewCaseType_motive_congr (closed : Conversion.Closed env) (h : Conversion.Conv env motive motive')
    (generated : viewCaseType env family constructor params depth signature ps motive recursion dependent = some type) :
    ∃ type',viewCaseType env family constructor params depth signature ps motive' recursion dependent = some type' ∧
      Conversion.Conv env type type' := by
  unfold viewCaseType at generated ⊢
  split at generated
  · contradiction
  · rename_i valid
    simp only [valid,ite_false]
    cases planned : viewPlan env family (signature.fields.drop params) with
    | none => simp [planned] at generated
    | some plans =>
      simp only [planned,Bind.bind,Option.bind] at generated ⊢
      cases generated
      exact ⟨_,by simp only [Bool.false_eq_true,ite_false],closeDataFields_congr
        (viewHypothesisTelescope_congr closed h (viewCaseResult_motive_congr closed h) _ _) _⟩

private theorem viewMapM_relation {α : Type} (xs : List α) (f g : α → Option Term)
    (transports : ∀ x ∈ xs,∀ value,f x = some value →
      ∃ value',g x = some value' ∧ Conversion.Conv env value value')
    (generated : xs.mapM f = some values) :
    ∃ values',xs.mapM g = some values' ∧ Conversion.ListRel (Conversion.Conv env) values values' := by
  induction xs generalizing values with
  | nil =>
    simp only [List.mapM_nil,pure,Option.some.injEq] at generated
    subst values
    exact ⟨[],rfl,.nil⟩
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
        obtain ⟨value',head',converted⟩ := transports x (by simp) value head
        obtain ⟨rest',tail',convertedRest⟩ := ih
          (fun x member => transports x (by simp [member])) tail
        exact ⟨value' :: rest',by simp only [head',tail',Bind.bind,Option.bind,pure],
          .cons converted convertedRest⟩

theorem viewCaseTypes_motive_congr (closed : Conversion.Closed env) (h : Conversion.Conv env motive motive')
    (generated : viewCaseTypes env family params depth signatures ps motive recursion dependent = some types) :
    ∃ types',viewCaseTypes env family params depth signatures ps motive' recursion dependent = some types' ∧
      Conversion.ListRel (Conversion.Conv env) types types' := by
  unfold viewCaseTypes at generated ⊢
  apply viewMapM_relation _ _ _ _ generated
  intro pair _ value found
  exact viewCaseType_motive_congr closed h found

end Jihoo.NativeKernel.Environment
