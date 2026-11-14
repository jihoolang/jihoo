import Jihoo.NativeDataBindingAlgebra

/-! Full actual ACU congruence in data motives. Neither branch generation nor
its recursive/erasure masks inspect the substituted motive. -/
namespace Jihoo.NativeKernel.Environment
set_option linter.unusedSimpArgs false

theorem applications_motive_congr (h : Conversion.Conv env motive motive') (arguments : List Term) :
    Conversion.Conv env (applications motive arguments) (applications motive' arguments) := by
  induction arguments generalizing motive motive' with
  | nil => exact h
  | cons argument arguments ih =>
      exact ih (.node .app (.cons h (.cons (.refl argument) .nil)))

theorem closeDataFields_congr (h : Conversion.Conv env body body') (fields : List (Bool × Term)) :
    Conversion.Conv env (closeDataFields fields body) (closeDataFields fields body') := by
  induction fields with
  | nil => exact h
  | cons field fields ih => exact .node (.pi field.1) (.cons (.refl field.2) (.cons ih .nil))

theorem dataHypothesisType_motive_congr (closed : Conversion.Closed env) (h : Conversion.Conv env motive motive') :
    Conversion.Conv env (dataHypothesisType params fields motive recursive q)
      (dataHypothesisType params fields motive' recursive q) :=
  .node .app (.cons (applications_motive_congr (h.renaming _ closed) _) (.cons (.refl _) .nil))

theorem dataHypothesisTelescope_congr (closed : Conversion.Closed env) (hm : Conversion.Conv env motive motive')
    (hb : Conversion.Conv env body body') (recursive : List (Nat × List Term)) (offset : Nat) :
    Conversion.Conv env (dataHypothesisTelescope params fields offset recursive proof motive body)
      (dataHypothesisTelescope params fields offset recursive proof motive' body') := by
  induction recursive generalizing offset with
  | nil => exact hb
  | cons pair recursive ih =>
      simp only [dataHypothesisTelescope,List.zipIdx_cons,List.foldr_cons]
      exact .node (.pi proof) (.cons (dataHypothesisType_motive_congr closed hm) (.cons (ih (offset + 1)) .nil))

theorem dataCaseResult_motive_congr (closed : Conversion.Closed env) (h : Conversion.Conv env motive motive') :
    Conversion.Conv env (dataCaseResult family constructor params fields hypotheses ps motive indices)
      (dataCaseResult family constructor params fields hypotheses ps motive' indices) :=
  .node .app (.cons (applications_motive_congr (h.renaming _ closed) _) (.cons (.refl _) .nil))

theorem dataCaseType_motive_congr (closed : Conversion.Closed env) (h : Conversion.Conv env motive motive')
    (generated : dataCaseType family constructor params depth signature ps motive recursion proof = some type) :
    ∃ type', dataCaseType family constructor params depth signature ps motive' recursion proof = some type' ∧
      Conversion.Conv env type type' := by
  unfold dataCaseType at generated ⊢
  split at generated
  · contradiction
  · rename_i valid
    simp only [valid,ite_false]
    cases generated
    exact ⟨_,rfl,closeDataFields_congr
      (dataHypothesisTelescope_congr closed h (dataCaseResult_motive_congr closed h) _ _) _⟩

private theorem mapM_relation {α : Type} (xs : List α) (f g : α → Option Term)
    (transports : ∀ x ∈ xs, ∀ value, f x = some value →
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

theorem dataCaseTypes_motive_congr (closed : Conversion.Closed env) (h : Conversion.Conv env motive motive')
    (generated : dataCaseTypes family params depth signatures ps motive recursion proof = some types) :
    ∃ types',dataCaseTypes family params depth signatures ps motive' recursion proof = some types' ∧
      Conversion.ListRel (Conversion.Conv env) types types' := by
  unfold dataCaseTypes at generated ⊢
  apply mapM_relation _ _ _ _ generated
  intro pair _ value found
  exact dataCaseType_motive_congr closed h found

end Jihoo.NativeKernel.Environment
