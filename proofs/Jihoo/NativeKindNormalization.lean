import Jihoo.NativeCodeKinds

/-! First-order kinds are fixed by actual forward delta/ACU normalization in
any environment. This is a computation-shape theorem, not checker completeness. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds
open Environment.Conversion

private theorem mixed_list_refl (terms : List Term) : ListRel ACU.MixedRed terms terms := by
  induction terms with
  | nil => exact .nil
  | cons term terms ih => exact .cons (.refl _) ih
private theorem mixed_list_trans (first : ListRel ACU.MixedRed xs ys) (second : ListRel ACU.MixedRed ys zs) :
    ListRel ACU.MixedRed xs zs := by
  induction first generalizing zs with
  | nil => cases second; exact .nil
  | cons first rest ih => cases second with | cons next tail => exact .cons (.trans first next) (ih tail)

private theorem mixed_of_arithmetic_list (kids : ListRel ACU.ArithmeticRed xs ys) : ListRel ACU.MixedRed xs ys := by
  induction kids with
  | nil => exact .nil
  | cons first rest ih => exact .cons (.arithmetic first) ih

/-- Actual forward reduction retains a rigid head syntactically, including its
child reduction derivations. This is stronger than conversion injectivity. -/
private theorem kind_mixed_rigid_shape (step : ACU.MixedRed input output) :
    ∀ {op xs}, ACU.fullRigid op = true → input = .node op xs →
    ∃ ys, output = .node op ys ∧ ListRel ACU.MixedRed xs ys := by
  induction step using ACU.MixedRed.rec (motive_2 := fun _ _ _ => True) with
  | refl term => intro op xs rigid equality; exact ⟨xs,equality,mixed_list_refl xs⟩
  | trans first second ihfirst ihsecond =>
    intro op xs rigid equality
    obtain ⟨ys,middle,firstKids⟩ := ihfirst rigid equality
    obtain ⟨zs,last,secondKids⟩ := ihsecond rigid middle
    exact ⟨zs,last,mixed_list_trans firstKids secondKids⟩
  | node op kids _ =>
    intro op' xs rigid equality
    cases equality
    exact ⟨_,rfl,kids⟩
  | arithmetic step =>
    intro op xs rigid equality
    obtain ⟨ys,last,kids⟩ := step.rigid_shape (Bool.and_eq_true_iff.mp rigid).2 equality
    exact ⟨ys,last,mixed_of_arithmetic_list kids⟩
  | compute step =>
    intro op xs rigid equality
    cases step <;> cases equality <;> contradiction
  | nil => trivial
  | cons => trivial

private theorem forward_list_refl (terms : List Term) : ListRel (EnvironmentDelta.Forward env) terms terms := by
  induction terms with
  | nil => exact .nil
  | cons term terms ih => exact .cons .refl ih

private theorem forward_list_trans (first : ListRel (EnvironmentDelta.Forward env) xs ys)
    (second : ListRel (EnvironmentDelta.Forward env) ys zs) : ListRel (EnvironmentDelta.Forward env) xs zs := by
  induction first generalizing zs with
  | nil => cases second; exact .nil
  | cons first rest ih => cases second with | cons next tail => exact .cons (.trans first next) (ih tail)

private theorem forward_of_mixed_list (kids : ListRel ACU.MixedRed xs ys) :
    ListRel (EnvironmentDelta.Forward env) xs ys := by
  induction kids with
  | nil => exact .nil
  | cons first rest ih => exact .cons (.acu first) ih

/-- Delta cannot contract a rigid non-global head; every retained child has an actual forward path. -/
private theorem kind_forward_rigid_shape (step : EnvironmentDelta.Forward env input output) :
    ∀ {op xs}, EnvironmentDelta.Basis.rigid op = true → input = .node op xs →
    ∃ ys, output = .node op ys ∧ ListRel (EnvironmentDelta.Forward env) xs ys := by
  induction step using EnvironmentDelta.Forward.rec (motive_2 := fun _ _ _ => True) with
  | refl => intro op xs rigid equality; exact ⟨xs,equality,forward_list_refl xs⟩
  | trans first second ihfirst ihsecond =>
      intro op xs rigid equality
      obtain ⟨ys,middle,firstKids⟩ := ihfirst rigid equality
      obtain ⟨zs,last,secondKids⟩ := ihsecond rigid middle
      exact ⟨zs,last,forward_list_trans firstKids secondKids⟩
  | node op kids _ =>
      intro op' xs rigid equality
      cases equality
      exact ⟨_,rfl,kids⟩
  | delta found =>
      intro op xs rigid equality
      cases equality
      simp [EnvironmentDelta.Basis.rigid,GlobalEnvironment.ordinary] at rigid
  | acu step =>
      intro op xs rigid equality
      obtain ⟨ys,last,kids⟩ := kind_mixed_rigid_shape step (Bool.and_eq_true_iff.mp rigid).2 equality
      exact ⟨ys,last,forward_of_mixed_list kids⟩
  | nil => trivial
  | cons => trivial


private theorem forward_u64_fixed (step : EnvironmentDelta.Forward env .u64 output) : output = .u64 := by
  obtain ⟨children, shape, changes⟩ := kind_forward_rigid_shape step rfl rfl
  cases changes
  exact shape

theorem Kind.forward_fixed (kind : Kind) (step : EnvironmentDelta.Forward env kind.term output) :
    output = kind.term := by
  induction kind generalizing output with
  | type level =>
      obtain ⟨children, shape, changes⟩ := kind_forward_rigid_shape step rfl rfl
      cases changes
      exact shape
  | index erased rest ih =>
      obtain ⟨children, shape, changes⟩ := kind_forward_rigid_shape step rfl rfl
      cases changes with
      | cons domainChange remaining =>
          cases remaining with
          | cons resultChange remaining =>
              cases remaining
              have domain := forward_u64_fixed domainChange
              have result := ih resultChange
              simpa only [domain,result,Kind.term] using shape

theorem Kind.normalize?_fixed (kind : Kind)
    (accepted : Conversion.normalize? env fuel kind.term = some output) : output = kind.term :=
  kind.forward_fixed (Conversion.normalize?_forward accepted)

theorem Kind.normalize_fixed (kind : Kind) : Conversion.normalize env fuel kind.term = kind.term := by
  change (Conversion.normalize? env fuel kind.term).getD kind.term = kind.term
  cases found : Conversion.normalize? env fuel kind.term with
  | none => rfl
  | some output => exact kind.normalize?_fixed found

end Jihoo.NativeKernel.Environment.CodeKinds
