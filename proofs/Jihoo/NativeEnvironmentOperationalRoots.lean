import Jihoo.NativeEnvironmentTyping

/-! Further native pure value equations and preservation at the original type.
These roots follow Core.normal and the Strict equation in Core.identical.
They are deliberately separate from ACU.Conv: no contextual conversion or
confluence theorem for the enlarged relation is assumed here. -/
namespace Jihoo.NativeKernel.Environment.ValueReduction

def arithmetic (op : Arith) (a b : Int) : Int :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b

def signed64 (n : Int) : Prop := -(2^63 : Int) ≤ n ∧ n < (2^63 : Int)

instance (n : Int) : Decidable (signed64 n) := inferInstanceAs (Decidable (_ ∧ _))

/-- Pure conversion may discard Strict's first value even when runtime
evaluation must retain its traps. Memory Free is erased only in the pure model.
Fold/Loop reduce only at zero; no changing-bound recursive unrolling is used. -/
inductive Root : Term → Term → Prop where
  | arithmetic (op : Arith) (a b : Int) : signed64 (arithmetic op a b) →
      Root (.arith op (.integer a) (.integer b)) (.integer (arithmetic op a b))
  | strict (first rest : Term) : Root (.strict first rest) rest
  | free (buffer rest : Term) : Root (.free buffer rest) rest
  | foldZero (init body : Term) : Root (.fold (.natural 0) init body) init
  | loopZero (motive init body : Term) : Root (.loop (.natural 0) motive init body) init

private def View (env : Environment) (ctx : Context) (mode : Bool) : Term → Term → Prop
  | .arith _ _ _, T => Conversion.Conv .i64 T
  | .strict _ rest, T | .free _ rest, T | .fold _ rest _, T =>
      ∃ A, HasType env ctx mode rest A ∧ Conversion.Conv A T
  | .loop n motive init _, T =>
      ∃ proof : Bool, HasType env ctx (mode || proof) init (.app motive (.natural 0)) ∧
        Conversion.Conv (.app motive n) T
  | _, _ => True

private theorem View.convert (view : View env ctx mode term A) (converted : Conversion.Conv A B) :
    View env ctx mode term B := by
  fun_cases View env ctx mode term A <;> simp only [View] at view ⊢
  all_goals first
    | exact view.trans converted
    | obtain ⟨type, typed, result⟩ := view; exact ⟨type, typed, result.trans converted⟩
    | trivial

private theorem view (typed : HasType env ctx mode term type) : View env ctx mode term type := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun ctx mode term type _ => View env ctx mode term type)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case arith => exact .refl _
  case strict => exact ⟨_, by assumption, .refl _⟩
  case free => exact ⟨_, by assumption, .refl _⟩
  case foldI64 => exact ⟨_, by assumption, .refl _⟩
  case loop => exact ⟨_, by assumption, .refl _⟩
  case convert => exact View.convert (by assumption) (by assumption)

theorem Root.preserves (step : Root term result) (typed : HasType env ctx true term type) :
    HasType env ctx true result type := by
  have inspected := view typed
  cases step with
  | arithmetic op a b bound =>
      exact .convert (.integer bound.1 bound.2) inspected
  | strict | free | foldZero =>
      obtain ⟨_, value, converted⟩ := inspected
      exact .convert value converted
  | loopZero =>
      obtain ⟨proof, value, converted⟩ := inspected
      exact .convert (by simpa only [Bool.true_or] using value) converted

theorem Root.renaming (step : Root term result) (ρ : Nat → Nat) :
    Root (term.rename ρ) (result.rename ρ) := by
  cases step <;> simp only [Term.rename, renameArgs, Op.binders, liftRenaming]
  all_goals first
    | exact .arithmetic _ _ _ (by assumption)
    | exact .strict _ _
    | exact .free _ _
    | exact .foldZero _ _
    | exact .loopZero _ _ _

theorem Root.substitution (step : Root term result) (σ : Nat → Term) :
    Root (term.subst σ) (result.subst σ) := by
  cases step <;> simp only [Term.subst, substArgs, Op.binders, liftSub]
  all_goals first
    | exact .arithmetic _ _ _ (by assumption)
    | exact .strict _ _
    | exact .free _ _
    | exact .foldZero _ _
    | exact .loopZero _ _ _

/-- This adapter contracts the stated pure equations. It is not a replacement
for Core.normal or the bounded ACU normalizer. Overflow remains uncontracted. -/
def contract : Term → Option Term
  | .arith op (.integer a) (.integer b) =>
      if signed64 (arithmetic op a b) then some (.integer (arithmetic op a b)) else none
  | .strict _ rest | .free _ rest | .fold (.natural 0) rest _ | .loop (.natural 0) _ rest _ => some rest
  | _ => none

theorem contract_sound (accepted : contract term = some result) : Root term result := by
  fun_cases contract term <;> simp_all [contract]
  all_goals try (subst result)
  all_goals first
    | exact .arithmetic _ _ _ (by assumption)
    | exact .strict _ _
    | exact .free _ _
    | exact .foldZero _ _
    | exact .loopZero _ _ _

theorem contract_preserves (accepted : contract term = some result)
    (typed : HasType env ctx true term type) : HasType env ctx true result type :=
  (contract_sound accepted).preserves typed

inductive Steps : Term → Term → Prop where
  | refl : Steps term term
  | next : Root term middle → Steps middle result → Steps term result

theorem Steps.trans (first : Steps a b) (second : Steps b c) : Steps a c := by
  induction first with
  | refl => exact second
  | next step rest ih => exact .next step (ih second)

theorem Steps.preserves (steps : Steps term result) (typed : HasType env ctx true term type) :
    HasType env ctx true result type := by
  induction steps with
  | refl => exact typed
  | next step rest ih => exact ih (step.preserves typed)

theorem Root.size_decreases (step : Root term result) :
    Conversion.treeSize result < Conversion.treeSize term := by
  change Jihoo.NativeKernel.Conversion.treeSize result < Jihoo.NativeKernel.Conversion.treeSize term
  cases step <;> simp [Jihoo.NativeKernel.Conversion.treeSize] <;> omega

def run : Nat → Term → Term
  | 0, term => term
  | fuel + 1, term => match contract term with
      | none => term
      | some next => run fuel next

theorem run_steps (fuel : Nat) (term : Term) : Steps term (run fuel term) := by
  induction fuel generalizing term with
  | zero => exact .refl
  | succ fuel ih =>
      simp only [run]
      cases accepted : contract term with
      | none => exact .refl
      | some next => exact .next (contract_sound accepted) (ih next)

theorem run_preserves (fuel : Nat) (typed : HasType env ctx true term type) :
    HasType env ctx true (run fuel term) type := (run_steps fuel term).preserves typed

theorem run_size (fuel : Nat) (term : Term) : Conversion.treeSize (run fuel term) ≤ Conversion.treeSize term := by
  induction fuel generalizing term with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      simp only [run]
      cases accepted : contract term with
      | none => exact Nat.le_refl _
      | some next => exact Nat.le_trans (ih next) (Nat.le_of_lt (contract_sound accepted).size_decreases)

theorem run_eventually_stops (fuel : Nat) (enough : Conversion.treeSize term ≤ fuel) :
    contract (run fuel term) = none := by
  induction fuel generalizing term with
  | zero =>
      cases term <;> simp [Jihoo.NativeKernel.Conversion.treeSize] at enough
  | succ fuel ih =>
      simp only [run]
      cases accepted : contract term with
      | none => exact accepted
      | some next =>
          apply ih
          have decreases := (contract_sound accepted).size_decreases
          omega

theorem overflow_remains (rejected : ¬signed64 (arithmetic op a b)) :
    contract (.arith op (.integer a) (.integer b)) = none := by
  simp [contract, rejected]

namespace Examples

theorem signed_upper_boundary :
    contract (.arith .add (.integer ((2^63 : Int) - 2)) (.integer 1)) =
      some (.integer ((2^63 : Int) - 1)) := by cbv

theorem signed_lower_boundary :
    contract (.arith .sub (.integer (-(2^63 : Int) + 1)) (.integer 1)) =
      some (.integer (-(2^63 : Int))) := by cbv

theorem positive_overflow_kept :
    contract (.arith .add (.integer ((2^63 : Int) - 1)) (.integer 1)) = none := by decide

theorem negative_overflow_kept :
    contract (.arith .sub (.integer (-(2^63 : Int))) (.integer 1)) = none := by decide

theorem multiplication_overflow_kept :
    contract (.arith .mul (.integer ((2^63 : Int) - 1)) (.integer 2)) = none := by decide

theorem empty_fold_does_not_visit_body :
    run 1 (.fold (.natural 0) (.integer 9)
      (.arith .mul (.integer ((2^63 : Int) - 1)) (.integer 2))) = .integer 9 := rfl

theorem free_then_arithmetic :
    run 2 (.free (.alloc (.natural 2) (.integer 0))
      (.arith .add (.integer 20) (.integer 22))) = .integer 42 := by cbv

end Examples

end Jihoo.NativeKernel.Environment.ValueReduction
