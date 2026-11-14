import Jihoo.NativeDependentFormulaSemantics

/-! Actual source typing is sufficient for contextual dependent proof
interpretation on a syntax-recognized Refl/Lam/App fragment. Raw result types
are interpreted by conversion saturation, including unformed representatives.
The theorem constructs the semantic proof; none is supplied by its caller. -/
namespace Jihoo.NativeKernel.Environment.Semantics.Dependent
open Jihoo.NativeKernel.Environment.Conversion

def context : Nat → Context
  | 0 => []
  | depth+1 => ⟨.u64,false⟩ :: context depth

def Index.Valid (depth : Nat) : Index → Prop
  | .var position => position < depth
  | .natural value => value < 2^64

theorem lookup_context (bound : position < depth) :
    NativeKernel.lookup (context depth) position = some ⟨.u64,false⟩ := by
  induction depth generalizing position with
  | zero => omega
  | succ depth ih =>
    cases position with
    | zero => simp only [context,NativeKernel.lookup,Term.u64,Term.rename,renameArgs]
    | succ position =>
      change (NativeKernel.lookup (context depth) position).map _ = _
      rw [ih (by omega)]
      simp only [Option.map,Term.u64,Term.rename,renameArgs]

theorem lookup_context_bound (found : NativeKernel.lookup (context depth) position = some binding) : position < depth := by
  induction depth generalizing position binding with
  | zero => simp only [context,NativeKernel.lookup,reduceCtorEq] at found
  | succ depth ih =>
    cases position with
    | zero => omega
    | succ position =>
      change (NativeKernel.lookup (context depth) position).map _ = some binding at found
      cases previous : NativeKernel.lookup (context depth) position with
      | none => simp only [previous,Option.map,reduceCtorEq] at found
      | some prior => exact Nat.succ_lt_succ (ih previous)

theorem Index.typed (value : Index) (valid : value.Valid depth) :
    HasType env (context depth) mode value.syntax .u64 := by
  cases value with
  | var position => exact .var (lookup_context valid) (Or.inr rfl)
  | natural value => exact .natural valid

theorem Index.valid_of_typed (value : Index)
    (typed : HasType env (context depth) mode value.syntax type) : value.Valid depth := by
  cases value with
  | var position =>
    obtain ⟨binding,found,converted⟩ := typed.principalView
    exact lookup_context_bound found
  | natural value => exact typed.naturalView.1

inductive Expression : Nat → Formula → Type where
  | refl (value : Index) (valid : value.Valid depth) : Expression depth (.equal value value)
  | lam : Expression (depth+1) body → Expression depth (.all body)
  | app : Expression depth (.all body) → (argument : Index) → argument.Valid depth →
      Expression depth (body.subst (singleIndex argument))

def Expression.syntax : Expression depth formula → Term
  | .refl value _ => .refl value.syntax
  | .lam body => .lam false .u64 body.syntax
  | .app function argument _ => .app function.syntax argument.syntax

theorem Expression.typed (expression : Expression depth formula) :
    HasType env (context depth) true expression.syntax formula.syntax := by
  induction expression with
  | refl value valid => exact .refl (value.typed valid)
  | lam body ih =>
    exact .lam (.intro (s := .type 0) HasType.u64
      (Or.inl (by change SortTag.type 0 ≠ SortTag.prop; intro h; cases h))) ih
  | @app depth body function argument valid ih =>
    change HasType env (context depth) true (.app function.syntax argument.syntax)
      (body.subst (singleIndex argument)).syntax
    rw [Formula.instantiate_syntax]
    exact HasType.app (B := body.syntax) ih (argument.typed (mode := true) valid) (Or.inl rfl)

/-- Dependent lambda/application are interpreted as actual host proof functions.
The quantified argument is any natural, with no numeric-observation premise. -/
theorem Expression.fundamental (expression : Expression depth formula) :
    ∀ assignment, formula.truth assignment := by
  induction expression with
  | refl => intro assignment; rfl
  | lam body ih => intro assignment value; exact ih (extend assignment value)
  | app function argument valid ih =>
    intro assignment
    rw [Formula.instantiate_truth]
    exact ih assignment (argument.meaning assignment)

def Expression.interpret (expression : Expression depth formula) (assignment : Nat → Nat) :
    Finite.Carrier (formula.code assignment) := ⟨⟨expression.fundamental assignment⟩⟩

/-- Source recognition contains syntax only; in particular the Refl index
need not be in scope or bounded until actual HasType establishes those facts. -/
inductive Recognized : Term → Prop where
  | refl (value : Index) : Recognized (.refl value.syntax)
  | lam : Recognized body → Recognized (.lam false .u64 body)
  | app (argument : Index) : Recognized function → Recognized (.app function argument.syntax)

theorem recognized_principal (wf : UnifiedProgram.EnvWellFormed env) (recognized : Recognized term)
    (typed : HasType env (context depth) mode term type) :
    ∃ formula, ∃ expression : Expression depth formula,
      expression.syntax = term ∧ Conv env formula.syntax type := by
  induction recognized generalizing depth mode type with
  | refl value =>
    obtain ⟨indexTyped,converted⟩ := typed.reflView
    exact ⟨.equal value value,.refl value (value.valid_of_typed indexTyped),rfl,converted⟩
  | @lam body recognized ih =>
    obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
    obtain ⟨formula,expression,erased,bodyConversion⟩ := ih (depth := depth+1) bodyTyped
    refine ⟨.all formula,.lam expression,?_,?_⟩
    · simp only [Expression.syntax,erased]
    · exact .trans (.node (.pi false) (.cons (.refl _) (.cons bodyConversion .nil))) converted
  | @app function argument recognized ih =>
    obtain ⟨erased,domain,codomain,functionTyped,argumentTyped,allowed,resultConversion⟩ := typed.appView
    obtain ⟨formula,expression,erasedSource,functionConversion⟩ := ih functionTyped
    cases formula with
    | equal a b =>
      exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint
        (op := .eq) (op' := .pi erased) rfl rfl (by intro h; cases h) functionConversion wf.admissible)
    | less a b =>
      exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint
        (op := .lt) (op' := .pi erased) rfl rfl (by intro h; cases h) functionConversion wf.admissible)
    | all body =>
      have components := functionConversion.pi_injective wf.admissible
      refine ⟨body.subst (singleIndex argument),.app expression argument (argument.valid_of_typed argumentTyped),?_,?_⟩
      · simp only [Expression.syntax,erasedSource]
      · rw [Formula.instantiate_syntax]
        exact .trans (components.2.2.substitution (single argument.syntax) wf.closed) resultConversion

/-- Raw result types denote proposition families through their actual
conversion class, rather than an unjustified raw-type formation premise. -/
def FamilyTruth (env : Environment) (type : Term) (assignment : Nat → Nat) : Prop :=
  ∃ formula : Formula, Conv env formula.syntax type ∧ formula.truth assignment

theorem FamilyTruth.conversion (converted : Conv env type replacement) :
    FamilyTruth env type assignment ↔ FamilyTruth env replacement assignment := by
  constructor
  · rintro ⟨formula,original,truth⟩; exact ⟨formula,.trans original converted,truth⟩
  · rintro ⟨formula,original,truth⟩; exact ⟨formula,.trans original (.symm converted),truth⟩

theorem FamilyTruth.formula_iff (wf : UnifiedProgram.EnvWellFormed env) (formula : Formula) :
    FamilyTruth env formula.syntax assignment ↔ formula.truth assignment := by
  constructor
  · rintro ⟨other,converted,truth⟩
    exact (Formula.conversion_truth wf other formula converted assignment).mp truth
  · intro truth; exact ⟨formula,.refl _,truth⟩

/-- This fundamental theorem takes actual source typing and syntax recognition;
semantic proof membership and normalization are outputs, never assumptions. -/
theorem native_fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env (context depth) mode term type) (recognized : Recognized term) :
    ∀ assignment, FamilyTruth env type assignment := by
  obtain ⟨formula,expression,erased,converted⟩ := recognized_principal wf recognized typed
  intro assignment
  exact ⟨formula,converted,expression.fundamental assignment⟩

theorem checked_fundamental (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env (context depth) mode term type) (recognized : Recognized term) :
    ∀ assignment, FamilyTruth env type assignment := native_fundamental history.wellFormed typed recognized

theorem no_recognized_false_equality (wf : UnifiedProgram.EnvWellFormed env) (different : m ≠ n)
    (typed : HasType env [] mode term (.eq (.natural m) (.natural n))) (recognized : Recognized term) : False := by
  have truth := native_fundamental (depth := 0) wf typed recognized (fun _ => 0)
  exact different ((FamilyTruth.formula_iff wf (.equal (.natural m) (.natural n))).mp truth)

theorem no_recognized_false_less (wf : UnifiedProgram.EnvWellFormed env) (unordered : ¬ m < n)
    (typed : HasType env [] mode term (.lt (.natural m) (.natural n))) (recognized : Recognized term) : False := by
  have truth := native_fundamental (depth := 0) wf typed recognized (fun _ => 0)
  exact unordered ((FamilyTruth.formula_iff wf (.less (.natural m) (.natural n))).mp truth)

end Jihoo.NativeKernel.Environment.Semantics.Dependent
