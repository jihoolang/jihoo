import Jihoo.NativeFunctionFundamental
set_option maxUniverseOffset 40

/-! Concrete dependent proposition families and conversion coherence. Index
assignments range over every natural number; no canonicity of arbitrary native
U64 terms is assumed. Actual checked-world closedness permits substitution in
delta conversion, and admissibility supplies the proved rigid injectivity. -/
namespace Jihoo.NativeKernel.Environment.Semantics.Dependent
open Jihoo.NativeKernel.Environment.Conversion

inductive Index where
  | var (position : Nat)
  | natural (value : Nat)
  deriving DecidableEq, Repr

def Index.syntax : Index → Term
  | .var position => .var position
  | .natural value => .natural value

def Index.meaning (assignment : Nat → Nat) : Index → Nat
  | .var position => assignment position
  | .natural value => value

def Index.rename (ρ : Nat → Nat) : Index → Index
  | .var position => .var (ρ position)
  | .natural value => .natural value

def Index.subst (σ : Nat → Index) : Index → Index
  | .var position => σ position
  | .natural value => .natural value

def extend (assignment : Nat → α) (value : α) : Nat → α
  | 0 => value
  | n+1 => assignment n

def lift (σ : Nat → Index) : Nat → Index
  | 0 => .var 0
  | n+1 => (σ n).rename Nat.succ

def singleIndex (value : Index) : Nat → Index := extend Index.var value

theorem Index.syntax_rename (value : Index) (ρ : Nat → Nat) :
    (value.rename ρ).syntax = value.syntax.rename ρ := by
  cases value <;> simp only [Index.rename,Index.syntax,Term.rename,Term.natural,renameArgs]

theorem Index.syntax_subst (value : Index) (σ : Nat → Index) :
    (value.subst σ).syntax = value.syntax.subst (fun i => (σ i).syntax) := by
  cases value <;> simp only [Index.subst,Index.syntax,Term.subst,Term.natural,substArgs]

theorem Index.meaning_rename (value : Index) (ρ : Nat → Nat) (assignment : Nat → Nat) :
    (value.rename ρ).meaning assignment = value.meaning (assignment ∘ ρ) := by
  cases value <;> rfl

theorem Index.meaning_subst (value : Index) (σ : Nat → Index) (assignment : Nat → Nat) :
    (value.subst σ).meaning assignment = value.meaning (fun i => (σ i).meaning assignment) := by
  cases value <;> rfl

theorem lift_syntax (σ : Nat → Index) :
    (fun i => (lift σ i).syntax) = liftSub 1 (fun i => (σ i).syntax) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact Index.syntax_rename _ _

inductive Formula where
  | equal (left right : Index)
  | less (left right : Index)
  | all (body : Formula)
  deriving DecidableEq, Repr

def Formula.syntax : Formula → Term
  | .equal left right => .eq left.syntax right.syntax
  | .less left right => .lt left.syntax right.syntax
  | .all body => .pi false .u64 body.syntax

def Formula.truth (assignment : Nat → Nat) : Formula → Prop
  | .equal left right => left.meaning assignment = right.meaning assignment
  | .less left right => left.meaning assignment < right.meaning assignment
  | .all body => ∀ value, body.truth (extend assignment value)

def Formula.code (assignment : Nat → Nat) (formula : Formula) : Finite.Universe .proposition :=
  .proposition (formula.truth assignment)

def Formula.subst (σ : Nat → Index) : Formula → Formula
  | .equal left right => .equal (left.subst σ) (right.subst σ)
  | .less left right => .less (left.subst σ) (right.subst σ)
  | .all body => .all (body.subst (lift σ))

theorem Formula.syntax_subst (formula : Formula) (σ : Nat → Index) :
    (formula.subst σ).syntax = formula.syntax.subst (fun i => (σ i).syntax) := by
  induction formula generalizing σ with
  | equal left right =>
    simp only [Formula.subst,Formula.syntax,Term.eq,Term.subst,substArgs,Op.binders,liftSub,
      Index.syntax_subst]
  | less left right =>
    simp only [Formula.subst,Formula.syntax,Term.lt,Term.subst,substArgs,Op.binders,liftSub,
      Index.syntax_subst]
  | all body ih =>
    simp only [Formula.subst,Formula.syntax,Term.pi,Term.u64,Term.subst,substArgs,Op.binders,liftSub]
    rw [ih,lift_syntax]
    rfl

theorem lift_meaning (σ : Nat → Index) (assignment : Nat → Nat) (value : Nat) :
    (fun i => (lift σ i).meaning (extend assignment value)) =
      extend (fun i => (σ i).meaning assignment) value := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    simp only [lift,Index.meaning_rename]
    rfl

theorem Formula.truth_subst (formula : Formula) (σ : Nat → Index) (assignment : Nat → Nat) :
    (formula.subst σ).truth assignment = formula.truth (fun i => (σ i).meaning assignment) := by
  induction formula generalizing σ assignment with
  | equal left right => simp only [Formula.subst,Formula.truth,Index.meaning_subst]
  | less left right => simp only [Formula.subst,Formula.truth,Index.meaning_subst]
  | all body ih =>
    simp only [Formula.subst,Formula.truth]
    apply congrArg (fun predicate : Nat → Prop => ∀ value, predicate value)
    funext value
    rw [ih,lift_meaning]

theorem singleIndex_syntax (argument : Index) :
    (fun i => (singleIndex argument i).syntax) = single argument.syntax := by
  funext i
  cases i <;> rfl

theorem singleIndex_meaning (argument : Index) (assignment : Nat → Nat) :
    (fun i => (singleIndex argument i).meaning assignment) = extend assignment (argument.meaning assignment) := by
  funext i
  cases i <;> rfl

theorem Formula.instantiate_syntax (formula : Formula) (argument : Index) :
    (formula.subst (singleIndex argument)).syntax = formula.syntax.subst (single argument.syntax) := by
  rw [Formula.syntax_subst,singleIndex_syntax]

theorem Formula.instantiate_truth (formula : Formula) (argument : Index) (assignment : Nat → Nat) :
    (formula.subst (singleIndex argument)).truth assignment =
      formula.truth (extend assignment (argument.meaning assignment)) := by
  rw [Formula.truth_subst,singleIndex_meaning]

theorem Formula.code_all (body : Formula) (assignment : Nat → Nat) :
    (Formula.all body).code assignment =
      Finite.pi Finite.natural .proposition (fun value => body.code (extend assignment value.down)) := by
  change Finite.Universe.proposition (∀ value,body.truth (extend assignment value)) =
    Finite.Universe.proposition (∀ value : ULift.{34} Nat,body.truth (extend assignment value.down))
  apply congrArg Finite.Universe.proposition
  apply propext
  constructor
  · exact fun proof value => proof value.down
  · exact fun proof value => proof ⟨value⟩

theorem Index.closed_value (value : Index) (assignment : Nat → Nat) :
    value.syntax.subst (fun i => .natural (assignment i)) = .natural (value.meaning assignment) := by
  cases value <;> simp only [Index.syntax,Index.meaning,Term.subst,Term.natural,substArgs]

theorem Index.conversion_meaning {left right : Index} (wf : UnifiedProgram.EnvWellFormed env)
    (converted : Conv env left.syntax right.syntax) (assignment : Nat → Nat) :
    left.meaning assignment = right.meaning assignment := by
  have closed := converted.substitution (fun i => .natural (assignment i)) wf.closed
  rw [Index.closed_value,Index.closed_value] at closed
  exact closed.natural_injective wf.admissible

/-- Type-family coherence follows from actual conversion constructors and the
checked world's proved shape theorems, not from a semantic equality oracle. -/
theorem Formula.conversion_truth (wf : UnifiedProgram.EnvWellFormed env)
    (left right : Formula) (converted : Conv env left.syntax right.syntax) (assignment : Nat → Nat) :
    left.truth assignment ↔ right.truth assignment := by
  induction left generalizing right assignment with
  | equal a b =>
    cases right with
    | equal c d =>
      have parts := converted.eq_injective wf.admissible
      simp only [Formula.truth,Index.conversion_meaning wf parts.1 assignment,
        Index.conversion_meaning wf parts.2 assignment]
    | less c d => exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint
        (op := .eq) (op' := .lt) rfl rfl (by intro h; cases h) converted wf.admissible)
    | all body => exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint
        (op := .eq) (op' := .pi false) rfl rfl (by intro h; cases h) converted wf.admissible)
  | less a b =>
    cases right with
    | equal c d => exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint
        (op := .lt) (op' := .eq) rfl rfl (by intro h; cases h) converted wf.admissible)
    | less c d =>
      have parts := converted.lt_injective wf.admissible
      simp only [Formula.truth,Index.conversion_meaning wf parts.1 assignment,
        Index.conversion_meaning wf parts.2 assignment]
    | all body => exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint
        (op := .lt) (op' := .pi false) rfl rfl (by intro h; cases h) converted wf.admissible)
  | all body ih =>
    cases right with
    | equal c d => exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint
        (op := .pi false) (op' := .eq) rfl rfl (by intro h; cases h) converted wf.admissible)
    | less c d => exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint
        (op := .pi false) (op' := .lt) rfl rfl (by intro h; cases h) converted wf.admissible)
    | all other =>
      have parts := converted.pi_injective wf.admissible
      exact forall_congr' (fun value => ih other parts.2.2 (extend assignment value))

end Jihoo.NativeKernel.Environment.Semantics.Dependent
