import Jihoo.NativeFunctionInterpretation

/-! Coverage of actual HasType in the U64/function source fragment. Recognition
is syntax only; it does not contain a typing, realization, or normalization
certificate. Arbitrary result conversions are interpreted through saturation.
This is a contextual fragment theorem, not yet the full dependent/universe
fundamental lemma for every native term. -/
namespace Jihoo.NativeKernel.Environment.Semantics.Functions
open Jihoo.NativeKernel.Environment.Conversion

inductive Recognized : Term → Prop where
  | var : Recognized (.var index)
  | natural : Recognized (.natural value)
  | lam (domain : SimpleType) : Recognized body → Recognized (.lam false domain.syntax body)
  | app : Recognized function → Recognized argument → Recognized (.app function argument)

theorem SimpleType.syntax_injective {A B : SimpleType} (wf : UnifiedProgram.EnvWellFormed env)
    (converted : Conv env A.syntax B.syntax) : A = B := by
  induction A generalizing B with
  | natural =>
    cases B with
    | natural => rfl
    | arrow B C =>
      exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint
        (op := .u64) (op' := .pi false) rfl rfl (by intro h; cases h) converted wf.admissible)
  | arrow A C ha hc =>
    cases B with
    | natural =>
      exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint
        (op := .pi false) (op' := .u64) rfl rfl (by intro h; cases h) converted wf.admissible)
    | arrow B D =>
      have parts := converted.pi_injective wf.admissible
      cases ha parts.2.1
      cases hc parts.2.2
      rfl

theorem lookup_context (Γ : List SimpleType) (index : Nat) :
    NativeKernel.lookup (context Γ) index = (Γ[index]?).map (fun A => ⟨A.syntax,false⟩) := by
  induction Γ generalizing index with
  | nil => rfl
  | cons A Γ ih =>
    cases index with
    | zero => simp only [context,List.map,NativeKernel.lookup,SimpleType.syntax_rename,List.getElem?_cons_zero,Option.map]
    | succ index =>
      change (NativeKernel.lookup (context Γ) index).map _ = (Γ[index]?).map _
      rw [ih]
      cases Γ[index]? <;> simp only [Option.map,SimpleType.syntax_rename]

def Member.ofLookup {Γ : List SimpleType} {index : Nat} {A : SimpleType} (found : Γ[index]? = some A) : Member A Γ index :=
  match Γ,index with
  | [],_ => by simp at found
  | B :: _,0 => by simp only [List.getElem?_cons_zero,Option.some.injEq] at found; cases found; exact .here
  | _ :: Γ,index+1 => .there (Member.ofLookup (Γ := Γ) (by simpa only [List.getElem?_cons_succ] using found))

/-- Actual typing reconstructs an intrinsic expression from recognized syntax.
The result type may be an unformed raw representative; only its conversion
class is used, so this theorem assumes no false regularity principle. -/
theorem recognized_principal (wf : UnifiedProgram.EnvWellFormed env)
    (recognized : Recognized term) (typed : HasType env (context Γ) mode term T) :
    ∃ A, ∃ expression : Expression Γ A, expression.syntax = term ∧ Conv env A.syntax T := by
  induction recognized generalizing Γ mode T with
  | @var index =>
    obtain ⟨binding,found,converted⟩ := typed.principalView
    rw [lookup_context] at found
    cases original : Γ[index]? with
    | none => simp [original] at found
    | some A =>
      simp only [original,Option.map,Option.some.injEq] at found
      cases found
      exact ⟨A,.var (.ofLookup original),rfl,converted⟩
  | @natural value =>
    obtain ⟨bound,converted⟩ := typed.naturalView
    exact ⟨.natural,.natural value bound,rfl,converted⟩
  | @lam body domain recognized ih =>
    obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
    obtain ⟨B,bodyExpression,erased,bodyConversion⟩ := ih (Γ := domain :: Γ) bodyTyped
    refine ⟨.arrow domain B,.lam bodyExpression,?_,?_⟩
    · simp only [Expression.syntax,erased]
    · exact .trans (.node (.pi false) (.cons (.refl _) (.cons bodyConversion .nil))) converted
  | @app function argument recognizedFunction recognizedArgument ihf iha =>
    obtain ⟨erased,domain,codomain,functionTyped,argumentTyped,allowed,resultConverted⟩ := typed.appView
    obtain ⟨F,functionExpression,functionErasure,functionConverted⟩ := ihf functionTyped
    cases F with
    | natural =>
      exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint
        (op := .u64) (op' := .pi erased) rfl rfl (by intro h; cases h) functionConverted wf.admissible)
    | arrow A B =>
      have components := functionConverted.pi_injective wf.admissible
      obtain ⟨C,argumentExpression,argumentErasure,argumentConverted⟩ := iha argumentTyped
      have same : C = A := SimpleType.syntax_injective wf (.trans argumentConverted (.symm components.2.1))
      subst C
      refine ⟨B,.app functionExpression argumentExpression,?_,?_⟩
      · simp only [Expression.syntax,functionErasure,argumentErasure]
      · have result := components.2.2.substitution (single argument) wf.closed
        rw [SimpleType.syntax_subst] at result
        exact .trans result resultConverted

/-- A contextual fundamental theorem with actual source typing as input.
Realization of the source itself is constructed, never supplied by the caller. -/
theorem native_fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env (context Γ) mode term T) (recognized : Recognized term)
    (substitution : SubstitutionRealizes env Γ σ values) :
    ∃ A, ∃ expression : Expression Γ A,
      expression.syntax = term ∧ Conv env A.syntax T ∧
      Realizes env A (term.subst σ) (expression.meaning values) := by
  obtain ⟨A,expression,erased,converted⟩ := recognized_principal wf recognized typed
  exact ⟨A,expression,erased,converted,erased ▸ expression.fundamental substitution⟩

theorem closed_native_fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env [] mode term T) (recognized : Recognized term) :
    ∃ A, ∃ expression : Expression [] A,
      expression.syntax = term ∧ Conv env A.syntax T ∧ Realizes env A term (expression.meaning .nil) := by
  obtain ⟨A,expression,erased,converted,realized⟩ := native_fundamental (Γ := []) wf typed recognized empty_substitution_realizes
  exact ⟨A,expression,erased,converted,by simpa only [Term.subst_id] using realized⟩

theorem closed_natural_canonicity (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env [] mode term .u64) (recognized : Recognized term) :
    ∃ value, value < 2^64 ∧ Conv env term (.natural value) := by
  obtain ⟨A,expression,erased,converted,realized⟩ := closed_native_fundamental wf typed recognized
  have same : A = .natural := SimpleType.syntax_injective wf converted
  subst A
  exact ⟨_,realized⟩

end Jihoo.NativeKernel.Environment.Semantics.Functions
