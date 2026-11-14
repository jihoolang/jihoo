import Jihoo.NativeEnvironmentTypeUniqueness
import Jihoo.NativeContextualUniverseModel

/-! A concrete contextual interpretation of the U64/function source fragment.
The logical relation is saturated under the actual environment-indexed
conversion. This file supplies no realization or normalization oracle. The
subsequent source-coverage theorem reconstructs this fragment from HasType.
Dependent codomains and universe-polymorphic terms remain separate obligations. -/
namespace Jihoo.NativeKernel.Environment.Semantics.Functions
open Jihoo.NativeKernel.Environment.Conversion

inductive SimpleType where
  | natural
  | arrow (domain codomain : SimpleType)
  deriving DecidableEq, Repr

def SimpleType.syntax : SimpleType → Term
  | .natural => .u64
  | .arrow A B => .pi false A.syntax B.syntax

@[reducible] def SimpleType.Meaning : SimpleType → Type
  | .natural => Nat
  | .arrow A B => A.Meaning → B.Meaning

def SimpleType.code (A : SimpleType) : Finite.Universe (.type ⟨0,by decide⟩) :=
  .type0 A.Meaning

theorem SimpleType.code_natural : SimpleType.code .natural = Finite.natural := rfl

theorem SimpleType.code_arrow (A B : SimpleType) :
    (SimpleType.arrow A B).code = Finite.pi A.code (.type ⟨0,by decide⟩) (fun _ => B.code) := rfl

theorem SimpleType.syntax_rename (A : SimpleType) (ρ : Nat → Nat) : A.syntax.rename ρ = A.syntax := by
  induction A generalizing ρ with
  | natural => simp only [SimpleType.syntax,Term.u64,Term.rename,renameArgs]
  | arrow A B ha hb =>
    simp only [SimpleType.syntax,Term.pi,Term.rename,renameArgs,Op.binders]
    rw [ha,hb]

theorem SimpleType.syntax_subst (A : SimpleType) (σ : Nat → Term) : A.syntax.subst σ = A.syntax := by
  induction A generalizing σ with
  | natural => simp only [SimpleType.syntax,Term.u64,Term.subst,substArgs]
  | arrow A B ha hb =>
    simp only [SimpleType.syntax,Term.pi,Term.subst,substArgs,Op.binders]
    rw [ha,hb]

theorem SimpleType.formed (A : SimpleType) : HasType env ctx mode A.syntax (.univ 0) := by
  induction A generalizing ctx mode with
  | natural => exact .u64
  | arrow A B ha hb =>
    exact .pi (e := false) (s := .type 0) (r := .type 0) (.intro (s := .type 0) (ha (mode := true)) (Or.inl (by change SortTag.type 0 ≠ SortTag.prop; intro h; cases h))) (hb (mode := true))

def context (Γ : List SimpleType) : Context := Γ.map fun A => ⟨A.syntax,false⟩

inductive Member : SimpleType → List SimpleType → Nat → Type where
  | here : Member A (A :: Γ) 0
  | there : Member A Γ i → Member A (B :: Γ) (i+1)

theorem Member.lookup (member : Member A Γ i) :
    NativeKernel.lookup (context Γ) i = some ⟨A.syntax,false⟩ := by
  induction member with
  | here => simp only [context,List.map,NativeKernel.lookup,SimpleType.syntax_rename]
  | there previous ih =>
    change (NativeKernel.lookup (context _) _).map _ = _
    rw [ih]
    simp only [Option.map,SimpleType.syntax_rename]

inductive Values : List SimpleType → Type where
  | nil : Values []
  | cons : A.Meaning → Values Γ → Values (A :: Γ)

def Member.value (member : Member A Γ i) (values : Values Γ) : A.Meaning :=
  match member, values with
  | .here, .cons first _ => first
  | .there previous, .cons _ rest => previous.value rest

inductive Expression : List SimpleType → SimpleType → Type where
  | var : Member A Γ i → Expression Γ A
  | natural (value : Nat) (bound : value < 2^64) : Expression Γ .natural
  | lam : Expression (A :: Γ) B → Expression Γ (.arrow A B)
  | app : Expression Γ (.arrow A B) → Expression Γ A → Expression Γ B

def Expression.syntax : Expression Γ A → Term
  | .var (i := i) _ => .var i
  | .natural value _ => .natural value
  | .lam (A := A) body => .lam false A.syntax body.syntax
  | .app function argument => .app function.syntax argument.syntax

def Expression.meaning : Expression Γ A → Values Γ → A.Meaning
  | .var member, values => member.value values
  | .natural value _, _ => value
  | .lam body, values => fun argument => body.meaning (.cons argument values)
  | .app function argument, values => function.meaning values (argument.meaning values)

theorem Expression.typed (expression : Expression Γ A) :
    HasType env (context Γ) true expression.syntax A.syntax := by
  induction expression with
  | var member => exact .var member.lookup (Or.inl rfl)
  | natural value bound => exact .natural bound
  | @lam A Γ B body ih =>
    exact .lam (.intro (s := .type 0) A.formed (Or.inl (by change SortTag.type 0 ≠ SortTag.prop; intro h; cases h))) ih
  | app function argument ihf iha =>
    simpa only [Expression.syntax,SimpleType.syntax_subst] using HasType.app ihf iha (Or.inl rfl)

/-- Native terms realize concrete host values. Function values quantify over
all realizable native arguments, including terms outside the source fragment. -/
def Realizes (env : Environment) : (A : SimpleType) → Term → A.Meaning → Prop
  | .natural, term, value => value < 2^64 ∧ Conv env term (.natural value)
  | .arrow A B, term, function =>
    ∀ argument value, Realizes env A argument value → Realizes env B (.app term argument) (function value)

theorem Realizes.conversion (converted : Conv env term replacement) (A : SimpleType) (value : A.Meaning) :
    Realizes env A term value ↔ Realizes env A replacement value := by
  induction A generalizing term replacement with
  | natural =>
    constructor
    · rintro ⟨bound,realized⟩; exact ⟨bound,.trans (.symm converted) realized⟩
    · rintro ⟨bound,realized⟩; exact ⟨bound,.trans converted realized⟩
  | arrow A B ha hb =>
    constructor <;> intro realizes argument argumentValue admitted
    · exact (hb (.node .app (.cons converted (.cons (.refl _) .nil))) _).mp (realizes argument argumentValue admitted)
    · exact (hb (.node .app (.cons converted (.cons (.refl _) .nil))) _).mpr (realizes argument argumentValue admitted)

def SubstitutionRealizes (env : Environment) (Γ : List SimpleType) (σ : Nat → Term) (values : Values Γ) : Prop :=
  ∀ {A i} (member : Member A Γ i), Realizes env A (σ i) (member.value values)

def extendSubstitution (σ : Nat → Term) (argument : Term) : Nat → Term
  | 0 => argument
  | n+1 => σ n

theorem SubstitutionRealizes.extend (substitution : SubstitutionRealizes env Γ σ values)
    (argument : Realizes env A term value) :
    SubstitutionRealizes env (A :: Γ) (extendSubstitution σ term) (.cons value values) := by
  intro B i member
  cases member with
  | here => exact argument
  | there previous => exact substitution previous

theorem lifted_substitution_instantiation (body : Term) (σ : Nat → Term) (argument : Term) :
    (body.subst (liftSub 1 σ)).subst (single argument) = body.subst (extendSubstitution σ argument) := by
  rw [Term.subst_comp]
  congr 1
  funext i
  cases i with
  | zero => simp only [liftSub,liftSubOne,Term.subst,NativeKernel.single,extendSubstitution]
  | succ i =>
    change ((σ i).rename Nat.succ).subst (single argument) = σ i
    exact Term.shift_subst_single _ _

/-- The contextual fundamental lemma is proved by the source expression;
neither membership of that expression nor its normalization is an input. -/
theorem Expression.fundamental (expression : Expression Γ A)
    (substitution : SubstitutionRealizes env Γ σ values) :
    Realizes env A (expression.syntax.subst σ) (expression.meaning values) := by
  induction expression generalizing σ with
  | var member => simpa only [Expression.syntax,Expression.meaning,Term.subst] using substitution member
  | natural value bound =>
    simpa only [Expression.syntax,Expression.meaning,Term.natural,Term.subst,substArgs] using (show Realizes env .natural (.natural value) value from ⟨bound,.refl _⟩)
  | @lam A Γ B body ih =>
    intro argument argumentValue admitted
    have realized := ih (SubstitutionRealizes.extend substitution admitted)
    have beta : Conv env (.app ((Term.lam false A.syntax body.syntax).subst σ) argument)
        (body.syntax.subst (extendSubstitution σ argument)) := by
      simp only [Term.lam,Term.subst,substArgs,Op.binders,SimpleType.syntax_subst]
      exact .trans (.legacy (.beta false A.syntax _ argument))
        (by rw [lifted_substitution_instantiation]; exact .refl _)
    exact (Realizes.conversion beta B _).mpr realized
  | app function argument ihf iha =>
    simpa only [Expression.syntax,Expression.meaning,Term.app,Term.subst,substArgs,Op.binders,liftSub] using ihf substitution _ _ (iha substitution)

theorem empty_substitution_realizes : SubstitutionRealizes env [] Term.var .nil := by
  intro A i member
  cases member

theorem Expression.closed_fundamental (expression : Expression [] A) :
    Realizes env A expression.syntax (expression.meaning .nil) := by
  simpa only [Term.subst_id] using expression.fundamental (env := env) empty_substitution_realizes

theorem Expression.closed_natural_conversion (expression : Expression [] .natural) :
    expression.meaning .nil < 2^64 ∧ Conv env expression.syntax (.natural (expression.meaning .nil)) :=
  expression.closed_fundamental

end Jihoo.NativeKernel.Environment.Semantics.Functions
