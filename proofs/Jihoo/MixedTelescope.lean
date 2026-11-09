import Jihoo.Semantics

/-! Finite mixed telescopes for the Indexed calculus. Natural and proof variables
have separate de Bruijn namespaces. Proof types refer only to earlier naturals;
proofs never occur in indices. This is not the executable checker's judgment. -/
namespace Jihoo.Indexed.Mixed
open Arithmetic (Expr Env)

/-- Propositions, including universal quantification over mathematical naturals. -/
inductive Proposition : Ty → Prop where
  | lt : Proposition (.lt a b)
  | eq : Proposition (.eq a b)
  | all : Proposition A → Proposition (.pi A)

def Holds (A : Ty) (ρ : Env) : Prop := Nonempty (A.denote ρ)

theorem Proposition.subst (h : Proposition A) (σ : Substitution) :
    Proposition (A.subst σ) := by
  induction h generalizing σ with
  | lt => exact .lt
  | eq => exact .eq
  | all _ ih => exact .all (ih (lift σ))

/-- Oldest binder is constructed first. A proof binder does not increment the
natural namespace; a natural binder shifts every previous proof type. -/
inductive Telescope where
  | empty
  | natural : Telescope → Telescope
  | proof : Telescope → Ty → Telescope

def Telescope.naturals : Telescope → Nat
  | .empty => 0
  | .natural Γ => Γ.naturals + 1
  | .proof Γ _ => Γ.naturals

def Telescope.proofs : Telescope → List Ty
  | .empty => []
  | .natural Γ => Γ.proofs.map (fun A => A.subst shift)
  | .proof Γ A => A :: Γ.proofs

inductive WellFormed : Telescope → Prop where
  | empty : WellFormed .empty
  | natural : WellFormed Γ → WellFormed (.natural Γ)
  | proof : WellFormed Γ → Proposition A → A.Scoped Γ.naturals →
      WellFormed (.proof Γ A)

theorem WellFormed.scoped (h : WellFormed Γ) :
    ∀ A ∈ Γ.proofs, A.Scoped Γ.naturals := by
  induction h with
  | empty => simp [Telescope.proofs]
  | natural _ ih =>
      intro A ha
      obtain ⟨B, hb, rfl⟩ := List.mem_map.mp ha
      exact Ty.scoped_subst (ih B hb) scoped_shift
  | proof _ _ hs ih =>
      intro B hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hs
      · exact ih B hb

/-- Validity is built in telescope order, requiring truth only of assumptions,
never of a derived conclusion. Unused environment entries are immaterial. -/
inductive Valid : Telescope → Env → Prop where
  | empty (ρ) : Valid .empty ρ
  | natural : Valid Γ ρ → Valid (.natural Γ) (extendEnv ρ a)
  | proof : Valid Γ ρ → Holds A ρ → Valid (.proof Γ A) ρ

theorem Valid.valuation (h : Valid Γ ρ) : Valuation (complete Γ.proofs) ρ := by
  induction h with
  | empty => exact empty_valuation _
  | @natural Γ ρ a _ ih =>
      rw [Telescope.proofs, complete_subst]
      intro x
      rw [Context.subst, Ty.denote_shift]
      exact ih x
  | @proof Γ ρ A _ ha ih =>
      intro x
      cases x with
      | zero => exact ha
      | succ x => exact ih x

/-- Scope, proposition formation and typing are explicit, independent premises. -/
def Derives (Γ : Telescope) (t : Term) (A : Ty) : Prop :=
  WellFormed Γ ∧ Proposition A ∧ ScopedTyping Γ.naturals Γ.proofs t A

theorem Derives.sound (h : Derives Γ t A) (hv : Valid Γ ρ) : Holds A ρ :=
  h.2.2.2.2.2.realize ρ hv.valuation

/-- Finite value substitution: only actual entries need replacement derivations.
The total-context completion is filled with a natural term outside that scope. -/
def finiteValues (Γ : List Ty) (υ : Nat → Term) : Nat → Term :=
  fun x => if x < Γ.length then υ x else .natural (.lit 0)

theorem finite_value_substitution (h : ScopedTyping n Γ t A)
    (hΔ : ∀ B ∈ Δ, B.Scoped n)
    (υ : Nat → Term)
    (hυ : ∀ x, x < Γ.length → ScopedTyping n Δ (υ x) (complete Γ x)) :
    ScopedTyping n Δ (t.valueSubst (finiteValues Γ υ)) A := by
  refine ⟨hΔ, ?_, h.2.2.1, ?_⟩
  · apply Term.scoped_valueSubst h.2.1
    intro x hx
    simpa [finiteValues, hx] using (hυ x hx).2.1
  · apply h.2.2.2.valueSubstitution
    intro x
    by_cases hx : x < Γ.length
    · simpa [finiteValues, hx] using (hυ x hx).2.2.2
    · have missing : Γ[x]? = none := List.getElem?_eq_none (by omega)
      simp only [finiteValues, hx, ↓reduceIte, complete, missing, Option.getD_none]
      exact .natural _ _

/-- A simultaneous scalar/proof substitution between independently well-formed
mixed telescopes. Every source proof is replaced at its scalar-substituted type. -/
structure Substitutes (Γ Δ : Telescope) (σ : Substitution) (υ : Nat → Term) : Prop where
  target : WellFormed Δ
  indices : ScopedSubstitution Γ.naturals Δ.naturals σ
  proofs : ∀ x, x < Γ.proofs.length →
    ScopedTyping Δ.naturals Δ.proofs (υ x) ((complete Γ.proofs x).subst σ)

theorem Derives.substitution (h : Derives Γ t A) (s : Substitutes Γ Δ σ υ) :
    Derives Δ
      ((t.subst σ).valueSubst (finiteValues (Γ.proofs.map (fun B => B.subst σ)) υ))
      (A.subst σ) := by
  refine ⟨s.target, h.2.1.subst σ, ?_⟩
  apply finite_value_substitution (h.2.2.indexSubstitution s.indices) s.target.scoped
  intro x hx
  rw [complete_subst]
  exact s.proofs x (by simpa using hx)

/-- Substituted derivations are true in every valid target environment. The
replacement proofs are syntactically typed, not assumed true conclusions. -/
theorem Derives.substitution_sound (h : Derives Γ t A)
    (s : Substitutes Γ Δ σ υ) (hv : Valid Δ ρ) : Holds (A.subst σ) ρ :=
  (h.substitution s).sound hv

/-- Discharge the newest natural binder without capturing older indices. Proof
assumptions introduced before that binder return to their original types. -/
theorem natural_instantiation (wf : WellFormed Γ) (ha : a.Scoped Γ.naturals) :
    Substitutes (.natural Γ) Γ (single a) Term.param := by
  refine ⟨wf, scoped_single ha, ?_⟩
  intro x hx
  have bound : x < Γ.proofs.length := by simpa [Telescope.proofs] using hx
  have member : complete Γ.proofs x ∈ Γ.proofs := by
    simp [complete, List.getElem?_eq_getElem bound]
  rw [Telescope.proofs, complete_subst, Context.subst, Ty.shift_single]
  exact ⟨wf.scoped, bound, wf.scoped _ member, .param _ _⟩

/-- Discharge the newest proof assumption. Proof substitution never alters
indices; inserted proofs are index-weakened beneath natural lambdas. -/
theorem proof_instantiation (wf : WellFormed Γ)
    (hv : ScopedTyping Γ.naturals Γ.proofs v P) :
    Substitutes (.proof Γ P) Γ Expr.var (singleValue v) := by
  refine ⟨wf, ?_, ?_⟩
  · intro x hx
    exact hx
  · intro x hx
    rw [Ty.subst_id]
    cases x with
    | zero => exact hv
    | succ x =>
        have bound : x < Γ.proofs.length := by
          simp only [Telescope.proofs, List.length_cons] at hx
          omega
        have member : complete Γ.proofs x ∈ Γ.proofs := by
          simp [complete, List.getElem?_eq_getElem bound]
        exact ⟨wf.scoped, bound, wf.scoped _ member, .param _ _⟩

theorem no_closed_false_bound :
    ¬ Derives .empty t (.lt (.lit n) (.lit n)) := by
  intro h
  obtain ⟨bad⟩ := h.sound (.empty (fun _ => 0))
  exact Nat.lt_irrefl n bad.down

theorem no_closed_false_equality (hne : m ≠ n) :
    ¬ Derives .empty t (.eq (.lit m) (.lit n)) := by
  intro h
  obtain ⟨bad⟩ := h.sound (.empty (fun _ => 0))
  exact hne bad.down

end Jihoo.Indexed.Mixed
