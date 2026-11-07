import Jihoo.Indexed

/-! Finite scope for the index/value calculus. Scoping is independent of typing
and reduction; the finite typing judgment combines the already proved relations. -/
namespace Jihoo.Indexed

open Arithmetic (Expr)

def _root_.Jihoo.Arithmetic.Expr.Scoped (n : Nat) : Expr → Prop
  | .var x => x < n
  | .lit _ => True
  | .add a b | .sub a b => a.Scoped n ∧ b.Scoped n

abbrev ScopedSubstitution (n m : Nat) (σ : Substitution) :=
  ∀ x, x < n → (σ x).Scoped m

theorem _root_.Jihoo.Arithmetic.Expr.scoped_subst {t : Expr} (h : t.Scoped n) (hσ : ScopedSubstitution n m σ) :
    (t.subst σ).Scoped m := by
  induction t with
  | var x => exact hσ x h
  | lit => trivial
  | add a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | sub a b iha ihb => exact ⟨iha h.1, ihb h.2⟩

theorem scoped_shift : ScopedSubstitution n (n + 1) shift := by
  intro x h
  simp only [shift, Expr.Scoped]
  omega

theorem scoped_lift (hσ : ScopedSubstitution n m σ) :
    ScopedSubstitution (n + 1) (m + 1) (lift σ) := by
  intro x h
  cases x with
  | zero => simp [lift, Expr.Scoped]
  | succ x => exact Expr.scoped_subst (hσ x (by omega)) scoped_shift

theorem scoped_single {a : Expr} (h : a.Scoped n) : ScopedSubstitution (n + 1) n (single a) := by
  intro x hx
  cases x with
  | zero => exact h
  | succ x => simpa [single, Expr.Scoped] using (show x < n by omega)

def Ty.Scoped (n : Nat) : Ty → Prop
  | .u64 | .i64 => True
  | .array a => a.Scoped n
  | .lt a b | .eq a b => a.Scoped n ∧ b.Scoped n
  | .pi B => B.Scoped (n + 1)

theorem Ty.scoped_subst {A : Ty} (h : A.Scoped n) (hσ : ScopedSubstitution n m σ) :
    (A.subst σ).Scoped m := by
  induction A generalizing n m σ with
  | u64 => trivial
  | i64 => trivial
  | array => exact Expr.scoped_subst h hσ
  | lt => exact ⟨Expr.scoped_subst h.1 hσ, Expr.scoped_subst h.2 hσ⟩
  | eq => exact ⟨Expr.scoped_subst h.1 hσ, Expr.scoped_subst h.2 hσ⟩
  | pi B ih => exact ih h (scoped_lift hσ)

def Term.Scoped (n m : Nat) : Term → Prop
  | .param x => x < m
  | .natural a | .refl a | .zeroLe a => a.Scoped n
  | .integer _ | .elements _ | .decide _ _ => True
  | .index a i p => a.Scoped n m ∧ i.Scoped n ∧ p.Scoped n m
  | .lam body => body.Scoped (n + 1) m
  | .app f a => f.Scoped n m ∧ a.Scoped n
  | .letValue v body => v.Scoped n m ∧ body.Scoped n (m + 1)

theorem Term.scoped_indexSubst {t : Term} (h : t.Scoped n m)
    (hσ : ScopedSubstitution n k σ) : (t.subst σ).Scoped k m := by
  induction t generalizing n m k σ with
  | param => exact h
  | natural => exact Expr.scoped_subst h hσ
  | integer => trivial
  | elements => trivial
  | decide => trivial
  | refl => exact Expr.scoped_subst h hσ
  | zeroLe => exact Expr.scoped_subst h hσ
  | index a i p iha ihp =>
      exact ⟨iha h.1 hσ, Expr.scoped_subst h.2.1 hσ, ihp h.2.2 hσ⟩
  | lam body ih => exact ih h (scoped_lift hσ)
  | app f a ih => exact ⟨ih h.1 hσ, Expr.scoped_subst h.2 hσ⟩
  | letValue v body ihv ihb => exact ⟨ihv h.1 hσ, ihb h.2 hσ⟩

theorem Term.scoped_valueRenaming {t : Term} {ρ : Nat → Nat} (h : t.Scoped n m)
    (hρ : ∀ x, x < m → ρ x < k) : (t.renameValues ρ).Scoped n k := by
  induction t generalizing n m k ρ with
  | param x => exact hρ x h
  | natural => exact h
  | integer => trivial
  | elements => trivial
  | decide => trivial
  | refl => exact h
  | zeroLe => exact h
  | index a i p iha ihp => exact ⟨iha h.1 hρ, h.2.1, ihp h.2.2 hρ⟩
  | lam body ih => exact ih h hρ
  | app f a ih => exact ⟨ih h.1 hρ, h.2⟩
  | letValue v body ihv ihb =>
      refine ⟨ihv h.1 hρ, ihb h.2 ?_⟩
      intro x hx
      cases x with
      | zero => simp [liftRenaming]
      | succ x =>
          have := hρ x (by omega)
          simp only [liftRenaming]
          omega

theorem Term.scoped_valueSubst {t : Term} {σ : Nat → Term} (h : t.Scoped n m)
    (hσ : ∀ x, x < m → (σ x).Scoped n k) : (t.valueSubst σ).Scoped n k := by
  induction t generalizing n m k σ with
  | param x => exact hσ x h
  | natural => exact h
  | integer => trivial
  | elements => trivial
  | decide => trivial
  | refl => exact h
  | zeroLe => exact h
  | index a i p iha ihp => exact ⟨iha h.1 hσ, h.2.1, ihp h.2.2 hσ⟩
  | lam body ih =>
      apply ih h
      intro x hx
      exact Term.scoped_indexSubst (hσ x hx) scoped_shift
  | app f a ih => exact ⟨ih h.1 hσ, h.2⟩
  | letValue v body ihv ihb =>
      refine ⟨ihv h.1 hσ, ihb h.2 ?_⟩
      intro x hx
      cases x with
      | zero => simp [liftValues, Term.Scoped]
      | succ x =>
          apply Term.scoped_valueRenaming (hσ x (by omega))
          intro y hy
          omega

/-- Untyped reduction does not create dangling indices or value variables. -/
theorem scoped_step (h : t.Scoped n m) (hs : Step t u) : u.Scoped n m := by
  induction hs generalizing n m with
  | beta body a => exact Term.scoped_indexSubst h.1 (scoped_single h.2)
  | lam _ ih => exact ih h
  | app _ ih => exact ⟨ih h.1, h.2⟩
  | indexArray _ ih => exact ⟨ih h.1, h.2⟩
  | indexProof _ ih => exact ⟨h.1, h.2.1, ih h.2.2⟩
  | letBeta v body =>
      apply Term.scoped_valueSubst h.2
      intro x hx
      cases x with
      | zero => exact h.1
      | succ x => simp only [singleValue, Term.Scoped]; omega
  | letArg _ ih => exact ⟨ih h.1, h.2⟩
  | letBody _ ih => exact ⟨h.1, ih h.2⟩

/-- The completion is only a technical bridge to the earlier total context.
The separate scope premise prevents a typed term from using any default entry. -/
def complete (Γ : List Ty) : Context := fun x => Γ[x]?.getD .u64

def ScopedTyping (n : Nat) (Γ : List Ty) (t : Term) (A : Ty) : Prop :=
  (∀ B ∈ Γ, B.Scoped n) ∧ t.Scoped n Γ.length ∧ A.Scoped n ∧ HasType (complete Γ) t A

theorem complete_subst (Γ : List Ty) (σ : Substitution) :
    complete (Γ.map (fun A => A.subst σ)) = (complete Γ).subst σ := by
  funext x
  simp only [complete, Context.subst, List.getElem?_map]
  cases Γ[x]? <;> rfl

theorem ScopedTyping.indexSubstitution (h : ScopedTyping n Γ t A)
    (hσ : ScopedSubstitution n m σ) :
    ScopedTyping m (Γ.map (fun B => B.subst σ)) (t.subst σ) (A.subst σ) := by
  refine ⟨?_, ?_, Ty.scoped_subst h.2.2.1 hσ, ?_⟩
  · intro B hb
    obtain ⟨C, hc, rfl⟩ := List.mem_map.mp hb
    exact Ty.scoped_subst (h.1 C hc) hσ
  · simpa only [List.length_map] using Term.scoped_indexSubst h.2.1 hσ
  · rw [complete_subst]
    exact h.2.2.2.substitution σ

/-- The finite judgment requires the converted result type to be in scope.
Raw arithmetic equations alone can introduce otherwise unused free variables. -/
theorem ScopedTyping.convert (h : ScopedTyping n Γ t A) (hc : A.Conv B)
    (hB : B.Scoped n) : ScopedTyping n Γ t B :=
  ⟨h.1, h.2.1, hB, .convert h.2.2.2 hc⟩

theorem scoped_preservation (h : ScopedTyping n Γ t A) (hs : Step t u) :
    ScopedTyping n Γ u A :=
  ⟨h.1, scoped_step h.2.1 hs, h.2.2.1, preservation h.2.2.2 hs⟩

theorem scoped_preservation_many (h : ScopedTyping n Γ t A) (hs : Steps t u) :
    ScopedTyping n Γ u A := by
  induction hs with
  | refl => exact h
  | next step _ ih => exact ih (scoped_preservation h step)

/-- Unlike the earlier total-context typing judgment, the finite judgment
cannot type a free value parameter in an empty value context. -/
theorem no_closed_parameter : ¬ ScopedTyping n [] (.param x) A := by
  intro h
  have bad := h.2.1
  simp [Term.Scoped] at bad

end Jihoo.Indexed
