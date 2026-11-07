import Std.Tactic

/-! A declarative arithmetic fragment of jihoo's pure model, not an
implementation of `core.jh`. Logical indices denote naturals, not UInt64. -/
namespace Jihoo.Arithmetic

inductive Expr where
  | var : Nat → Expr
  | lit : Nat → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  deriving DecidableEq, Repr

abbrev Env := Nat → Nat

def Expr.eval (ρ : Env) : Expr → Nat
  | .var n => ρ n
  | .lit n => n
  | .add a b => a.eval ρ + b.eval ρ
  | .sub a b => a.eval ρ - b.eval ρ

def Expr.subst (σ : Nat → Expr) : Expr → Expr
  | .var n => σ n
  | .lit n => .lit n
  | .add a b => .add (a.subst σ) (b.subst σ)
  | .sub a b => .sub (a.subst σ) (b.subst σ)

theorem Expr.eval_subst (t : Expr) (σ : Nat → Expr) (ρ : Env) :
    (t.subst σ).eval ρ = t.eval (fun n => (σ n).eval ρ) := by
  induction t <;> simp_all [Expr.subst, Expr.eval]

/-- A declarative natural-number equational theory inspired by pure conversion.
This does not assert completeness or correctness of jihoo's normalizer. -/
inductive Conv : Expr → Expr → Prop where
  | refl (a) : Conv a a
  | symm : Conv a b → Conv b a
  | trans : Conv a b → Conv b c → Conv a c
  | add : Conv a a' → Conv b b' → Conv (.add a b) (.add a' b')
  | sub : Conv a a' → Conv b b' → Conv (.sub a b) (.sub a' b')
  | addComm (a b) : Conv (.add a b) (.add b a)
  | addAssoc (a b c) : Conv (.add (.add a b) c) (.add a (.add b c))
  | addZero (a) : Conv (.add a (.lit 0)) a
  | addLiterals (m n) : Conv (.add (.lit m) (.lit n)) (.lit (m + n))
  | subLiterals (m n) : Conv (.sub (.lit m) (.lit n)) (.lit (m - n))
  | subAddCancel (a b) : Conv (.sub (.add a b) b) a

theorem Conv.sound (h : Conv a b) (ρ : Env) : a.eval ρ = b.eval ρ := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | add _ _ ih₁ ih₂ => simp_all [Expr.eval]
  | sub _ _ ih₁ ih₂ => simp_all [Expr.eval]
  | addComm => simp [Expr.eval, Nat.add_comm]
  | addAssoc => simp [Expr.eval, Nat.add_assoc]
  | addZero => simp [Expr.eval]
  | addLiterals => rfl
  | subLiterals => rfl
  | subAddCancel => simp [Expr.eval]

theorem Conv.subst (h : Conv a b) (σ : Nat → Expr) :
    Conv (a.subst σ) (b.subst σ) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | add _ _ ih₁ ih₂ => exact .add ih₁ ih₂
  | sub _ _ ih₁ ih₂ => exact .sub ih₁ ih₂
  | addComm => exact .addComm _ _
  | addAssoc => exact .addAssoc _ _ _
  | addZero => exact .addZero _
  | addLiterals => exact .addLiterals _ _
  | subLiterals => exact .subLiterals _ _
  | subAddCancel => exact .subAddCancel _ _

inductive Formula where
  | lt : Expr → Expr → Formula
  | eq : Expr → Expr → Formula
  deriving DecidableEq, Repr

def Formula.Holds (ρ : Env) : Formula → Prop
  | .lt a b => a.eval ρ < b.eval ρ
  | .eq a b => a.eval ρ = b.eval ρ

def Formula.subst (σ : Nat → Expr) : Formula → Formula
  | .lt a b => .lt (a.subst σ) (b.subst σ)
  | .eq a b => .eq (a.subst σ) (b.subst σ)

theorem Formula.holds_subst (p : Formula) (σ : Nat → Expr) (ρ : Env) :
    (p.subst σ).Holds ρ ↔ p.Holds (fun n => (σ n).eval ρ) := by
  cases p <;> simp [Formula.subst, Formula.Holds, Expr.eval_subst]

/-- Instantiate variable zero; remaining free variables retain their numbers.
This is a first-order proposition family, not a dependent binder telescope. -/
def instantiate (p : Formula) (a : Expr) : Formula :=
  p.subst (fun n => if n = 0 then a else .var n)

abbrev Context := List Formula

def Satisfies (ρ : Env) (Γ : Context) : Prop := ∀ p ∈ Γ, p.Holds ρ

/-- Syntactic evidence rules. No constructor assumes semantic validity of an arbitrary formula;
`decide` requires only a closed numeral comparison. -/
inductive Derives (Γ : Context) : Formula → Prop where
  | assumption : p ∈ Γ → Derives Γ p
  | refl (a) : Derives Γ (.eq a a)
  | decide (m n : Nat) : m < n → Derives Γ (.lt (.lit m) (.lit n))
  | zeroLe (a) : Derives Γ (.lt (.lit 0) (.add a (.lit 1)))
  | ltAdd : Derives Γ (.lt a b) → Derives Γ (.lt (.add a c) (.add b c))
  | ltCancel : Derives Γ (.lt (.add a c) (.add b c)) → Derives Γ (.lt a b)
  | ltLe : Derives Γ (.lt x y) → Derives Γ (.lt y (.add z (.lit 1))) →
      Derives Γ (.lt x z)
  | convertLt : Conv a a' → Conv b b' → Derives Γ (.lt a b) →
      Derives Γ (.lt a' b')
  | convertEq : Conv a a' → Conv b b' → Derives Γ (.eq a b) →
      Derives Γ (.eq a' b')
  | transport (p : Formula) : Derives Γ (.eq a b) →
      Derives Γ (instantiate p a) → Derives Γ (instantiate p b)

theorem Derives.sound (h : Derives Γ p) (ρ : Env) (hΓ : Satisfies ρ Γ) :
    p.Holds ρ := by
  induction h with
  | assumption hp => exact hΓ _ hp
  | refl => rfl
  | decide _ _ h => exact h
  | zeroLe => simp [Formula.Holds, Expr.eval]
  | ltAdd _ ih => simp_all [Formula.Holds, Expr.eval]
  | ltCancel _ ih => simp_all [Formula.Holds, Expr.eval]
  | ltLe _ _ ih₁ ih₂ =>
      simp only [Formula.Holds, Expr.eval] at *
      omega
  | convertLt ha hb _ ih =>
      simp only [Formula.Holds] at *
      rw [← ha.sound ρ, ← hb.sound ρ]
      exact ih
  | convertEq ha hb _ ih =>
      simp only [Formula.Holds] at *
      rw [← ha.sound ρ, ← hb.sound ρ]
      exact ih
  | @transport a b p _ _ he hp =>
      simp only [Formula.Holds] at he
      simp only [instantiate, Formula.holds_subst] at hp ⊢
      have same : (fun n => (if n = 0 then a else Expr.var n).eval ρ) =
          (fun n => (if n = 0 then b else Expr.var n).eval ρ) := by
        funext n
        split <;> simp_all
      rw [← same]
      exact hp

/-- Consistency for this fragment, with no assumption that an input derivation
was produced by the jihoo implementation. -/
theorem no_closed_false_lt : ¬ Derives [] (.lt (.lit 0) (.lit 0)) := by
  intro h
  have bad := h.sound (fun _ => 0) (by simp [Satisfies])
  exact (Nat.lt_irrefl 0) bad

/-- Evidence justifies the bounded subtraction cancellation used by the core.
Unlike `(a+b)-b=a`, this rewrite needs the non-underflow premise. -/
theorem certified_sub_add (h : Derives Γ (.lt b (.add a (.lit 1))))
    (ρ : Env) (hΓ : Satisfies ρ Γ) :
    (.add (.sub a b) b : Expr).eval ρ = a.eval ρ := by
  have bound := h.sound ρ hΓ
  simp only [Formula.Holds, Expr.eval] at *
  omega

/-- The arithmetic part of bounds safety: runtime representation and heap
length correspondence are separate obligations, not assumptions hidden here. -/
theorem certified_index_lt (h : Derives Γ (.lt i n))
    (ρ : Env) (hΓ : Satisfies ρ Γ) : i.eval ρ < n.eval ρ :=
  h.sound ρ hΓ

end Jihoo.Arithmetic
