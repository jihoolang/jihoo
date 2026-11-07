import Jihoo.Scoped

/-! Logical interpretation of the conversion-aware index/value-let calculus.
Realization recurses on typing derivations; it proves inhabitation and consistency,
not operational adequacy, runtime behavior or implementation correctness. -/
namespace Jihoo.Indexed
open Arithmetic (Expr Env)

def extendEnv (ρ : Env) (a : Nat) : Env
  | 0 => a
  | n + 1 => ρ n

theorem lift_eval (σ : Substitution) (ρ : Env) (a : Nat) :
    (fun n => (lift σ n).eval (extendEnv ρ a)) =
      extendEnv (fun n => (σ n).eval ρ) a := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [lift, Expr.eval_subst, shift, Expr.eval, extendEnv]

theorem Ty.view_subst (A : Ty) (σ : Substitution) (ρ : Env) :
    (A.subst σ).view ρ = A.view (fun n => (σ n).eval ρ) := by
  induction A generalizing σ ρ with
  | u64 => rfl
  | i64 => rfl
  | array => simp only [Ty.subst, Ty.view, Expr.eval_subst]
  | lt => simp only [Ty.subst, Ty.view, Expr.eval_subst]
  | eq => simp only [Ty.subst, Ty.view, Expr.eval_subst]
  | pi B ih =>
      apply congrArg TypeView.pi
      funext a
      change (B.subst (lift σ)).view (extendEnv ρ a) =
        B.view (extendEnv (fun n => (σ n).eval ρ) a)
      rw [ih, lift_eval]

/-- Propositions are lifted to Type; arrays are genuinely length-indexed
functions. Function types bind a mathematical natural, not a machine word. -/
def TypeView.denote : TypeView → Type
  | .u64 => Nat
  | .i64 => Int
  | .array n => Fin n → Int
  | .lt a b => PLift (a < b)
  | .eq a b => PLift (a = b)
  | .pi B => (a : Nat) → (B a).denote

def Ty.denote (A : Ty) (ρ : Env) : Type := (A.view ρ).denote

theorem Ty.Conv.denote_sound {A B : Ty} (h : A.Conv B) (ρ : Env) :
    A.denote ρ = B.denote ρ := congrArg TypeView.denote (h.view_sound ρ)

theorem Ty.denote_subst (A : Ty) (σ : Substitution) (ρ : Env) :
    (A.subst σ).denote ρ = A.denote (fun n => (σ n).eval ρ) :=
  congrArg TypeView.denote (A.view_subst σ ρ)

theorem Ty.denote_shift (A : Ty) (ρ : Env) (a : Nat) :
    (A.subst shift).denote (extendEnv ρ a) = A.denote ρ := by
  rw [A.denote_subst]
  rfl

theorem Ty.denote_single (A : Ty) (ρ : Env) (a : Expr) :
    (A.subst (single a)).denote ρ = A.denote (extendEnv ρ (a.eval ρ)) := by
  rw [A.denote_subst]
  have same : (fun n => (single a n).eval ρ) = extendEnv ρ (a.eval ρ) := by
    funext n
    cases n <;> rfl
  rw [same]

abbrev Valuation (Γ : Context) (ρ : Env) := (x : Nat) → Nonempty ((Γ x).denote ρ)

/-- Every typing derivation realizes its result type, assuming realizations of
its free parameters. No validity of its conclusion is assumed as a premise. -/
theorem HasType.realize (h : HasType Γ t A) (ρ : Env) (values : Valuation Γ ρ) :
    Nonempty (A.denote ρ) := by
  induction h generalizing ρ with
  | param Γ x => exact values x
  | natural Γ a => exact ⟨a.eval ρ⟩
  | integer Γ n => exact ⟨n⟩
  | elements Γ ns => exact ⟨fun i => ns[i.val]'i.isLt⟩
  | decide Γ m n h => exact ⟨⟨h⟩⟩
  | refl Γ a => exact ⟨⟨rfl⟩⟩
  | zeroLe Γ a => exact ⟨⟨Nat.zero_lt_succ _⟩⟩
  | index ha hp iha ihp =>
      obtain ⟨array⟩ := iha ρ values
      obtain ⟨proof⟩ := ihp ρ values
      exact ⟨array ⟨_, proof.down⟩⟩
  | @lam body B Γ hb ih =>
      refine ⟨fun a => Classical.choice (ih (extendEnv ρ a) ?_)⟩
      intro x
      obtain ⟨value⟩ := values x
      exact ⟨cast ((Γ x).denote_shift ρ a).symm value⟩
  | @app Γ f B a hf ih =>
      obtain ⟨function⟩ := ih ρ values
      exact ⟨cast (B.denote_single ρ a).symm (function (a.eval ρ))⟩
  | @letValue Γ v A body B hv hb ihv ihb =>
      apply ihb ρ
      intro x
      cases x with
      | zero => exact ihv ρ values
      | succ x => exact values x
  | convert _ hc ih =>
      obtain ⟨value⟩ := ih ρ values
      exact ⟨cast (hc.denote_sound ρ) value⟩

theorem empty_valuation (ρ : Env) : Valuation (complete []) ρ := by
  intro x
  simpa [complete, Ty.denote, Ty.view, TypeView.denote] using (show Nonempty Nat from ⟨0⟩)

/-- The finite, empty-context calculus has no evidence of a false strict bound.
This includes index lambdas, value lets, and conversions in arbitrary positions. -/
theorem no_closed_false_bound : ¬ ScopedTyping 0 [] t (.lt (.lit 0) (.lit 0)) := by
  intro h
  obtain ⟨bad⟩ := h.2.2.2.realize (fun _ => 0) (empty_valuation _)
  exact (Nat.lt_irrefl 0) bad.down

theorem no_closed_false_equality :
    ¬ ScopedTyping 0 [] t (.eq (.lit 0) (.lit 1)) := by
  intro h
  obtain ⟨bad⟩ := h.2.2.2.realize (fun _ => 0) (empty_valuation _)
  exact (Nat.zero_ne_one) bad.down

end Jihoo.Indexed
