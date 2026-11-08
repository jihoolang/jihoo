import Jihoo.LinearEvidence

/-! Scoped, capture-avoiding substitution for first-order natural indices and
quantified formulas. Encoding commutes with existing Raw.subst, and semantics
commutes with environment substitution. No general Beta.Conv soundness is used. -/
namespace Jihoo.CoreBridge.LinearNaturals

def Expr.rename (ρ : Fin n → Fin m) : Expr n → Expr m
  | .var x => .var (ρ x)
  | .lit x => .lit x
  | .add a b => .add (a.rename ρ) (b.rename ρ)

def Expr.substitute (σ : Fin n → Expr m) : Expr n → Expr m
  | .var x => σ x
  | .lit x => .lit x
  | .add a b => .add (a.substitute σ) (b.substitute σ)

theorem Expr.encode_rename (e : Expr n) (ρ : Fin n → Fin m) (r : Nat → Nat)
    (h : ∀ x, (ρ x).val = r x.val) : (e.rename ρ).encode = e.encode.rename r := by
  induction e with
  | var x => simp [rename, encode, Raw.rename, h]
  | lit => simp [rename, encode, Raw.rename]
  | add _ _ ha hb => simp only [rename, encode, Raw.rename, ha, hb]

theorem Expr.eval_rename (e : Expr n) (r : Fin n → Fin m) (ρ η : Nat → Nat)
    (h : ∀ x, η (r x).val = ρ x.val) : (e.rename r).eval η = e.eval ρ := by
  induction e with
  | var x => exact h x
  | lit => rfl
  | add _ _ ha hb => simp only [rename, eval, ha, hb]

theorem Expr.encode_substitute (e : Expr n) (σ : Fin n → Expr m) (s : Nat → Raw)
    (h : ∀ x, (σ x).encode = s x.val) : (e.substitute σ).encode = e.encode.subst s := by
  induction e with
  | var x => simpa [substitute, encode, Raw.subst] using h x
  | lit => simp [substitute, encode, Raw.subst]
  | add _ _ ha hb => simp only [substitute, encode, Raw.subst, ha, hb]

theorem Expr.eval_substitute (e : Expr n) (σ : Fin n → Expr m) (ρ η : Nat → Nat)
    (h : ∀ x, (σ x).eval η = ρ x.val) : (e.substitute σ).eval η = e.eval ρ := by
  induction e with
  | var x => exact h x
  | lit => rfl
  | add _ _ ha hb => simp only [substitute, eval, ha, hb]

def lift (σ : Fin n → Expr m) : Fin (n + 1) → Expr (m + 1) :=
  Fin.cases (.var 0) (fun x => (σ x).rename Fin.succ)

end Jihoo.CoreBridge.LinearNaturals

namespace Jihoo.CoreBridge.LinearEvidence
open LinearNaturals

def Formula.substitute (σ : Fin n → Expr m) : Formula n → Formula m
  | .equal a b => .equal (a.substitute σ) (b.substitute σ)
  | .less a b => .less (a.substitute σ) (b.substitute σ)
  | .all p => .all (p.substitute (lift σ))

theorem Formula.encode_substitute (p : Formula n) (σ : Fin n → Expr m) (s : Nat → Raw)
    (h : ∀ x, (σ x).encode = s x.val) : (p.substitute σ).encode = p.encode.subst s := by
  induction p generalizing m s with
  | equal a b => simp only [substitute, encode, Raw.subst, Expr.encode_substitute _ _ _ h]
  | less a b => simp only [substitute, encode, Raw.subst, Expr.encode_substitute _ _ _ h]
  | all p ih =>
      simp only [substitute, encode, Raw.subst]
      congr 1
      apply ih
      intro x
      refine Fin.cases ?_ (fun y => ?_) x
      · rfl
      · simp only [lift, Fin.cases_succ]
        rw [Expr.encode_rename _ _ Nat.succ (fun _ => rfl), h]
        rfl

theorem Formula.holds_substitute (p : Formula n) (σ : Fin n → Expr m) (ρ η : Nat → Nat)
    (h : ∀ x, (σ x).eval η = ρ x.val) : (p.substitute σ).Holds η ↔ p.Holds ρ := by
  induction p generalizing m ρ η with
  | equal a b => simp only [substitute, Holds, Expr.eval_substitute _ _ _ _ h]
  | less a b => simp only [substitute, Holds, Expr.eval_substitute _ _ _ _ h]
  | all p ih =>
      apply forall_congr'
      intro v
      apply ih
      intro x
      refine Fin.cases ?_ (fun y => ?_) x
      · rfl
      · simp only [lift, Fin.cases_succ]
        rw [Expr.eval_rename _ _ η (extend η v) (fun _ => rfl), h]
        rfl

def Formula.instantiate (p : Formula (n + 1)) (a : Expr n) : Formula n :=
  p.substitute (Fin.cases a Expr.var)

theorem Formula.encode_instantiate (p : Formula (n + 1)) (a : Expr n) :
    (p.instantiate a).encode = p.encode.subst (Raw.single a.encode) := by
  apply p.encode_substitute
  intro x
  exact Fin.cases rfl (fun _ => rfl) x

theorem Formula.holds_instantiate (p : Formula (n + 1)) (a : Expr n) (ρ : Nat → Nat) :
    (p.instantiate a).Holds ρ ↔ p.Holds (extend ρ (a.eval ρ)) := by
  apply p.holds_substitute
  intro x
  exact Fin.cases rfl (fun _ => rfl) x

/-- A compositional semantic extension; the old Derives judgment is unchanged.
Applications take only natural indices, never higher-order or proof arguments. -/
inductive Applied : {n : Nat} → Raw → Formula n → Prop where
  | base : Derives t p → Applied t p
  | app {n : Nat} {f : Raw} {p : Formula (n + 1)} :
      Applied f (.all p) → (a : Expr n) → Applied (.app f a.encode) (p.instantiate a)
  | lam : Applied t p → Applied (.lam false .u64 t) (.all p)
  | convert : Applied t p → Converts p q → Applied t q

theorem Applied.sound (h : Applied t p) (ρ : Nat → Nat) : p.Holds ρ := by
  induction h generalizing ρ with
  | base h => exact h.sound ρ
  | app _ a ih => exact (Formula.holds_instantiate _ a ρ).mpr (ih ρ (a.eval ρ))
  | lam _ ih => exact fun x => ih (extend ρ x)
  | convert _ hc ih => exact (hc.sound ρ).mp (ih ρ)

end Jihoo.CoreBridge.LinearEvidence
