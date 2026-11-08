import Jihoo.CoreBridgeBetaTyping

/-! A deliberately first-order, ghost-natural model of symbolic sums. Leaves
are representable words; evaluation and coefficients are mathematical naturals.
This is neither machine arithmetic nor an extension of Beta.Conv. -/
namespace Jihoo.CoreBridge.LinearNaturals

inductive Expr (arity : Nat) where
  | var : Fin arity → Expr arity
  | lit : Word → Expr arity
  | add : Expr arity → Expr arity → Expr arity

def Expr.encode : Expr n → Raw
  | .var x => .var x.val
  | .lit x => .natural x.val
  | .add a b => .uadd a.encode b.encode

def Expr.eval (ρ : Nat → Nat) : Expr n → Nat
  | .var x => ρ x.val
  | .lit x => x.val
  | .add a b => a.eval ρ + b.eval ρ

/-- Exactly n available scalar variables, in de Bruijn order. -/
def context (n : Nat) : Raw.Context := fun x => if x < n then some .u64 else none

theorem Expr.typed (e : Expr n) : Raw.Beta.HasType (context n) e.encode .u64 := by
  induction e with
  | var x => exact .var (by simp [context, x.isLt])
  | lit x => exact .natural x.isLt
  | add a b ha hb => exact .uadd ha hb

/-- Extraction returns an exact representation witness, not an assumed typing
or evaluation result. Unsupported constructors and out-of-scope leaves fail. -/
def extract (n : Nat) : (t : Raw) → Option {e : Expr n // e.encode = t}
  | .var x => if h : x < n then some ⟨.var ⟨x, h⟩, rfl⟩ else none
  | .natural x => if h : x < wordBound then some ⟨.lit ⟨x, h⟩, rfl⟩ else none
  | .uadd a b => do
      let ea ← extract n a
      let eb ← extract n b
      pure ⟨.add ea.val eb.val, by simp only [Expr.encode, ea.property, eb.property]⟩
  | _ => none

def coefficientsAdd : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: coefficientsAdd xs ys

def coefficientsEval : List Nat → (Nat → Nat) → Nat
  | [], _ => 0
  | x :: xs, ρ => x * ρ 0 + coefficientsEval xs (fun i => ρ (i + 1))

theorem coefficientsAdd_eval (xs ys : List Nat) (ρ : Nat → Nat) :
    coefficientsEval (coefficientsAdd xs ys) ρ = coefficientsEval xs ρ + coefficientsEval ys ρ := by
  induction xs generalizing ys ρ with
  | nil => simp [coefficientsAdd, coefficientsEval]
  | cons x xs ih =>
      cases ys with
      | nil => simp [coefficientsAdd, coefficientsEval]
      | cons y ys =>
          simp only [coefficientsAdd, coefficientsEval, ih, Nat.add_mul]
          omega

def basis : Nat → List Nat
  | 0 => [1]
  | k + 1 => 0 :: basis k

theorem basis_eval (k : Nat) (ρ : Nat → Nat) : coefficientsEval (basis k) ρ = ρ k := by
  induction k generalizing ρ with
  | zero => simp [basis, coefficientsEval]
  | succ k ih => simp [basis, coefficientsEval, ih]

structure Normal where
  constant : Nat
  coefficients : List Nat
  deriving DecidableEq, Repr

def Normal.eval (p : Normal) (ρ : Nat → Nat) : Nat := p.constant + coefficientsEval p.coefficients ρ

def Expr.normalize : Expr n → Normal
  | .var x => ⟨0, basis x.val⟩
  | .lit x => ⟨x.val, []⟩
  | .add a b => ⟨a.normalize.constant + b.normalize.constant,
      coefficientsAdd a.normalize.coefficients b.normalize.coefficients⟩

theorem Expr.normalize_eval (e : Expr n) (ρ : Nat → Nat) : e.normalize.eval ρ = e.eval ρ := by
  induction e with
  | var x => simp [normalize, Normal.eval, basis_eval, eval]
  | lit x => simp [normalize, Normal.eval, coefficientsEval, eval]
  | add a b ha hb =>
      simp only [normalize, Normal.eval, coefficientsAdd_eval, eval] at *
      omega

theorem Expr.equal_normal_values (a b : Expr n) (h : a.normalize = b.normalize) (ρ : Nat → Nat) :
    a.eval ρ = b.eval ρ := by
  rw [← a.normalize_eval ρ, ← b.normalize_eval ρ, h]

/-- Structural semantics independent of the coefficient checker. -/
inductive Evaluates (ρ : Nat → Nat) : Raw → Nat → Prop where
  | var : Evaluates ρ (.var k) (ρ k)
  | lit : Evaluates ρ (.natural n) n
  | add : Evaluates ρ a x → Evaluates ρ b y → Evaluates ρ (.uadd a b) (x + y)

theorem Expr.evaluates (e : Expr n) (ρ : Nat → Nat) : Evaluates ρ e.encode (e.eval ρ) := by
  induction e with
  | var => exact .var
  | lit => exact .lit
  | add _ _ ha hb => exact .add ha hb

theorem Evaluates.deterministic (h : Evaluates ρ t x) (h' : Evaluates ρ t y) : x = y := by
  induction h generalizing y with
  | var => cases h'; rfl
  | lit => cases h'; rfl
  | add _ _ ha hb => cases h' with | add a b => rw [ha a, hb b]

/-- Successful equality checking entails equal values for every environment;
there is no sample-based testing premise. -/
def equivalent (n : Nat) (t u : Raw) :
    Option (PLift (Raw.Beta.HasType (context n) t .u64 ∧ Raw.Beta.HasType (context n) u .u64 ∧
      ∀ ρ, ∃ v, Evaluates ρ t v ∧ Evaluates ρ u v)) := do
  let a ← extract n t
  let b ← extract n u
  if h : a.val.normalize = b.val.normalize then
    pure ⟨by
      have typedA := a.val.typed
      have typedB := b.val.typed
      rw [a.property] at typedA
      rw [b.property] at typedB
      refine ⟨typedA, typedB, fun ρ => ⟨a.val.eval ρ, ?_, ?_⟩⟩
      · simpa only [a.property] using a.val.evaluates ρ
      · rw [a.val.equal_normal_values b.val h ρ]
        simpa only [b.property] using b.val.evaluates ρ⟩
  else none

end Jihoo.CoreBridge.LinearNaturals
