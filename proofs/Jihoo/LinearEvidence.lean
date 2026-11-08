import Jihoo.LinearNaturals

/-! A first-order evidence judgment with proved natural-sum conversion. This is
separate from Beta.HasType/Conv: it does not assume their semantic soundness or
claim to cover arbitrary terms accepted by the executable checker. -/
namespace Jihoo.CoreBridge.LinearEvidence
open LinearNaturals

inductive Formula : Nat → Type where
  | equal : Expr n → Expr n → Formula n
  | less : Expr n → Expr n → Formula n
  | all : Formula (n + 1) → Formula n

def Formula.encode : Formula n → Raw
  | .equal a b => .eq a.encode b.encode
  | .less a b => .lt a.encode b.encode
  | .all p => .pi false .u64 p.encode

def extend (ρ : Nat → Nat) (x : Nat) : Nat → Nat
  | 0 => x
  | k + 1 => ρ k

def Formula.Holds : Formula n → (Nat → Nat) → Prop
  | .equal a b, ρ => a.eval ρ = b.eval ρ
  | .less a b, ρ => a.eval ρ < b.eval ρ
  | .all p, ρ => ∀ x, p.Holds (extend ρ x)

theorem context_succ : context (n + 1) = (context n).extend .u64 := by
  funext x
  cases x with
  | zero => simp [context, Raw.Context.extend, Raw.rename]
  | succ x => simp [context, Raw.Context.extend, Raw.rename]

/-- The requested proposition is also formed in the existing Raw Beta model;
semantic evidence conversion below is deliberately a separate judgment. -/
theorem Formula.formed (p : Formula n) : Raw.Beta.IsType (context n) p.encode := by
  induction p with
  | equal a b => exact .eq a.typed b.typed
  | less a b => exact .lt a.typed b.typed
  | all p ih =>
      exact .pi .u64 rfl (by simpa only [context_succ] using ih)

/-- Independent syntax-directed conversion: no arbitrary raw beta expansion. -/
inductive Converts : Formula n → Formula n → Prop where
  | equal : a.normalize = c.normalize → b.normalize = d.normalize →
      Converts (.equal a b) (.equal c d)
  | less : a.normalize = c.normalize → b.normalize = d.normalize →
      Converts (.less a b) (.less c d)
  | all : Converts p q → Converts (.all p) (.all q)

theorem Converts.sound (h : Converts p q) (ρ : Nat → Nat) : p.Holds ρ ↔ q.Holds ρ := by
  induction h generalizing ρ with
  | equal ha hb => simp only [Formula.Holds, Expr.equal_normal_values _ _ ha ρ,
      Expr.equal_normal_values _ _ hb ρ]
  | less ha hb => simp only [Formula.Holds, Expr.equal_normal_values _ _ ha ρ,
      Expr.equal_normal_values _ _ hb ρ]
  | all _ ih => exact forall_congr' (fun x => ih (extend ρ x))

def conversion : (p q : Formula n) → Option (PLift (Converts p q))
  | .equal a b, .equal c d =>
      if ha : a.normalize = c.normalize then
        if hb : b.normalize = d.normalize then some ⟨.equal ha hb⟩ else none
      else none
  | .less a b, .less c d =>
      if ha : a.normalize = c.normalize then
        if hb : b.normalize = d.normalize then some ⟨.less ha hb⟩ else none
      else none
  | .all p, .all q => do
      let h ← conversion p q
      pure ⟨.all h.down⟩
  | _, _ => none

def parseFormula (n : Nat) : (A : Raw) → Option {p : Formula n // p.encode = A}
  | .eq a b => do
      let a' ← extract n a
      let b' ← extract n b
      pure ⟨.equal a'.val b'.val, by simp only [Formula.encode, a'.property, b'.property]⟩
  | .lt a b => do
      let a' ← extract n a
      let b' ← extract n b
      pure ⟨.less a'.val b'.val, by simp only [Formula.encode, a'.property, b'.property]⟩
  | .pi false .u64 body => do
      let p ← parseFormula (n + 1) body
      pure ⟨.all p.val, by simp only [Formula.encode, p.property]⟩
  | _ => none

def zero : Expr n := .lit ⟨0, by decide⟩
def one : Expr n := .lit ⟨1, by decide⟩

/-- Closed sums may be wider than a word, but every literal leaf is bounded. -/
theorem closed_value (e : Expr n) (h : e.normalize.coefficients = []) (ρ : Nat → Nat) :
    e.eval ρ = e.normalize.constant := by
  rw [← e.normalize_eval]
  simp [Normal.eval, h, coefficientsEval]

inductive Derives : {n : Nat} → Raw → Formula n → Prop where
  | refl (a : Expr n) : Derives (.refl a.encode) (.equal a a)
  | zeroLe (a : Expr n) : Derives (.zeroLe a.encode) (.less zero (.add a one))
  | decide (a b : Expr n) : a.normalize.coefficients = [] → b.normalize.coefficients = [] →
      a.normalize.constant < b.normalize.constant → Derives (.decide a.encode b.encode) (.less a b)
  | lam : Derives t p → Derives (.lam false .u64 t) (.all p)
  | convert : Derives t p → Converts p q → Derives t q

theorem Derives.sound (h : Derives t p) (ρ : Nat → Nat) : p.Holds ρ := by
  induction h generalizing ρ with
  | refl => rfl
  | zeroLe => simp [Formula.Holds, zero, one, Expr.eval]
  | decide a b ha hb hlt =>
      simpa only [Formula.Holds, closed_value a ha ρ, closed_value b hb ρ] using hlt
  | lam _ ih => exact fun x => ih (extend ρ x)
  | convert _ hc ih => exact (hc.sound ρ).mp (ih ρ)

/-- Proof-producing inference over the supported actual Raw constructor shapes. -/
def infer (n : Nat) : (t : Raw) → Option {p : Formula n // Derives t p}
  | .refl a => do
      let e ← extract n a
      pure ⟨.equal e.val e.val, by simpa only [e.property] using Derives.refl e.val⟩
  | .zeroLe a => do
      let e ← extract n a
      pure ⟨.less zero (.add e.val one), by simpa only [e.property] using Derives.zeroLe e.val⟩
  | .decide a b => do
      let ea ← extract n a
      let eb ← extract n b
      if ha : ea.val.normalize.coefficients = [] then
        if hb : eb.val.normalize.coefficients = [] then
          if hlt : ea.val.normalize.constant < eb.val.normalize.constant then
            pure ⟨.less ea.val eb.val, by
              simpa only [ea.property, eb.property] using Derives.decide ea.val eb.val ha hb hlt⟩
          else none
        else none
      else none
  | .lam false .u64 body => do
      let p ← infer (n + 1) body
      pure ⟨.all p.val, Derives.lam p.property⟩
  | _ => none

def check (n : Nat) (t A : Raw) :
    Option {p : Formula n // p.encode = A ∧ Derives t p} := do
  let p ← infer n t
  let q ← parseFormula n A
  let h ← conversion p.val q.val
  pure ⟨q.val, q.property, .convert p.property h.down⟩

theorem check_sound (_h : check n t A = some result) :
    result.val.encode = A ∧ Derives t result.val ∧ ∀ ρ, result.val.Holds ρ := by
  exact ⟨result.property.1, result.property.2, result.property.2.sound⟩

end Jihoo.CoreBridge.LinearEvidence
