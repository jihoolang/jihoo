import Jihoo.LinearEvidence
import Jihoo.CoreBridgeComputation

/-! Principal inference shapes for a selected actual Core.infer fragment.
These are modeled rules, not a verified translation of compiler/core.jh.
The additional word bounds on Decide match its requirement for Natural nodes. -/
namespace Jihoo.CoreBridge.CorePrincipal
open LinearNaturals LinearEvidence

theorem coefficientsAdd_nil (h : coefficientsAdd xs ys = []) : xs = [] ∧ ys = [] := by
  cases xs <;> cases ys <;> simp_all [coefficientsAdd]

theorem basis_nonempty (k : Nat) : basis k ≠ [] := by
  cases k <;> simp [basis]

theorem steps_trans (h : Raw.Computation.Steps a b) (g : Raw.Computation.Steps b c) :
    Raw.Computation.Steps a c := by
  induction h with
  | refl => exact g
  | next hs _ ih => exact .next hs (ih g)

/-- Closed coefficient records below the word bound admit actual bounded-add
steps in the existing Raw computation model, not merely semantic equality. -/
theorem closed_reduces (e : Expr n) (hc : e.normalize.coefficients = [])
    (hb : e.normalize.constant < wordBound) :
    Raw.Computation.Steps e.encode (.natural e.normalize.constant) := by
  induction e with
  | var x => exact False.elim (basis_nonempty x.val hc)
  | lit x => exact .refl
  | add a b ha hb' =>
      obtain ⟨hca, hcb⟩ := coefficientsAdd_nil hc
      have hba : a.normalize.constant < wordBound := by
        simp only [Expr.normalize] at hb; omega
      have hbb : b.normalize.constant < wordBound := by
        simp only [Expr.normalize] at hb; omega
      exact steps_trans ((ha hca hba).map (fun t => .uadd t b.encode) (fun h => .uaddLeft h))
        (steps_trans ((hb' hcb hbb).map (fun t => .uadd (.natural a.normalize.constant) t)
          (fun h => .uaddRight h)) (.next (.add _ _ hb) .refl))

theorem converts_refl (p : Formula n) : Converts p p := by
  induction p with
  | equal => exact .equal rfl rfl
  | less => exact .less rfl rfl
  | all _ ih => exact .all ih

theorem converts_trans (h : Converts p q) (g : Converts q r) : Converts p r := by
  induction h with
  | equal ha hb => cases g with | equal hc hd => exact .equal (ha.trans hc) (hb.trans hd)
  | less ha hb => cases g with | less hc hd => exact .less (ha.trans hc) (hb.trans hd)
  | all _ ih => cases g with | all hc => exact .all (ih hc)

/-- Exact selected inference rules: unlike Derives, no conversion rule can
replace the inferred type. Scalar subexpressions retain their original syntax. -/
inductive Principal : {n : Nat} → Raw → Formula n → Prop where
  | refl (a : Expr n) : Principal (.refl a.encode) (.equal a a)
  | zeroLe (a : Expr n) : Principal (.zeroLe a.encode) (.less zero (.add a one))
  | decide (a b : Expr n) : a.normalize.coefficients = [] → b.normalize.coefficients = [] →
      a.normalize.constant < b.normalize.constant → a.normalize.constant < wordBound →
      b.normalize.constant < wordBound → Principal (.decide a.encode b.encode) (.less a b)
  | lam : Principal t p → Principal (.lam false .u64 t) (.all p)

theorem Principal.derives (h : Principal t p) : Derives t p := by
  induction h with
  | refl a => exact .refl a
  | zeroLe a => exact .zeroLe a
  | decide a b ha hb hl _ _ => exact .decide a b ha hb hl
  | lam _ ih => exact .lam ih

/-- Every comparison appearing in the proof has representable endpoints.
This is a property of raw syntax and structural evaluation, not of a chosen
proof derivation or the executable normalizer's behavior. -/
def DecisionBounded : Raw → Prop
  | .decide a b => (∀ ρ v, Evaluates ρ a v → v < wordBound) ∧
      (∀ ρ v, Evaluates ρ b v → v < wordBound)
  | .lam _ _ t => DecisionBounded t
  | _ => True

/-- The earlier semantic judgment connects to the selected inference rules
provided every Decide endpoint is word-representable. This condition is proved
by the new executable checker, never silently assumed for arbitrary Derives. -/
theorem derives_principal (h : Derives t p) (bounded : DecisionBounded t) :
    ∃ q, Principal t q ∧ Converts q p := by
  induction h with
  | refl a => exact ⟨_, .refl a, converts_refl _⟩
  | zeroLe a => exact ⟨_, .zeroLe a, converts_refl _⟩
  | decide a b ha hb hl =>
      have hwa := bounded.1 (fun _ => 0) _ (a.evaluates _)
      have hwb := bounded.2 (fun _ => 0) _ (b.evaluates _)
      rw [closed_value a ha] at hwa
      rw [closed_value b hb] at hwb
      exact ⟨_, .decide a b ha hb hl hwa hwb, converts_refl _⟩
  | lam _ ih =>
      obtain ⟨q, hq, hc⟩ := ih bounded
      exact ⟨.all q, .lam hq, .all hc⟩
  | convert _ hc ih =>
      obtain ⟨q, hq, hconv⟩ := ih bounded
      exact ⟨q, hq, converts_trans hconv hc⟩

theorem Principal.bounded (h : Principal t p) : DecisionBounded t := by
  induction h with
  | refl => trivial
  | zeroLe => trivial
  | decide a b ha hb _ hwa hwb =>
      constructor
      · intro ρ v hv
        have he := (a.evaluates ρ).deterministic hv
        rw [← he, closed_value a ha ρ]
        exact hwa
      · intro ρ v hv
        have he := (b.evaluates ρ).deterministic hv
        rw [← he, closed_value b hb ρ]
        exact hwb
  | lam _ ih => exact ih

/-- Exact characterization of the additional compatibility obligation. -/
theorem principal_iff : (∃ p, Principal t p ∧ Converts p q) ↔
    Derives t q ∧ DecisionBounded t := by
  constructor
  · rintro ⟨p, hp, hc⟩
    exact ⟨.convert hp.derives hc, hp.bounded⟩
  · rintro ⟨h, hb⟩
    exact derives_principal h hb

/-- Shape-only reference function. It does not authorize Decide's inequality. -/
def inferredShape : Raw → Option Raw
  | .refl a => some (.eq a a)
  | .zeroLe a => some (.lt (.natural 0) (.uadd a (.natural 1)))
  | .decide a b => some (.lt a b)
  | .lam false .u64 t => do
      let A ← inferredShape t
      pure (.pi false .u64 A)
  | _ => none

theorem Principal.shape (h : Principal t p) : inferredShape t = some p.encode := by
  induction h with
  | refl => rfl
  | zeroLe => rfl
  | decide => rfl
  | lam _ ih => simp [inferredShape, ih, Formula.encode]

theorem Principal.unique_type (h : Principal t p) (g : Principal t q) : p.encode = q.encode := by
  exact Option.some.inj (h.shape.symm.trans g.shape)

/-- Both numerical endpoints in a modeled Decide reduce to representable
Natural nodes using existing bounded contextual addition rules. -/
theorem decide_reductions (a b : Expr n) (ha : a.normalize.coefficients = [])
    (hb : b.normalize.coefficients = []) (hwa : a.normalize.constant < wordBound)
    (hwb : b.normalize.constant < wordBound) :
    Raw.Computation.Steps a.encode (.natural a.normalize.constant) ∧
    Raw.Computation.Steps b.encode (.natural b.normalize.constant) :=
  ⟨closed_reduces a ha hwa, closed_reduces b hb hwb⟩

def infer (n : Nat) : (t : Raw) → Option {p : Formula n // Principal t p}
  | .refl a => do
      let e ← extract n a
      pure ⟨.equal e.val e.val, by simpa only [e.property] using Principal.refl e.val⟩
  | .zeroLe a => do
      let e ← extract n a
      pure ⟨.less zero (.add e.val one), by simpa only [e.property] using Principal.zeroLe e.val⟩
  | .decide a b => do
      let ea ← extract n a
      let eb ← extract n b
      if ha : ea.val.normalize.coefficients = [] then
        if hb : eb.val.normalize.coefficients = [] then
          if hl : ea.val.normalize.constant < eb.val.normalize.constant then
            if hwa : ea.val.normalize.constant < wordBound then
              if hwb : eb.val.normalize.constant < wordBound then
                pure ⟨.less ea.val eb.val, by
                  simpa only [ea.property, eb.property] using
                    (Principal.decide ea.val eb.val ha hb hl hwa hwb)⟩
              else none
            else none
          else none
        else none
      else none
  | .lam false .u64 body => do
      let p ← infer (n + 1) body
      pure ⟨.all p.val, .lam p.property⟩
  | _ => none

end Jihoo.CoreBridge.CorePrincipal
