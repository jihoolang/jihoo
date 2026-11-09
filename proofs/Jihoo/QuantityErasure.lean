import Jihoo.QuantitySubstitution

/-! Erasure and binder-slot compaction in the ownership control semantics.
This is not a translation of native Core or MIR. Binder modes must already be
justified; the transformation must only be used after quantity checking. -/
namespace Jihoo.Quantity.Erasure
open Substitution

/-- Remove ghost computations and erased binder slots. Other slots, including
borrowed and unrestricted ones, retain their identity. -/
def erase : Control → Control
  | .pure => .pure
  | .trap => .trap
  | .use k => .use k
  | .seq a b => .seq (erase a) (erase b)
  | .branch a b => .branch (erase a) (erase b)
  | .repeat b => .repeat (erase b)
  | .once b => .once (erase b)
  | .closure b => .closure (erase b)
  | .erased _ => .pure
  | .scope .erased b => (erase b).relabel dropBorrow
  | .scope m b => .scope m (erase b)

private theorem lift_compose (ρ τ : PartialMap) :
    liftPartial (fun k => (ρ k).bind τ) =
      fun k => (liftPartial ρ k).bind (liftPartial τ) := by
  funext k; cases k with
  | zero => rfl
  | succ k => cases h : ρ k <;> simp [liftPartial, h]

/-- Partial renamings compose under retained binder slots. -/
theorem relabel_compose (c : Control) (ρ τ : PartialMap) :
    (c.relabel ρ).relabel τ = c.relabel (fun k => (ρ k).bind τ) := by
  induction c generalizing ρ τ with
  | use k => cases h : ρ k <;> simp [Control.relabel, h]
  | _ => simp_all [Control.relabel, lift_compose]

private theorem drop_lift (ρ : PartialMap) :
    (fun k => (liftPartial ρ k).bind dropBorrow) =
      fun k => (dropBorrow k).bind ρ := by
  funext k; cases k with
  | zero => rfl
  | succ k => cases h : ρ k <;> simp [liftPartial, dropBorrow, h]

/-- Slot compaction commutes with capture-avoiding replacement of outer names,
including removal of a borrowed ownership event. -/
theorem erase_relabel (c : Control) (ρ : PartialMap) :
    erase (c.relabel ρ) = (erase c).relabel ρ := by
  induction c generalizing ρ with
  | use k => cases h : ρ k <;> simp [Control.relabel, erase, h]
  | scope mode b ih =>
      cases mode <;> simp [Control.relabel, erase, ih, relabel_compose, drop_lift]
  | _ => simp_all [Control.relabel, erase]

/-- Compose the existing annotated-source substitution theorem with erasure.
Only variable/borrow substitutions are covered; mode stability is assumed by
that source representation, not derived from arbitrary native Core typing. -/
theorem substitution_erasure {e out : Expr} {σ : Nat → Atom}
    (h : e.subst σ = some out) :
    erase out.project = (erase e.project).relabel (fun k => (σ k).event) := by
  rw [substitution_projection h, erase_relabel]

/-- Successful checking is preserved for every remaining resource. No converse
is claimed: deleting an ill-used ghost slot can conceal the original error. -/
theorem demand_preserved (c : Control) (h : c.demand r = some n) :
    (erase c).demand r = some n := by
  induction c generalizing r n with
  | pure | trap | use | erased => exact h
  | seq a b ia ib =>
      simp only [Control.demand] at h
      cases ha : a.demand r <;> cases hb : b.demand r <;> simp_all [erase, Control.demand]
  | branch a b ia ib =>
      simp only [Control.demand] at h
      cases ha : a.demand r <;> cases hb : b.demand r <;> simp_all [erase, Control.demand]
  | «repeat» b ih | closure b ih =>
      simp only [Control.demand] at h
      cases hb : b.demand r <;> simp_all [erase, Control.demand]
  | once b ih => exact ih h
  | scope mode b ih =>
      cases mode with
      | erased =>
          simp only [Control.demand] at h
          cases hb : b.demand 0 <;> simp_all [erase, drop_borrow_demand, Control.demand]
      | linear =>
          simp only [Control.demand] at h
          cases hb : b.demand 0 <;> simp_all [erase, Control.demand]
      | unrestricted | borrowed => exact ih h

/-- All complete source traces survive erasure with the same outer identities. -/
theorem finishes_forward (h : Finishes c xs) : Finishes (erase c) xs := by
  induction h with
  | pure => exact .pure
  | use => exact .use
  | seq _ _ ia ib => exact .seq ia ib
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | repeatZero => exact .repeatZero
  | repeatNext _ _ ia ib => exact .repeatNext ia ib
  | once _ ih => exact .once ih
  | closure => exact .closure
  | erased => exact .pure
  | @bind b xs mode _ ih =>
      cases mode with
      | erased => simpa only [erase, drop_borrow_trace] using ih.relabel dropBorrow
      | linear | unrestricted | borrowed => exact .bind ih

/-- Includes prefixes ending at a trap and finite observations of divergence. -/
theorem prefix_forward (h : Prefix c xs) : Prefix (erase c) xs := by
  induction h with
  | start => exact .start
  | use => exact .use
  | seqLeft _ ih => exact .seqLeft ih
  | seqRight ha _ ih => exact .seqRight (finishes_forward ha) ih
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | repeatNext ha _ ih => exact .repeatNext (finishes_forward ha) ih
  | repeatBody _ ih => exact .repeatBody ih
  | once _ ih => exact .once ih
  | @bind b xs mode _ ih =>
      cases mode with
      | erased => simpa only [erase, drop_borrow_trace] using ih.relabel dropBorrow
      | linear | unrestricted | borrowed => exact .bind ih

/-- Quantifies over ALL target executions, not just translated source runs. -/
theorem finished_count (checked : c.demand r = some n)
    (run : Finishes (erase c) xs) : xs.count r = n :=
  run.count_eq (demand_preserved c checked)

theorem prefix_count (checked : c.demand r = some n)
    (run : Prefix (erase c) xs) : xs.count r ≤ n :=
  run.count_le (demand_preserved c checked)

theorem linear_finished (checked : Linear resources c)
    (run : Finishes (erase c) xs) : ∀ r ∈ resources, xs.count r = 1 :=
  fun r hr => finished_count (checked r hr) run

theorem linear_prefix (checked : Linear resources c)
    (run : Prefix (erase c) xs) : ∀ r ∈ resources, xs.count r ≤ 1 :=
  fun r hr => prefix_count (checked r hr) run

end Jihoo.Quantity.Erasure
