import Jihoo.CoreBridgeSimpleErasure

namespace Jihoo.CoreBridge.Raw.Beta.SimpleErasure

namespace Term

def rename (ρ : Nat → Nat) : Term → Term
  | .atom => .atom
  | .var x => .var (ρ x)
  | .lam body => .lam (rename (Jihoo.Indexed.liftRenaming ρ) body)
  | .app f a => .app (rename ρ f) (rename ρ a)

def liftSub (σ : Nat → Term) : Nat → Term
  | 0 => .var 0
  | n + 1 => (σ n).rename Nat.succ

def single (a : Term) : Nat → Term
  | 0 => a
  | n + 1 => .var n

def subst (σ : Nat → Term) : Term → Term
  | .atom => .atom
  | .var x => σ x
  | .lam body => .lam (subst (liftSub σ) body)
  | .app f a => .app (subst σ f) (subst σ a)

end Term

theorem erase_renaming (t : Raw) (ρ : Nat → Nat) :
    erase (t.rename ρ) = (erase t).rename ρ := by
  induction t using Raw.rec (motive_2 := fun _ => True) generalizing ρ <;>
    simp_all [Raw.rename, erase, Term.rename]

private theorem erase_lift (σ : Nat → Raw) :
    (fun x => erase (Raw.liftSub σ x)) = Term.liftSub (fun x => erase (σ x)) := by
  funext x
  cases x <;> simp [Raw.liftSub, Term.liftSub, erase, erase_renaming]

theorem erase_substitution (t : Raw) (σ : Nat → Raw) :
    erase (t.subst σ) = (erase t).subst (fun x => erase (σ x)) := by
  induction t using Raw.rec (motive_2 := fun _ => True) generalizing σ <;>
    simp_all [Raw.subst, erase, Term.subst, erase_lift]

theorem erase_instantiate (body a : Raw) :
    erase (body.subst (Raw.single a)) = (erase body).subst (Term.single (erase a)) := by
  rw [erase_substitution]
  congr 1
  funext x
  cases x <;> rfl

/-- Only root beta and its function-spine closure. Reducing inside an erased
constructor or annotation is intentionally not a step of this relation. -/
inductive HeadStep : Raw → Raw → Prop where
  | beta : HeadStep (.app (.lam e A body) a) (body.subst (Raw.single a))
  | function : HeadStep f g → HeadStep (.app f a) (.app g a)

inductive SimpleStep : Term → Term → Prop where
  | beta : SimpleStep (.app (.lam body) a) (body.subst (Term.single a))
  | function : SimpleStep f g → SimpleStep (.app f a) (.app g a)

theorem HeadStep.beta_step (h : HeadStep t u) : Beta.Step t u := by
  induction h with
  | beta => exact .beta _ _ _ _
  | function _ ih => exact .appFunction ih

/-- Each head beta step is one genuine simple beta step, not zero steps.
This is the direction needed to transfer a future termination theorem. -/
theorem HeadStep.simulation (h : HeadStep t u) : SimpleStep (erase t) (erase u) := by
  induction h with
  | beta => simpa only [erase, erase_instantiate] using (SimpleStep.beta (body := erase _) (a := erase _))
  | function _ ih => exact .function ih

inductive SimpleSteps : Nat → Term → Term → Prop where
  | refl : SimpleSteps 0 t t
  | next : SimpleStep t u → SimpleSteps n u v → SimpleSteps (n + 1) t v

/-- Conditional accessibility transfer. Accessibility of simply typed terms is
not assumed or proved here; it remains a separate normalization obligation. -/
theorem accessibility_transfer (h : Acc (fun u v => SimpleStep v u) (erase t)) :
    Acc (fun u v => HeadStep v u) t := by
  generalize he : erase t = v at h
  induction h generalizing t with
  | intro v h ih =>
      constructor
      intro u hs
      apply ih (erase u) (by simpa only [he] using hs.simulation) rfl

end Jihoo.CoreBridge.Raw.Beta.SimpleErasure
