import Jihoo.CoreBridgeSimpleSimulation

/-! A logical-relations proof of closed simply typed head normalization.
The relation stops at lambdas and atoms. It does not normalize lambda bodies,
arguments, annotations, arithmetic, arrays or evidence contents. -/
namespace Jihoo.CoreBridge.Raw.Beta.SimpleErasure

namespace Term

/-- Used only to transfer the already proved substitution algebra through
`erase`; it has no typing, scalar-value or compiler-refinement significance. -/
private def represent : Term → Raw
  | .atom => .natural 0
  | .var x => .var x
  | .lam b => .lam false .u64 (represent b)
  | .app f a => .app (represent f) (represent a)

private theorem erase_represent (t : Term) : erase (represent t) = t := by
  induction t <;> simp_all [represent, erase]

theorem subst_identity (t : Term) : t.subst Term.var = t := by
  have h := congrArg erase (Raw.subst_id (represent t))
  simpa only [erase_substitution, erase_represent, erase] using h

theorem subst_composition (t : Term) (σ τ : Nat → Term) :
    (t.subst σ).subst τ = t.subst (fun x => (σ x).subst τ) := by
  have h := congrArg erase (Raw.subst_comp (represent t)
    (fun x => represent (σ x)) (fun x => represent (τ x)))
  simpa only [erase_substitution, erase_represent] using h

theorem shift_instantiate (t a : Term) : (t.rename Nat.succ).subst (single a) = t := by
  have h := congrArg erase (Raw.subst_shift (represent t) (represent a))
  rw [erase_instantiate, erase_renaming] at h
  simpa only [erase_represent] using h

def extendSub (a : Term) (σ : Nat → Term) : Nat → Term
  | 0 => a
  | n + 1 => σ n

theorem instantiate_lift (t a : Term) (σ : Nat → Term) :
    (t.subst (liftSub σ)).subst (single a) = t.subst (extendSub a σ) := by
  rw [subst_composition]
  congr 1
  funext x
  cases x with
  | zero => rfl
  | succ x => exact shift_instantiate (σ x) a

end Term

inductive Star : Term → Term → Prop where
  | refl : Star t t
  | next : SimpleStep t u → Star u v → Star t v

theorem Star.trans (h : Star t u) (h' : Star u v) : Star t v := by
  induction h with
  | refl => exact h'
  | next hs _ ih => exact .next hs (ih h')

theorem Star.function (h : Star f g) : Star (.app f a) (.app g a) := by
  induction h with
  | refl => exact .refl
  | next hs _ ih => exact .next (.function hs) ih

def Normal (t : Term) : Prop := ∀ u, ¬ SimpleStep t u

def Normalizes (t : Term) : Prop := ∃ u, Star t u ∧ Normal u

private theorem normal_atom : Normal .atom := by intro u h; cases h
private theorem normal_lam : Normal (.lam body) := by intro u h; cases h

/-- Function reducibility retains a concrete lambda body and requires reducible
results for every reducible argument. No normalization premise is a typing rule. -/
def Reducible : Ty → Term → Prop
  | .base, t => Normalizes t
  | .arrow a b, t => ∃ body, Star t (.lam body) ∧
      ∀ u, Reducible a u → Reducible b (body.subst (Term.single u))

theorem Reducible.normalizes (h : Reducible a t) : Normalizes t := by
  cases a with
  | base => exact h
  | arrow a b =>
      obtain ⟨body, steps, _⟩ := h
      exact ⟨.lam body, steps, normal_lam⟩

theorem Reducible.expansion (h : Reducible a u) (hs : Star t u) : Reducible a t := by
  cases a with
  | base =>
      obtain ⟨v, hv, hn⟩ := h
      exact ⟨v, hs.trans hv, hn⟩
  | arrow a b =>
      obtain ⟨body, steps, hb⟩ := h
      exact ⟨body, hs.trans steps, hb⟩

theorem Reducible.application (hf : Reducible (.arrow a b) f) (hu : Reducible a u) :
    Reducible b (.app f u) := by
  obtain ⟨body, steps, hb⟩ := hf
  exact (hb u hu).expansion (steps.function.trans (.next .beta .refl))

def ReducibleSubstitution (Δ : Context) (σ : Nat → Term) : Prop :=
  ∀ x a, Δ x = some a → Reducible a (σ x)

theorem ReducibleSubstitution.extend (h : ReducibleSubstitution Δ σ) (ha : Reducible a u) :
    ReducibleSubstitution (Δ.extend a) (Term.extendSub u σ) := by
  intro x b hx
  cases x with
  | zero =>
      simp only [Context.extend, Option.some.injEq] at hx
      subst b
      exact ha
  | succ x => exact h x b hx

/-- Fundamental lemma by the existing simple typing derivation. Higher-order
arguments are handled by the arrow clause of the logical relation. -/
theorem Typed.reducible_substitution (h : Typed Δ t a) (hs : ReducibleSubstitution Δ σ) :
    Reducible a (t.subst σ) := by
  induction h generalizing σ with
  | atom => exact ⟨.atom, .refl, normal_atom⟩
  | var hx => exact hs _ _ hx
  | lam hb ih =>
      refine ⟨_, .refl, ?_⟩
      intro u hu
      rw [Term.instantiate_lift]
      exact ih (hs.extend hu)
  | app hf hx ihf ihx => exact (ihf hs).application (ihx hs)

theorem Typed.closed_normalizes (h : Typed (fun _ => none) t a) : Normalizes t := by
  have hr := h.reducible_substitution (σ := Term.var) (fun _ _ hx => by cases hx)
  rw [Term.subst_identity] at hr
  exact hr.normalizes

/-- Head beta is deterministic; weak normalization therefore supplies
accessibility of this relation, not merely one terminating reduction choice. -/
theorem SimpleStep.deterministic (h : SimpleStep t u) (h' : SimpleStep t v) : u = v := by
  induction h generalizing v with
  | beta =>
      cases h' with
      | beta => rfl
      | function hf => cases hf
  | function hf ih =>
      cases h' with
      | beta => cases hf
      | function hg => exact congrArg (fun f => Term.app f _) (ih hg)

theorem Star.accessible (h : Star t u) (hn : Normal u) : Acc (fun u v => SimpleStep v u) t := by
  induction h with
  | refl =>
      constructor
      intro v hv
      exact False.elim (hn v hv)
  | next hs _ ih =>
      constructor
      intro v hv
      have he := hs.deterministic hv
      subst v
      exact ih hn

theorem Typed.closed_accessible (h : Typed (fun _ => none) t a) :
    Acc (fun u v => SimpleStep v u) t := by
  obtain ⟨u, steps, hn⟩ := h.closed_normalizes
  exact steps.accessible hn

end Jihoo.CoreBridge.Raw.Beta.SimpleErasure
