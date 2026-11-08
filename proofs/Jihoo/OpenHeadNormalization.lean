import Jihoo.CoreBridgeClosedNormalization

/-! Open head normalization by closing substitution and accessibility reflection.
This is for the existing head-beta relation only. It does not normalize under
lambdas, interpret arithmetic indices, or verify Core.normal or source aliases. -/
namespace Jihoo.CoreBridge.Raw.Beta.SimpleErasure

namespace Term

theorem subst_instantiate (body a : Term) (σ : Nat → Term) :
    (body.subst (single a)).subst σ =
      (body.subst (liftSub σ)).subst (single (a.subst σ)) := by
  rw [instantiate_lift, subst_composition]
  congr 1
  funext x
  cases x <;> rfl

/-- Closed inhabitants are used only in the simple erasure, where every base
sort has atom. This is not inhabitation of arbitrary dependent propositions. -/
def inhabit : Ty → Term
  | .base => .atom
  | .arrow _ b => .lam (inhabit b)

theorem inhabit_subst (a : Ty) (σ : Nat → Term) : (inhabit a).subst σ = inhabit a := by
  induction a generalizing σ with
  | base => rfl
  | arrow a b _ ih => simp only [inhabit, subst, ih]

theorem inhabit_reducible (a : Ty) : Reducible a (inhabit a) := by
  induction a with
  | base =>
      refine ⟨.atom, .refl, ?_⟩
      intro u h
      cases h
  | arrow a b _ ih =>
      refine ⟨inhabit b, .refl, ?_⟩
      intro u _
      simpa only [inhabit_subst] using ih

end Term

theorem SimpleStep.substitution (h : SimpleStep t u) (σ : Nat → Term) :
    SimpleStep (t.subst σ) (u.subst σ) := by
  induction h with
  | beta =>
      simp only [Term.subst, Term.subst_instantiate]
      exact .beta
  | function _ ih => exact .function ih

/-- Every original head step remains a genuine step after substitution.
Substitution may introduce additional redexes; no converse simulation is used. -/
theorem substitution_accessibility (h : Acc (fun u v => SimpleStep v u) (t.subst σ)) :
    Acc (fun u v => SimpleStep v u) t := by
  generalize he : t.subst σ = v at h
  induction h generalizing t with
  | intro v _ ih =>
      constructor
      intro u hs
      exact ih (u.subst σ) (by simpa only [he] using hs.substitution σ) rfl

def closingSubstitution (Δ : Context) (x : Nat) : Term :=
  match Δ x with
  | some a => Term.inhabit a
  | none => .atom

theorem closing_reducible (Δ : Context) : ReducibleSubstitution Δ (closingSubstitution Δ) := by
  intro x a hx
  simpa only [closingSubstitution, hx] using Term.inhabit_reducible a

/-- No closedness or inhabitation assumption on the original simple context. -/
theorem Typed.accessible (h : Typed Δ t a) : Acc (fun u v => SimpleStep v u) t := by
  have hn := (h.reducible_substitution (closing_reducible Δ)).normalizes
  obtain ⟨u, steps, normal⟩ := hn
  exact substitution_accessibility (steps.accessible normal)

end Jihoo.CoreBridge.Raw.Beta.SimpleErasure

namespace Jihoo.CoreBridge.Raw.Beta
open SimpleErasure

/-- A finite dependent telescope. Each new domain must be formed in the
preceding context; arbitrary raw context entries are not silently admitted. -/
inductive FormedContext : Raw.Context → Prop where
  | empty : FormedContext (fun _ => none)
  | extend : FormedContext Γ → IsType Γ A → FormedContext (Γ.extend A)

theorem FormedContext.simple_context (h : FormedContext Γ) :
    ∃ Δ, SimpleErasure.ContextMatch Γ Δ := by
  induction h with
  | empty => exact ⟨fun _ => none, fun _ _ hx => by cases hx⟩
  | extend _ hA ih =>
      obtain ⟨Δ, hm⟩ := ih
      obtain ⟨a, ha⟩ := formed_shape hA
      exact ⟨Δ.extend a, hm.extend ha.arity⟩

/-- Open contexts need conversion-stable simple arities, not semantic
inhabitants of their propositions or an assumption of normalization. -/
theorem HasType.head_accessible_of_match (h : HasType Γ t A) (hm : SimpleErasure.ContextMatch Γ Δ) :
    Acc (fun u v => HeadStep v u) t := by
  obtain ⟨a, _, typed⟩ := typed_erasure h hm
  exact accessibility_transfer typed.accessible

theorem HasType.head_accessible (h : HasType Γ t A) (hΓ : FormedContext Γ) :
    Acc (fun u v => HeadStep v u) t := by
  obtain ⟨Δ, hm⟩ := hΓ.simple_context
  exact h.head_accessible_of_match hm

theorem HasType.head_normalizes (h : HasType Γ t A) (hΓ : FormedContext Γ) :
    ∃ u, Steps t u ∧ headNormal u = true :=
  head_accessible_normalizes (h.head_accessible hΓ)

/-- Normalization does not lose the original dependent type. -/
theorem HasType.typed_head_normalizes (h : HasType Γ t A) (hΓ : FormedContext Γ) :
    ∃ u, Steps t u ∧ headNormal u = true ∧ HasType Γ u A := by
  obtain ⟨u, steps, normal⟩ := h.head_normalizes hΓ
  exact ⟨u, steps, normal, h.preservation_steps steps⟩

end Jihoo.CoreBridge.Raw.Beta
