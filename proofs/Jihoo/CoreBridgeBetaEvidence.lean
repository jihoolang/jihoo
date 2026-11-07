import Jihoo.CoreBridgeBetaShapes
import Jihoo.CoreBridgeBetaPreservation

/-! Closed weak-head-normal evidence has true literal endpoints. This does NOT
prove that every typed term reaches weak head normal form, or interpret arbitrary
higher-order functions. Conversion is the unchanged untyped beta relation. -/
namespace Jihoo.CoreBridge.Raw.Beta

private def isLambda : Raw → Bool
  | .lam _ _ _ => true
  | _ => false

/-- Only the function spine is inspected. Lambda bodies and constructor indices
need not be normalized; this is explicitly not full normality or evaluation. -/
def headNormal : Raw → Bool
  | .app f _ => headNormal f && !isLambda f
  | _ => true

/-- Canonical shapes retain independently proved conversion of their indices. -/
def HeadCanonical (t A : Raw) : Prop :=
  (∀ e D C, Conv A (.pi e D C) → ∃ e' D' body, t = .lam e' D' body) ∧
  (∀ a b, Conv A (.lt a b) → ∃ m n,
    t = .decide (.natural m) (.natural n) ∧ m < n ∧
      Conv (.natural m) a ∧ Conv (.natural n) b) ∧
  (∀ a b, Conv A (.eq a b) → ∃ x, t = .refl x ∧ Conv x a ∧ Conv x b)

private theorem HeadCanonical.convert (h : HeadCanonical t A) (hc : Conv A B) :
    HeadCanonical t B := by
  exact ⟨fun e D C hp => h.1 e D C (hc.trans hp),
    fun a b hp => h.2.1 a b (hc.trans hp), fun a b hp => h.2.2 a b (hc.trans hp)⟩

private theorem inert_canonical (ht : typeHead A = some k)
    (hpi : k ≠ 5) (hlt : k ≠ 3) (heq : k ≠ 4) : HeadCanonical t A := by
  refine ⟨?_, ?_, ?_⟩
  · intro e D C hc; exact False.elim (hpi (hc.rigid_head ht rfl))
  · intro a b hc; exact False.elim (hlt (hc.rigid_head ht rfl))
  · intro a b hc; exact False.elim (heq (hc.rigid_head ht rfl))

private theorem closed_canonical : ∀ Γ t A, HasType Γ t A →
    Γ = (fun _ => none) → headNormal t = true → HeadCanonical t A := by
  intro Γ t A h
  induction h using HasType.rec (motive_1 := fun _ _ _ => True)
  case u64 | i64 | array | lt | eq | pi => trivial
  case var hx =>
    intro hΓ _
    rw [hΓ] at hx
    cases hx
  case natural => intros; exact inert_canonical rfl (by decide) (by decide) (by decide)
  case integer => intros; exact inert_canonical rfl (by decide) (by decide) (by decide)
  case uadd => intros; exact inert_canonical rfl (by decide) (by decide) (by decide)
  case usub => intros; exact inert_canonical rfl (by decide) (by decide) (by decide)
  case elements => intros; exact inert_canonical rfl (by decide) (by decide) (by decide)
  case index => intros; exact inert_canonical rfl (by decide) (by decide) (by decide)
  case decide ha hb hab =>
    intro _ _
    refine ⟨?_, ?_, ?_⟩
    · intro e D C hc; have := hc.rigid_head rfl rfl; contradiction
    · intro a b hc
      exact ⟨_, _, rfl, hab, hc.lt_injective⟩
    · intro a b hc; have := hc.rigid_head rfl rfl; contradiction
  case refl ha ih =>
    intro _ _
    refine ⟨?_, ?_, ?_⟩
    · intro e D C hc; have := hc.rigid_head rfl rfl; contradiction
    · intro a b hc; have := hc.rigid_head rfl rfl; contradiction
    · intro a b hc
      exact ⟨_, rfl, hc.eq_injective⟩
  case lam hA he hb ihA ihb =>
    intro _ _
    refine ⟨?_, ?_, ?_⟩
    · intro e D C _; exact ⟨_, _, _, rfl⟩
    · intro a b hc; have := hc.rigid_head rfl rfl; contradiction
    · intro a b hc; have := hc.rigid_head rfl rfl; contradiction
  case app hf ha ihf iha =>
    intro hΓ hn
    have hn' := Bool.and_eq_true_iff.mp hn
    obtain ⟨e, D, body, he⟩ := (ihf hΓ hn'.1).1 _ _ _ (.refl _)
    simp [he, isLambda] at hn'
  case convert ht hc ih =>
    intro hΓ hn
    exact (ih hΓ hn).convert hc

/-- No assumed output shape or semantic premise: induction is on the actual
closed typing derivation, including conversions at arbitrary positions. -/
theorem HasType.head_canonical (h : HasType (fun _ => none) t A)
    (hn : headNormal t = true) : HeadCanonical t A := closed_canonical _ _ _ h rfl hn

theorem HasType.head_literal_lt (h : HasType (fun _ => none) t (.lt (.natural m) (.natural n)))
    (hn : headNormal t = true) : m < n := by
  obtain ⟨a, b, _, hab, ha, hb⟩ := (h.head_canonical hn).2.1 _ _ (.refl _)
  simpa only [ha.natural_injective, hb.natural_injective] using hab

theorem HasType.head_literal_eq (h : HasType (fun _ => none) t (.eq (.natural m) (.natural n)))
    (hn : headNormal t = true) : m = n := by
  obtain ⟨_, _, ha, hb⟩ := (h.head_canonical hn).2.2 _ _ (.refl _)
  exact (ha.symm.trans hb).natural_injective

/-- This assumption is a finite reduction witness, not universal normalization. -/
theorem HasType.reduces_literal_lt
    (h : HasType (fun _ => none) t (.lt (.natural m) (.natural n)))
    (hs : Steps t u) (hn : headNormal u = true) : m < n :=
  (h.preservation_steps hs).head_literal_lt hn

theorem HasType.reduces_literal_eq
    (h : HasType (fun _ => none) t (.eq (.natural m) (.natural n)))
    (hs : Steps t u) (hn : headNormal u = true) : m = n :=
  (h.preservation_steps hs).head_literal_eq hn

end Jihoo.CoreBridge.Raw.Beta
