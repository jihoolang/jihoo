import Jihoo.CoreBridgeSubstitutionAlgebra

/-! Structural metatheory for the existing independent target judgment. No
conversion or typing rules are added. Context morphisms state exactly how
current-scope entries move; no regularity of arbitrary contexts is assumed. -/
namespace Jihoo.CoreBridge.Raw

open Jihoo.Indexed (liftRenaming)

/-- Renamings preserve each existing current-scope lookup and its type. -/
def Renaming (Γ Δ : Context) (ρ : Nat → Nat) : Prop :=
  ∀ x A, Γ x = some A → Δ (ρ x) = some (A.rename ρ)

/-- Every substituted variable has its substituted current-scope type. -/
def Substitution (Γ Δ : Context) (σ : Nat → Raw) : Prop :=
  ∀ x A, Γ x = some A → HasType Δ (σ x) (A.subst σ)

theorem Conv.renaming (h : Conv A B) (ρ : Nat → Nat) :
    Conv (A.rename ρ) (B.rename ρ) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | add a b bound => simpa only [rename] using Conv.add a b bound
  | lt _ _ ih₁ ih₂ => simpa only [rename] using Conv.lt ih₁ ih₂
  | eq _ _ ih₁ ih₂ => simpa only [rename] using Conv.eq ih₁ ih₂
  | array _ ih => simpa only [rename] using Conv.array ih

theorem Conv.substitution (h : Conv A B) (σ : Nat → Raw) :
    Conv (A.subst σ) (B.subst σ) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | add a b bound => simpa only [subst] using Conv.add a b bound
  | lt _ _ ih₁ ih₂ => simpa only [subst] using Conv.lt ih₁ ih₂
  | eq _ _ ih₁ ih₂ => simpa only [subst] using Conv.eq ih₁ ih₂
  | array _ ih => simpa only [subst] using Conv.array ih

/-- This needs formation: substituting for an arbitrary Raw variable can change
its proposition classification. Only the codomain of a formed Pi recurses. -/
theorem IsType.proposition_subst (h : IsType Γ A) (σ : Nat → Raw) :
    (A.subst σ).proposition = A.proposition := by
  induction A using Raw.rec (motive_2 := fun _ => True) generalizing Γ σ <;>
    first | trivial | (cases h <;> simp_all [subst, proposition])
  case pi.pi _ _ _ _ ih _ _ hB => exact ih hB _


theorem Renaming.lift (hρ : Renaming Γ Δ ρ) (A : Raw) :
    Renaming (Γ.extend A) (Δ.extend (A.rename ρ)) (liftRenaming ρ) := by
  intro x B hx
  cases x with
  | zero =>
      simp only [Context.extend, Option.some.injEq] at hx
      subst B
      simp only [liftRenaming, Context.extend, rename_comp]
  | succ x =>
      simp only [Context.extend, Option.map_eq_some_iff] at hx
      obtain ⟨B, hb, rfl⟩ := hx
      simp only [liftRenaming, Context.extend, hρ x B hb, Option.map_some, rename_comp]

private theorem renaming_mutual :
    (∀ Γ A, IsType Γ A → ∀ Δ ρ, Renaming Γ Δ ρ → IsType Δ (A.rename ρ)) ∧
    (∀ Γ t A, HasType Γ t A → ∀ Δ ρ, Renaming Γ Δ ρ →
      HasType Δ (t.rename ρ) (A.rename ρ)) := by
  constructor
  · intro Γ A h
    induction h using IsType.rec
      (motive_2 := fun Γ t A _ => ∀ Δ ρ, Renaming Γ Δ ρ →
        HasType Δ (t.rename ρ) (A.rename ρ))
    case u64 =>
      intro Δ ρ hρ
      simpa only [rename] using (IsType.u64 (Γ := Δ))
    case i64 =>
      intro Δ ρ hρ
      simpa only [rename] using (IsType.i64 (Γ := Δ))
    case array hn ih =>
      intro Δ ρ hρ
      simp only [rename]
      exact .array (by simpa only [rename] using ih Δ ρ hρ)
    case lt ha hb iha ihb =>
      intro Δ ρ hρ
      simp only [rename]
      exact .lt (by simpa only [rename] using iha Δ ρ hρ)
        (by simpa only [rename] using ihb Δ ρ hρ)
    case eq ha hb iha ihb =>
      intro Δ ρ hρ
      simp only [rename]
      exact .eq (by simpa only [rename] using iha Δ ρ hρ)
        (by simpa only [rename] using ihb Δ ρ hρ)
    case pi hA he hB ihA ihB =>
      intro Δ ρ hρ
      simp only [rename]
      exact .pi (ihA Δ ρ hρ) (by simpa only [proposition_rename] using he)
        (ihB _ _ (hρ.lift _))
    case var hx Δ ρ hρ => simpa only [rename] using HasType.var (hρ _ _ hx)
    case natural hn Δ ρ hρ => simpa only [rename] using (HasType.natural (Γ := Δ) hn)
    case integer hlo hhi Δ ρ hρ => simpa only [rename] using (HasType.integer (Γ := Δ) hlo hhi)
    case uadd ha hb iha ihb Δ ρ hρ =>
      simp only [rename]
      exact .uadd (by simpa only [rename] using iha Δ ρ hρ)
        (by simpa only [rename] using ihb Δ ρ hρ)
    case usub ha hb hp iha ihb ihp Δ ρ hρ =>
      simp only [rename]
      exact .usub (by simpa only [rename] using iha Δ ρ hρ)
        (by simpa only [rename] using ihb Δ ρ hρ)
        (by simpa only [rename] using ihp Δ ρ hρ)
    case elements xs Γ hs hlen ih Δ ρ hρ =>
      simp only [rename]
      have ht := HasType.elements (Γ := Δ) (xs := xs.map (rename ρ))
        (fun y hy => ?_) (by simpa only [List.length_map] using hlen)
      · simpa only [List.length_map] using ht
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        simpa only [rename] using ih x hx Δ ρ hρ
    case decide ha hb hab Δ ρ hρ => simpa only [rename] using (HasType.decide (Γ := Δ) ha hb hab)
    case refl ha ih Δ ρ hρ =>
      simp only [rename]
      exact .refl (by simpa only [rename] using ih Δ ρ hρ)
    case index ha hi hp iha ihi ihp Δ ρ hρ =>
      simp only [rename]
      exact .index (by simpa only [rename] using iha Δ ρ hρ)
        (by simpa only [rename] using ihi Δ ρ hρ)
        (by simpa only [rename] using ihp Δ ρ hρ)
    case lam hA he hb ihA ihb Δ ρ hρ =>
      simp only [rename]
      exact .lam (ihA Δ ρ hρ) (by simpa only [proposition_rename] using he)
        (ihb _ _ (hρ.lift _))
    case app hf ha ihf iha Δ ρ hρ =>
      simp only [rename, rename_instantiate]
      exact .app (by simpa only [rename] using ihf Δ ρ hρ) (iha Δ ρ hρ)
    case convert ht hc ih Δ ρ hρ => exact .convert (ih Δ ρ hρ) (hc.renaming ρ)
  · intro Γ t A h
    induction h using HasType.rec
      (motive_1 := fun Γ A _ => ∀ Δ ρ, Renaming Γ Δ ρ → IsType Δ (A.rename ρ))
    case u64 Δ ρ hρ => simpa only [rename] using (IsType.u64 (Γ := Δ))
    case i64 Δ ρ hρ => simpa only [rename] using (IsType.i64 (Γ := Δ))
    case array hn ih Δ ρ hρ =>
      simp only [rename]
      exact .array (by simpa only [rename] using ih Δ ρ hρ)
    case lt ha hb iha ihb Δ ρ hρ =>
      simp only [rename]
      exact .lt (by simpa only [rename] using iha Δ ρ hρ)
        (by simpa only [rename] using ihb Δ ρ hρ)
    case eq ha hb iha ihb Δ ρ hρ =>
      simp only [rename]
      exact .eq (by simpa only [rename] using iha Δ ρ hρ)
        (by simpa only [rename] using ihb Δ ρ hρ)
    case pi hA he hB ihA ihB Δ ρ hρ =>
      simp only [rename]
      exact .pi (ihA Δ ρ hρ) (by simpa only [proposition_rename] using he)
        (ihB _ _ (hρ.lift _))
    case var hx =>
      intro Δ ρ hρ
      simpa only [rename] using HasType.var (hρ _ _ hx)
    case natural hn =>
      intro Δ ρ hρ
      simpa only [rename] using (HasType.natural (Γ := Δ) hn)
    case integer hlo hhi =>
      intro Δ ρ hρ
      simpa only [rename] using (HasType.integer (Γ := Δ) hlo hhi)
    case uadd ha hb iha ihb =>
      intro Δ ρ hρ
      simp only [rename]
      exact .uadd (by simpa only [rename] using iha Δ ρ hρ)
        (by simpa only [rename] using ihb Δ ρ hρ)
    case usub ha hb hp iha ihb ihp =>
      intro Δ ρ hρ
      simp only [rename]
      exact .usub (by simpa only [rename] using iha Δ ρ hρ)
        (by simpa only [rename] using ihb Δ ρ hρ)
        (by simpa only [rename] using ihp Δ ρ hρ)
    case elements xs Γ hs hlen ih =>
      intro Δ ρ hρ
      simp only [rename]
      have ht := HasType.elements (Γ := Δ) (xs := xs.map (rename ρ))
        (fun y hy => ?_) (by simpa only [List.length_map] using hlen)
      · simpa only [List.length_map] using ht
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        simpa only [rename] using ih x hx Δ ρ hρ
    case decide ha hb hab =>
      intro Δ ρ hρ
      simpa only [rename] using (HasType.decide (Γ := Δ) ha hb hab)
    case refl ha ih =>
      intro Δ ρ hρ
      simp only [rename]
      exact .refl (by simpa only [rename] using ih Δ ρ hρ)
    case index ha hi hp iha ihi ihp =>
      intro Δ ρ hρ
      simp only [rename]
      exact .index (by simpa only [rename] using iha Δ ρ hρ)
        (by simpa only [rename] using ihi Δ ρ hρ)
        (by simpa only [rename] using ihp Δ ρ hρ)
    case lam hA he hb ihA ihb =>
      intro Δ ρ hρ
      simp only [rename]
      exact .lam (ihA Δ ρ hρ) (by simpa only [proposition_rename] using he)
        (ihb _ _ (hρ.lift _))
    case app hf ha ihf iha =>
      intro Δ ρ hρ
      simp only [rename, rename_instantiate]
      exact .app (by simpa only [rename] using ihf Δ ρ hρ) (iha Δ ρ hρ)
    case convert ht hc ih =>
      intro Δ ρ hρ
      exact .convert (ih Δ ρ hρ) (hc.renaming ρ)
/-- Joint transport includes formation of dependent domains and codomains. -/
theorem IsType.renaming (h : IsType Γ A) (hρ : Renaming Γ Δ ρ) :
    IsType Δ (A.rename ρ) := renaming_mutual.1 _ _ h _ _ hρ

theorem HasType.renaming (h : HasType Γ t A) (hρ : Renaming Γ Δ ρ) :
    HasType Δ (t.rename ρ) (A.rename ρ) := renaming_mutual.2 _ _ _ h _ _ hρ

/-- Extension weakens the new annotation and every old entry alike. -/
theorem Renaming.weaken (Γ : Context) (A : Raw) :
    Renaming Γ (Γ.extend A) Nat.succ := by
  intro x B hx
  simp only [Context.extend, hx, Option.map_some]

theorem HasType.weaken (h : HasType Γ t B) (A : Raw) :
    HasType (Γ.extend A) (t.rename Nat.succ) (B.rename Nat.succ) :=
  h.renaming (Renaming.weaken Γ A)

theorem Substitution.lift (hσ : Substitution Γ Δ σ) (A : Raw) :
    Substitution (Γ.extend A) (Δ.extend (A.subst σ)) (liftSub σ) := by
  intro x B hx
  cases x with
  | zero =>
      simp only [Context.extend, Option.some.injEq] at hx
      subst B
      rw [shift_subst_lift]
      exact .var rfl
  | succ x =>
      simp only [Context.extend, Option.map_eq_some_iff] at hx
      obtain ⟨B, hb, rfl⟩ := hx
      rw [shift_subst_lift]
      exact (hσ x B hb).weaken (A.subst σ)

private theorem substitution_mutual :
    (∀ Γ A, IsType Γ A → ∀ Δ σ, Substitution Γ Δ σ → IsType Δ (A.subst σ)) ∧
    (∀ Γ t A, HasType Γ t A → ∀ Δ σ, Substitution Γ Δ σ →
      HasType Δ (t.subst σ) (A.subst σ)) := by
  constructor
  · intro Γ A h
    induction h using IsType.rec
      (motive_2 := fun Γ t A _ => ∀ Δ σ, Substitution Γ Δ σ →
        HasType Δ (t.subst σ) (A.subst σ))
    case u64 =>
      intro Δ σ hσ
      simpa only [subst] using (IsType.u64 (Γ := Δ))
    case i64 =>
      intro Δ σ hσ
      simpa only [subst] using (IsType.i64 (Γ := Δ))
    case array hn ih =>
      intro Δ σ hσ
      simp only [subst]
      exact .array (by simpa only [subst] using ih Δ σ hσ)
    case lt ha hb iha ihb =>
      intro Δ σ hσ
      simp only [subst]
      exact .lt (by simpa only [subst] using iha Δ σ hσ)
        (by simpa only [subst] using ihb Δ σ hσ)
    case eq ha hb iha ihb =>
      intro Δ σ hσ
      simp only [subst]
      exact .eq (by simpa only [subst] using iha Δ σ hσ)
        (by simpa only [subst] using ihb Δ σ hσ)
    case pi hA he hB ihA ihB =>
      intro Δ σ hσ
      simp only [subst]
      exact .pi (ihA Δ σ hσ) (by simpa only [hA.proposition_subst σ] using he)
        (ihB _ _ (hσ.lift _))
    case var hx Δ σ hσ => simpa only [subst] using hσ _ _ hx
    case natural hn Δ σ hσ => simpa only [subst] using (HasType.natural (Γ := Δ) hn)
    case integer hlo hhi Δ σ hσ => simpa only [subst] using (HasType.integer (Γ := Δ) hlo hhi)
    case uadd ha hb iha ihb Δ σ hσ =>
      simp only [subst]
      exact .uadd (by simpa only [subst] using iha Δ σ hσ)
        (by simpa only [subst] using ihb Δ σ hσ)
    case usub ha hb hp iha ihb ihp Δ σ hσ =>
      simp only [subst]
      exact .usub (by simpa only [subst] using iha Δ σ hσ)
        (by simpa only [subst] using ihb Δ σ hσ)
        (by simpa only [subst] using ihp Δ σ hσ)
    case elements xs Γ hs hlen ih Δ σ hσ =>
      simp only [subst]
      have ht := HasType.elements (Γ := Δ) (xs := xs.map (subst σ))
        (fun y hy => ?_) (by simpa only [List.length_map] using hlen)
      · simpa only [List.length_map] using ht
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        simpa only [subst] using ih x hx Δ σ hσ
    case decide ha hb hab Δ σ hσ => simpa only [subst] using (HasType.decide (Γ := Δ) ha hb hab)
    case refl ha ih Δ σ hσ =>
      simp only [subst]
      exact .refl (by simpa only [subst] using ih Δ σ hσ)
    case index ha hi hp iha ihi ihp Δ σ hσ =>
      simp only [subst]
      exact .index (by simpa only [subst] using iha Δ σ hσ)
        (by simpa only [subst] using ihi Δ σ hσ)
        (by simpa only [subst] using ihp Δ σ hσ)
    case lam hA he hb ihA ihb Δ σ hσ =>
      simp only [subst]
      exact .lam (ihA Δ σ hσ) (by simpa only [hA.proposition_subst σ] using he)
        (ihb _ _ (hσ.lift _))
    case app hf ha ihf iha Δ σ hσ =>
      simp only [subst, subst_instantiate]
      exact .app (by simpa only [subst] using ihf Δ σ hσ) (iha Δ σ hσ)
    case convert ht hc ih Δ σ hσ => exact .convert (ih Δ σ hσ) (hc.substitution σ)
  · intro Γ t A h
    induction h using HasType.rec
      (motive_1 := fun Γ A _ => ∀ Δ σ, Substitution Γ Δ σ → IsType Δ (A.subst σ))
    case u64 Δ σ hσ => simpa only [subst] using (IsType.u64 (Γ := Δ))
    case i64 Δ σ hσ => simpa only [subst] using (IsType.i64 (Γ := Δ))
    case array hn ih Δ σ hσ =>
      simp only [subst]
      exact .array (by simpa only [subst] using ih Δ σ hσ)
    case lt ha hb iha ihb Δ σ hσ =>
      simp only [subst]
      exact .lt (by simpa only [subst] using iha Δ σ hσ)
        (by simpa only [subst] using ihb Δ σ hσ)
    case eq ha hb iha ihb Δ σ hσ =>
      simp only [subst]
      exact .eq (by simpa only [subst] using iha Δ σ hσ)
        (by simpa only [subst] using ihb Δ σ hσ)
    case pi hA he hB ihA ihB Δ σ hσ =>
      simp only [subst]
      exact .pi (ihA Δ σ hσ) (by simpa only [hA.proposition_subst σ] using he)
        (ihB _ _ (hσ.lift _))
    case var hx =>
      intro Δ σ hσ
      simpa only [subst] using hσ _ _ hx
    case natural hn =>
      intro Δ σ hσ
      simpa only [subst] using (HasType.natural (Γ := Δ) hn)
    case integer hlo hhi =>
      intro Δ σ hσ
      simpa only [subst] using (HasType.integer (Γ := Δ) hlo hhi)
    case uadd ha hb iha ihb =>
      intro Δ σ hσ
      simp only [subst]
      exact .uadd (by simpa only [subst] using iha Δ σ hσ)
        (by simpa only [subst] using ihb Δ σ hσ)
    case usub ha hb hp iha ihb ihp =>
      intro Δ σ hσ
      simp only [subst]
      exact .usub (by simpa only [subst] using iha Δ σ hσ)
        (by simpa only [subst] using ihb Δ σ hσ)
        (by simpa only [subst] using ihp Δ σ hσ)
    case elements xs Γ hs hlen ih =>
      intro Δ σ hσ
      simp only [subst]
      have ht := HasType.elements (Γ := Δ) (xs := xs.map (subst σ))
        (fun y hy => ?_) (by simpa only [List.length_map] using hlen)
      · simpa only [List.length_map] using ht
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        simpa only [subst] using ih x hx Δ σ hσ
    case decide ha hb hab =>
      intro Δ σ hσ
      simpa only [subst] using (HasType.decide (Γ := Δ) ha hb hab)
    case refl ha ih =>
      intro Δ σ hσ
      simp only [subst]
      exact .refl (by simpa only [subst] using ih Δ σ hσ)
    case index ha hi hp iha ihi ihp =>
      intro Δ σ hσ
      simp only [subst]
      exact .index (by simpa only [subst] using iha Δ σ hσ)
        (by simpa only [subst] using ihi Δ σ hσ)
        (by simpa only [subst] using ihp Δ σ hσ)
    case lam hA he hb ihA ihb =>
      intro Δ σ hσ
      simp only [subst]
      exact .lam (ihA Δ σ hσ) (by simpa only [hA.proposition_subst σ] using he)
        (ihb _ _ (hσ.lift _))
    case app hf ha ihf iha =>
      intro Δ σ hσ
      simp only [subst, subst_instantiate]
      exact .app (by simpa only [subst] using ihf Δ σ hσ) (iha Δ σ hσ)
    case convert ht hc ih =>
      intro Δ σ hσ
      exact .convert (ih Δ σ hσ) (hc.substitution σ)
/-- Typed capture-avoiding substitution transports formation and typing
jointly, including all annotations, dependent codomains and conversions. -/
theorem IsType.substitution (h : IsType Γ A) (hσ : Substitution Γ Δ σ) :
    IsType Δ (A.subst σ) := substitution_mutual.1 _ _ h _ _ hσ

theorem HasType.substitution (h : HasType Γ t A) (hσ : Substitution Γ Δ σ) :
    HasType Δ (t.subst σ) (A.subst σ) := substitution_mutual.2 _ _ _ h _ _ hσ

/-- Removing one binder is a typed simultaneous substitution. -/
theorem Substitution.single (ha : HasType Γ a A) :
    Substitution (Γ.extend A) Γ (Raw.single a) := by
  intro x B hx
  cases x with
  | zero =>
      simp only [Context.extend, Option.some.injEq] at hx
      subst B
      simpa only [subst_shift, Raw.single] using ha
  | succ x =>
      simp only [Context.extend, Option.map_eq_some_iff] at hx
      obtain ⟨B, hb, rfl⟩ := hx
      simpa only [subst_shift, Raw.single] using HasType.var hb

/-- Head-beta admissibility from the body's typing derivation. The result type
is instantiated too; no beta equation has been added to `Conv`. -/
theorem HasType.instantiate (hb : HasType (Γ.extend A) body B)
    (ha : HasType Γ a A) : HasType Γ (body.subst (single a)) (B.subst (single a)) :=
  hb.substitution (Substitution.single ha)

private def piView : Raw → Option (Bool × Raw × Raw)
  | .pi e A B => some (e, A, B)
  | _ => none

private theorem Conv.piView (h : Conv A B) : piView A = piView B := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | add => rfl
  | lt => rfl
  | eq => rfl
  | array => rfl

/-- In this deliberately restricted conversion, Pi types are rigid. This
fact is proved from the existing constructors, not supplied as an axiom. -/
theorem Conv.pi_rigid (h : Conv (.pi e A B) C) : C = .pi e A B := by
  have hv := h.piView
  cases C <;> simp [Raw.piView] at hv
  obtain ⟨rfl, rfl, rfl⟩ := hv
  rfl

private theorem HasType.lam_inversion_aux (h : HasType Γ t T) :
    ∀ e A body, t = .lam e A body →
      ∃ B, T = .pi e A B ∧ IsType Γ A ∧ e = A.proposition ∧
        HasType (Γ.extend A) body B := by
  induction h using HasType.rec (motive_1 := fun _ _ _ => True) <;>
    first | trivial | (intros e A body heq; cases heq)
  case lam Γ A e body B hA he hb ihA ihb => exact ⟨B, rfl, hA, he, hb⟩
  case convert hc ht ih =>
    obtain ⟨B, rfl, hA, he, hb⟩ := ih _ _ _ rfl
    exact ⟨B, hc.pi_rigid, hA, he, hb⟩

theorem HasType.lam_inversion (h : HasType Γ (.lam e A body) T) :
    ∃ B, T = .pi e A B ∧ IsType Γ A ∧ e = A.proposition ∧
      HasType (Γ.extend A) body B := h.lam_inversion_aux e A body rfl

private theorem HasType.head_beta_aux (h : HasType Γ t C) :
    ∀ e A body a, t = .app (.lam e A body) a →
      HasType Γ (body.subst (single a)) C := by
  induction h using HasType.rec (motive_1 := fun _ _ _ => True) <;>
    first | trivial | (intros e A body a heq; cases heq)
  case app ha iha hf ihf =>
    obtain ⟨B, hpi, _, _, hb⟩ := hf.lam_inversion
    cases hpi
    exact hb.instantiate ha
  case convert hc ht ih =>
    exact .convert (ih _ _ _ _ rfl) hc

/-- Retyping the head-beta contractum at the exact original application type,
including arbitrarily many outer conversion rules. This is not a theorem of
fixed-type preservation for beta steps inside arbitrary dependent contexts. -/
theorem HasType.head_beta (h : HasType Γ (.app (.lam e A body) a) C) :
    HasType Γ (body.subst (single a)) C := h.head_beta_aux e A body a rfl

end Jihoo.CoreBridge.Raw
