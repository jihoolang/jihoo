import Jihoo.CoreBridgeBetaConversion

/-! A beta-aware extension of the restricted target judgment. The historical
`Raw` judgments remain unchanged. Contexts need not be well formed: every
transport premise concerns actual lookups, not an assumed output derivation. -/
namespace Jihoo.CoreBridge.Raw.Beta

open Jihoo.Indexed (liftRenaming)

mutual
  /-- Type formation without adding a universe constructor to the selected Raw
  syntax. The indices in types must themselves be well-typed U64 expressions. -/
  inductive IsType : Context → Raw → Prop where
    | u64 : IsType Γ .u64
    | i64 : IsType Γ .i64
    | array : HasType Γ n .u64 → IsType Γ (.array n)
    | lt : HasType Γ a .u64 → HasType Γ b .u64 → IsType Γ (.lt a b)
    | eq : HasType Γ a .u64 → HasType Γ b .u64 → IsType Γ (.eq a b)
    | pi : IsType Γ A → e = A.proposition →
        IsType (Γ.extend A) B → IsType Γ (.pi e A B)

  /-- Ordinary declarative rules over one variable namespace. These rules do
  not mention `Index`, `Ty`, `Term`, their encoders, or source typing. Ghost-mode
  lookup is unrestricted; executable runtime erasure checking is not modeled. -/
  inductive HasType : Context → Raw → Raw → Prop where
    | var : Γ x = some A → HasType Γ (.var x) A
    | natural : n < wordBound → HasType Γ (.natural n) .u64
    | integer : -signedBound ≤ n → n < signedBound → HasType Γ (.integer n) .i64
    | uadd : HasType Γ a .u64 → HasType Γ b .u64 → HasType Γ (.uadd a b) .u64
    | usub : HasType Γ a .u64 → HasType Γ b .u64 →
        HasType Γ p (.lt b (.uadd a (.natural 1))) → HasType Γ (.usub a b p) .u64
    | elements : (∀ x ∈ xs, HasType Γ x .i64) → xs.length < wordBound →
        HasType Γ (.elements xs) (.array (.natural xs.length))
    | decide : a < wordBound → b < wordBound → a < b →
        HasType Γ (.decide (.natural a) (.natural b)) (.lt (.natural a) (.natural b))
    | refl : HasType Γ a .u64 → HasType Γ (.refl a) (.eq a a)
    | index : HasType Γ a (.array n) → HasType Γ i .u64 →
        HasType Γ p (.lt i n) → HasType Γ (.index a i p) .i64
    | lam : IsType Γ A → e = A.proposition →
        HasType (Γ.extend A) body B → HasType Γ (.lam e A body) (.pi e A B)
    | app : HasType Γ f (.pi e A B) → HasType Γ a A →
        HasType Γ (.app f a) (B.subst (single a))
    | convert : HasType Γ t A → Conv A B → HasType Γ t B
end


/-- Every substituted variable has its substituted current-scope type. -/
def Substitution (Γ Δ : Context) (σ : Nat → Raw) : Prop :=
  ∀ x A, Γ x = some A → HasType Δ (σ x) (A.subst σ)

/-- This needs formation: substituting for an arbitrary Raw variable can change
its proposition classification. Only the codomain of a formed Pi recurses. -/
theorem IsType.proposition_subst (h : IsType Γ A) (σ : Nat → Raw) :
    (A.subst σ).proposition = A.proposition := by
  induction A using Raw.rec (motive_2 := fun _ => True) generalizing Γ σ <;>
    first | trivial | (cases h <;> simp_all [subst, proposition])
  case pi.pi _ _ _ _ ih _ _ hB => exact ih hB _


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
    case integer hlo hhi Δ ρ hρ =>
      simpa only [rename] using (HasType.integer (Γ := Δ) hlo hhi)
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
    case decide ha hb hab Δ σ hσ =>
      simpa only [subst] using (HasType.decide (Γ := Δ) ha hb hab)
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
is instantiated by the same capture-avoiding operation. -/
theorem HasType.instantiate (hb : HasType (Γ.extend A) body B)
    (ha : HasType Γ a A) : HasType Γ (body.subst (single a)) (B.subst (single a)) :=
  hb.substitution (Substitution.single ha)


/-- Convertible contexts can change existing types without changing variables. -/
def ContextConversion (Γ Δ : Context) : Prop :=
  ∀ x A, Γ x = some A → ∃ B, Δ x = some B ∧ Conv A B

theorem ContextConversion.refl (Γ : Context) : ContextConversion Γ Γ := by
  intro x A hx
  exact ⟨A, hx, .refl A⟩

theorem ContextConversion.extend (h : ContextConversion Γ Δ) (hA : Conv A A') :
    ContextConversion (Γ.extend A) (Δ.extend A') := by
  intro x B hx
  cases x with
  | zero =>
      simp only [Context.extend, Option.some.injEq] at hx
      subst B
      exact ⟨_, rfl, hA.renaming Nat.succ⟩
  | succ x =>
      simp only [Context.extend, Option.map_eq_some_iff] at hx
      obtain ⟨B, hb, rfl⟩ := hx
      obtain ⟨C, hc, hbc⟩ := h x B hb
      exact ⟨_, by simp only [Context.extend, hc, Option.map_some], hbc.renaming Nat.succ⟩

private theorem context_conversion_mutual :
    (∀ Γ A, IsType Γ A → ∀ Δ, ContextConversion Γ Δ → IsType Δ A) ∧
    (∀ Γ t A, HasType Γ t A → ∀ Δ, ContextConversion Γ Δ → HasType Δ t A) := by
  constructor
  · intro Γ A h
    induction h using IsType.rec
      (motive_2 := fun Γ t A _ => ∀ Δ, ContextConversion Γ Δ → HasType Δ t A)
    case u64 => intros; exact .u64
    case i64 => intros; exact .i64
    case array hn ih => intro Δ hc; exact .array (ih Δ hc)
    case lt ha hb iha ihb => intro Δ hc; exact .lt (iha Δ hc) (ihb Δ hc)
    case eq ha hb iha ihb => intro Δ hc; exact .eq (iha Δ hc) (ihb Δ hc)
    case pi hA he hB ihA ihB =>
      intro Δ hc
      exact .pi (ihA Δ hc) he (ihB _ (hc.extend (.refl _)))
    case var hx Δ hc =>
      obtain ⟨B, hb, hab⟩ := hc _ _ hx
      exact .convert (.var hb) (.symm hab)
    case natural hn Δ hc => exact .natural hn
    case integer hlo hhi Δ hc => exact .integer hlo hhi
    case uadd ha hb iha ihb Δ hc => exact .uadd (iha Δ hc) (ihb Δ hc)
    case usub ha hb hp iha ihb ihp Δ hc => exact .usub (iha Δ hc) (ihb Δ hc) (ihp Δ hc)
    case elements xs Γ hs hlen ih Δ hc => exact .elements (fun x hx => ih x hx Δ hc) hlen
    case decide ha hb hab Δ hc => exact .decide ha hb hab
    case refl ha ih Δ hc => exact .refl (ih Δ hc)
    case index ha hi hp iha ihi ihp Δ hc => exact .index (iha Δ hc) (ihi Δ hc) (ihp Δ hc)
    case lam hA he hb ihA ihb Δ hc =>
      exact .lam (ihA Δ hc) he (ihb _ (hc.extend (.refl _)))
    case app hf ha ihf iha Δ hc => exact .app (ihf Δ hc) (iha Δ hc)
    case convert ht hconv ih Δ hc => exact .convert (ih Δ hc) hconv
  · intro Γ t A h
    induction h using HasType.rec
      (motive_1 := fun Γ A _ => ∀ Δ, ContextConversion Γ Δ → IsType Δ A)
    case u64 Δ hc => exact .u64
    case i64 Δ hc => exact .i64
    case array hn ih Δ hc => exact .array (ih Δ hc)
    case lt ha hb iha ihb Δ hc => exact .lt (iha Δ hc) (ihb Δ hc)
    case eq ha hb iha ihb Δ hc => exact .eq (iha Δ hc) (ihb Δ hc)
    case pi hA he hB ihA ihB Δ hc =>
      exact .pi (ihA Δ hc) he (ihB _ (hc.extend (.refl _)))
    case var hx =>
      intro Δ hc
      obtain ⟨B, hb, hab⟩ := hc _ _ hx
      exact .convert (.var hb) (.symm hab)
    case natural hn => intro Δ hc; exact .natural hn
    case integer hlo hhi => intro Δ hc; exact .integer hlo hhi
    case uadd ha hb iha ihb => intro Δ hc; exact .uadd (iha Δ hc) (ihb Δ hc)
    case usub ha hb hp iha ihb ihp => intro Δ hc; exact .usub (iha Δ hc) (ihb Δ hc) (ihp Δ hc)
    case elements xs Γ hs hlen ih => intro Δ hc; exact .elements (fun x hx => ih x hx Δ hc) hlen
    case decide ha hb hab => intro Δ hc; exact .decide ha hb hab
    case refl ha ih => intro Δ hc; exact .refl (ih Δ hc)
    case index ha hi hp iha ihi ihp => intro Δ hc; exact .index (iha Δ hc) (ihi Δ hc) (ihp Δ hc)
    case lam hA he hb ihA ihb =>
      intro Δ hc
      exact .lam (ihA Δ hc) he (ihb _ (hc.extend (.refl _)))
    case app hf ha ihf iha => intro Δ hc; exact .app (ihf Δ hc) (iha Δ hc)
    case convert ht hconv ih => intro Δ hc; exact .convert (ih Δ hc) hconv

theorem IsType.context_conversion (h : IsType Γ A) (hc : ContextConversion Γ Δ) :
    IsType Δ A := context_conversion_mutual.1 _ _ h _ hc

theorem HasType.context_conversion (h : HasType Γ t A) (hc : ContextConversion Γ Δ) :
    HasType Δ t A := context_conversion_mutual.2 _ _ _ h _ hc

private theorem HasType.lam_inversion_aux (h : HasType Γ t T) :
    ∀ e A body, t = .lam e A body →
      ∃ B, Conv (.pi e A B) T ∧ IsType Γ A ∧ e = A.proposition ∧
        HasType (Γ.extend A) body B := by
  induction h using HasType.rec (motive_1 := fun _ _ _ => True) <;>
    first | trivial | (intros e A body heq; cases heq)
  case lam Γ A e body B hA he hb ihA ihb => exact ⟨B, .refl _, hA, he, hb⟩
  case convert hc ht ih =>
    obtain ⟨B, hconv, hA, he, hb⟩ := ih _ _ _ rfl
    exact ⟨B, .trans hconv hc, hA, he, hb⟩

/-- Lambda inversion retains conversion, not the obsolete rigidity of Pis. -/
theorem HasType.lam_inversion (h : HasType Γ (.lam e A body) T) :
    ∃ B, Conv (.pi e A B) T ∧ IsType Γ A ∧ e = A.proposition ∧
      HasType (Γ.extend A) body B := h.lam_inversion_aux e A body rfl


/-- Every historical arithmetic conversion is a beta-aware conversion. -/
theorem Conv.of_raw (h : Raw.Conv A B) : Conv A B := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | add a b hb => exact .add a b hb
  | lt _ _ ih₁ ih₂ => exact .lt ih₁ ih₂
  | eq _ _ ih₁ ih₂ => exact .eq ih₁ ih₂
  | array _ ih => exact .array ih

private theorem of_raw_mutual :
    (∀ Γ A, Raw.IsType Γ A → IsType Γ A) ∧
    (∀ Γ t A, Raw.HasType Γ t A → HasType Γ t A) := by
  constructor
  · intro Γ A h
    induction h using Raw.IsType.rec (motive_2 := fun Γ t A _ => HasType Γ t A)
    case u64 => exact .u64
    case i64 => exact .i64
    case array hn ih => exact .array ih
    case lt ha hb iha ihb => exact .lt iha ihb
    case eq ha hb iha ihb => exact .eq iha ihb
    case pi hA he hB ihA ihB => exact .pi ihA he ihB
    case var hx => exact .var hx
    case natural hn => exact .natural hn
    case integer hlo hhi => exact .integer hlo hhi
    case uadd ha hb iha ihb => exact .uadd iha ihb
    case usub ha hb hp iha ihb ihp => exact .usub iha ihb ihp
    case elements xs Γ hs hlen ih => exact .elements ih hlen
    case decide ha hb hab => exact .decide ha hb hab
    case refl ha ih => exact .refl ih
    case index ha hi hp iha ihi ihp => exact .index iha ihi ihp
    case lam hA he hb ihA ihb => exact .lam ihA he ihb
    case app hf ha ihf iha => exact .app ihf iha
    case convert ht hc ih => exact .convert ih (Conv.of_raw hc)
  · intro Γ t A h
    induction h using Raw.HasType.rec (motive_1 := fun Γ A _ => IsType Γ A)
    case u64 => exact .u64
    case i64 => exact .i64
    case array hn ih => exact .array ih
    case lt ha hb iha ihb => exact .lt iha ihb
    case eq ha hb iha ihb => exact .eq iha ihb
    case pi hA he hB ihA ihB => exact .pi ihA he ihB
    case var hx => exact .var hx
    case natural hn => exact .natural hn
    case integer hlo hhi => exact .integer hlo hhi
    case uadd ha hb iha ihb => exact .uadd iha ihb
    case usub ha hb hp iha ihb ihp => exact .usub iha ihb ihp
    case elements xs Γ hs hlen ih => exact .elements ih hlen
    case decide ha hb hab => exact .decide ha hb hab
    case refl ha ih => exact .refl ih
    case index ha hi hp iha ihi ihp => exact .index iha ihi ihp
    case lam hA he hb ihA ihb => exact .lam ihA he ihb
    case app hf ha ihf iha => exact .app ihf iha
    case convert ht hc ih => exact .convert ih (Conv.of_raw hc)

/-- Legacy formation is included; the old judgment itself is unchanged. -/
theorem IsType.of_raw (h : Raw.IsType Γ A) : IsType Γ A := of_raw_mutual.1 _ _ h

/-- This is an extension, not an asserted equivalence to the executable core. -/
theorem HasType.of_raw (h : Raw.HasType Γ t A) : HasType Γ t A := of_raw_mutual.2 _ _ _ h

/-- Pi injectivity is derived from conversion's confluence, not assumed here. -/
theorem HasType.beta_contract (hf : HasType Γ (.lam e A body) (.pi e' A' B'))
    (ha : HasType Γ a A') : HasType Γ (body.subst (single a)) (B'.subst (single a)) := by
  obtain ⟨B, hpi, _, _, hb⟩ := hf.lam_inversion
  obtain ⟨_, hA, hB⟩ := hpi.pi_injective
  exact .convert (hb.instantiate (.convert ha (.symm hA))) (hB.substitution _)

private theorem HasType.head_beta_aux (h : HasType Γ t C) :
    ∀ e A body a, t = .app (.lam e A body) a →
      HasType Γ (body.subst (single a)) C := by
  induction h using HasType.rec (motive_1 := fun _ _ _ => True) <;>
    first | trivial | (intros e A body a heq; cases heq)
  case app ha iha hf ihf => exact hf.beta_contract ha
  case convert hc ht ih => exact .convert (ih _ _ _ _ rfl) hc

theorem HasType.head_beta (h : HasType Γ (.app (.lam e A body) a) C) :
    HasType Γ (body.subst (single a)) C := h.head_beta_aux e A body a rfl

end Jihoo.CoreBridge.Raw.Beta
