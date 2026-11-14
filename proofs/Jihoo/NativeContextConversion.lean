import Jihoo.NativeGhostMetatheory

/-! Ghost typing transport across independently related context lookups. No
target typing derivation is included in the context relation: annotations are
related by untyped conversion, while erased flags and actual lookups agree. -/
namespace Jihoo.NativeKernel

/-- The binder's native erasure policy survives changing its domain by a proved
conversion. Formation of the changed domain remains a separate typing premise. -/
theorem binderAllowed_conversion {e : Bool} {A A' : Term} {s : SortTag}
    (h : binderAllowed e A s) (hA : Conversion.Conv A A') : binderAllowed e A' s := by
  cases e with
  | false => exact h
  | true =>
      rcases h with hp | hu
      · exact Or.inl hp
      · exact Or.inr (.trans (.symm hA) hu)

namespace Ghost

def ContextConversion (Γ Δ : Context) : Prop :=
  ∀ x b, lookup Γ x = some b →
    ∃ b', lookup Δ x = some b' ∧ b'.erased = b.erased ∧ Conversion.Conv b.ty b'.ty

theorem ContextConversion.refl (Γ : Context) : ContextConversion Γ Γ := by
  intro x b hb
  exact ⟨b,hb,rfl,.refl _⟩

theorem ContextConversion.trans {Γ Δ Θ : Context}
    (h : ContextConversion Γ Δ) (h' : ContextConversion Δ Θ) : ContextConversion Γ Θ := by
  intro x b hb
  obtain ⟨b',hb',he,hc⟩ := h x b hb
  obtain ⟨b'',hb'',he',hc'⟩ := h' x b' hb'
  exact ⟨b'',hb'',he'.trans he,.trans hc hc'⟩

theorem ContextConversion.extend {Γ Δ : Context} {A A' : Term}
    (h : ContextConversion Γ Δ) (hA : Conversion.Conv A A') (e : Bool) :
    ContextConversion (⟨A,e⟩ :: Γ) (⟨A',e⟩ :: Δ) := by
  intro x b hx
  cases x with
  | zero =>
      simp only [lookup,Option.some.injEq] at hx
      cases hx
      exact ⟨⟨A'.rename Nat.succ,e⟩,rfl,rfl,hA.renaming Nat.succ⟩
  | succ x =>
      simp only [lookup] at hx
      obtain ⟨b₀,h₀,he⟩ := Option.map_eq_some_iff.mp hx
      subst b
      obtain ⟨b',hb',hflag,hconv⟩ := h x b₀ h₀
      exact ⟨⟨b'.ty.rename Nat.succ,b'.erased⟩,
        by simp only [lookup,hb',Option.map_some],hflag,hconv.renaming Nat.succ⟩

end Ghost

private theorem context_mutual :
    (∀ Γ e A s, Binder Γ e A s → ∀ Δ, Ghost.ContextConversion Γ Δ → Binder Δ e A s) ∧
    (∀ Γ mode t A, HasType Γ mode t A → ∀ Δ, Ghost.ContextConversion Γ Δ → HasType Δ true t A) := by
  constructor
  · intro Γ e A s h
    induction h using Binder.rec
      (motive_2 := fun Γ mode t A _ => ∀ Δ, Ghost.ContextConversion Γ Δ → HasType Δ true t A) with
    | intro ht allowed ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .intro (ih Δ hctx) allowed
    | var hx allowed =>
        first | intro Δ hctx | rename_i Δ hctx
        obtain ⟨b',hb',he,hconv⟩ := hctx _ _ hx
        exact .convert (.var hb' (Or.inl rfl)) (.symm hconv)
    | univ bound =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .univ bound
    | prop =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .prop
    | u64 =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .u64
    | i64 =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .i64
    | natural bound =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .natural bound
    | integer lo hi =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .integer lo hi
    | array hn ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .array (ih Δ hctx)
    | lt ha hb iha ihb =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .lt (iha Δ hctx) (ihb Δ hctx)
    | eq ha hb iha ihb =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .eq (iha Δ hctx) (ihb Δ hctx)
    | pi hA hB ihA ihB =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .pi (ihA Δ hctx) (ihB _ (hctx.extend (.refl _) _))
    | lam hA hb ihA ihb =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .lam (ihA Δ hctx) (ihb _ (hctx.extend (.refl _) _))
    | app hf ha allowed ihf iha =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .app (ihf Δ hctx) (by simpa using iha Δ hctx) (Or.inl rfl)
    | uadd ha hb iha ihb =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .uadd (iha Δ hctx) (ihb Δ hctx)
    | usub ha hb hp iha ihb ihp =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .usub (iha Δ hctx) (ihb Δ hctx) (ihp Δ hctx)
    | refl ha ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .refl (ih Δ hctx)
    | zeroLe ha ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .zeroLe (ih Δ hctx)
    | decide ha hb hab =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .decide ha hb hab
    | decideConverted ha hb ca cb hm hn hmn iha ihb =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .decideConverted (iha Δ hctx) (ihb Δ hctx) ca cb hm hn hmn
    | elements hn hb hs ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .elements hn hb (fun x hx => ih x hx Δ hctx)
    | index ha hi hp iha ihi ihp =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .index (iha Δ hctx) (ihi Δ hctx) (ihp Δ hctx)
    | arith ha hb iha ihb =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .arith (iha Δ hctx) (ihb Δ hctx)
    | strict ha hb iha ihb =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .strict (iha Δ hctx) (ihb Δ hctx)
    | ltAdd ha hb hc hp iha ihb ihc ihp =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .ltAdd (iha Δ hctx) (ihb Δ hctx) (ihc Δ hctx) (ihp Δ hctx)
    | ltCancel ha hb hc hp iha ihb ihc ihp =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .ltCancel (iha Δ hctx) (ihb Δ hctx) (ihc Δ hctx) (ihp Δ hctx)
    | ltLe ha hb hc hp hq iha ihb ihc ihp ihq =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .ltLe (iha Δ hctx) (ihb Δ hctx) (ihc Δ hctx) (ihp Δ hctx) (ihq Δ hctx)
    | transport hf he hp ihf ihe ihp =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .transport (ihf Δ hctx) (ihe Δ hctx) (ihp Δ hctx)
    | refine hp ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .refine (ih Δ hctx)
    | pack hp ha hq ihp iha ihq =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .pack (ihp Δ hctx) (iha Δ hctx) (ihq Δ hctx)
    | witness hs ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .witness (ih Δ hctx)
    | proof hs ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .proof (ih Δ hctx)
    | ifLt ha hb hy hn iha ihb ihy ihn =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .ifLt (iha Δ hctx) (ihb Δ hctx)
          (ihy _ (hctx.extend (.refl _) true)) (ihn Δ hctx)
    | ifEq ha hb hy hn iha ihb ihy ihn =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .ifEq (iha Δ hctx) (ihb Δ hctx)
          (ihy _ (hctx.extend (.refl _) true)) (ihn Δ hctx)
    | absurd hT hp allowed ihT ihp =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .absurd (ihT Δ hctx) (ihp Δ hctx) (Or.inl rfl)
    | convert ht hc ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .convert (ih Δ hctx) hc
  · intro Γ mode t A h
    induction h using HasType.rec
      (motive_1 := fun Γ e A s _ => ∀ Δ, Ghost.ContextConversion Γ Δ → Binder Δ e A s) with
    | intro ht allowed ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .intro (ih Δ hctx) allowed
    | var hx allowed =>
        first | intro Δ hctx | rename_i Δ hctx
        obtain ⟨b',hb',he,hconv⟩ := hctx _ _ hx
        exact .convert (.var hb' (Or.inl rfl)) (.symm hconv)
    | univ bound =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .univ bound
    | prop =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .prop
    | u64 =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .u64
    | i64 =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .i64
    | natural bound =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .natural bound
    | integer lo hi =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .integer lo hi
    | array hn ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .array (ih Δ hctx)
    | lt ha hb iha ihb =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .lt (iha Δ hctx) (ihb Δ hctx)
    | eq ha hb iha ihb =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .eq (iha Δ hctx) (ihb Δ hctx)
    | pi hA hB ihA ihB =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .pi (ihA Δ hctx) (ihB _ (hctx.extend (.refl _) _))
    | lam hA hb ihA ihb =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .lam (ihA Δ hctx) (ihb _ (hctx.extend (.refl _) _))
    | app hf ha allowed ihf iha =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .app (ihf Δ hctx) (by simpa using iha Δ hctx) (Or.inl rfl)
    | uadd ha hb iha ihb =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .uadd (iha Δ hctx) (ihb Δ hctx)
    | usub ha hb hp iha ihb ihp =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .usub (iha Δ hctx) (ihb Δ hctx) (ihp Δ hctx)
    | refl ha ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .refl (ih Δ hctx)
    | zeroLe ha ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .zeroLe (ih Δ hctx)
    | decide ha hb hab =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .decide ha hb hab
    | decideConverted ha hb ca cb hm hn hmn iha ihb =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .decideConverted (iha Δ hctx) (ihb Δ hctx) ca cb hm hn hmn
    | elements hn hb hs ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .elements hn hb (fun x hx => ih x hx Δ hctx)
    | index ha hi hp iha ihi ihp =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .index (iha Δ hctx) (ihi Δ hctx) (ihp Δ hctx)
    | arith ha hb iha ihb =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .arith (iha Δ hctx) (ihb Δ hctx)
    | strict ha hb iha ihb =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .strict (iha Δ hctx) (ihb Δ hctx)
    | ltAdd ha hb hc hp iha ihb ihc ihp =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .ltAdd (iha Δ hctx) (ihb Δ hctx) (ihc Δ hctx) (ihp Δ hctx)
    | ltCancel ha hb hc hp iha ihb ihc ihp =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .ltCancel (iha Δ hctx) (ihb Δ hctx) (ihc Δ hctx) (ihp Δ hctx)
    | ltLe ha hb hc hp hq iha ihb ihc ihp ihq =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .ltLe (iha Δ hctx) (ihb Δ hctx) (ihc Δ hctx) (ihp Δ hctx) (ihq Δ hctx)
    | transport hf he hp ihf ihe ihp =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .transport (ihf Δ hctx) (ihe Δ hctx) (ihp Δ hctx)
    | refine hp ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .refine (ih Δ hctx)
    | pack hp ha hq ihp iha ihq =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .pack (ihp Δ hctx) (iha Δ hctx) (ihq Δ hctx)
    | witness hs ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .witness (ih Δ hctx)
    | proof hs ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .proof (ih Δ hctx)
    | ifLt ha hb hy hn iha ihb ihy ihn =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .ifLt (iha Δ hctx) (ihb Δ hctx)
          (ihy _ (hctx.extend (.refl _) true)) (ihn Δ hctx)
    | ifEq ha hb hy hn iha ihb ihy ihn =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .ifEq (iha Δ hctx) (ihb Δ hctx)
          (ihy _ (hctx.extend (.refl _) true)) (ihn Δ hctx)
    | absurd hT hp allowed ihT ihp =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .absurd (ihT Δ hctx) (ihp Δ hctx) (Or.inl rfl)
    | convert ht hc ih =>
        first | intro Δ hctx | rename_i Δ hctx
        exact .convert (ih Δ hctx) hc

theorem Binder.ghostContextConversion {Γ Δ : Context} {e : Bool} {A : Term} {s : SortTag}
    (h : Binder Γ e A s) (hctx : Ghost.ContextConversion Γ Δ) : Binder Δ e A s :=
  context_mutual.1 Γ e A s h Δ hctx

theorem HasType.ghostContextConversion {Γ Δ : Context} {mode : Bool} {t A : Term}
    (h : HasType Γ mode t A) (hctx : Ghost.ContextConversion Γ Δ) : HasType Δ true t A :=
  context_mutual.2 Γ mode t A h Δ hctx

end Jihoo.NativeKernel
