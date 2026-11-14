import Jihoo.NativeTyping
import Jihoo.NativeSubstitution

/-! Ghost-mode typed renaming and simultaneous substitution for the complete
native syntax and every current declarative typing rule. Substituted variables
carry independently derived types from actual context lookups. Runtime
application representation checks are not assumed invariant under substitution. -/
namespace Jihoo.NativeKernel

set_option linter.unusedSimpArgs false

@[simp] theorem SortTag.rename_term (s : SortTag) (ρ : Nat → Nat) :
    s.term.rename ρ = s.term := by
  cases s <;> simp [SortTag.term, Term.rename, renameArgs]

@[simp] theorem SortTag.subst_term (s : SortTag) (σ : Nat → Term) :
    s.term.subst σ = s.term := by
  cases s <;> simp [SortTag.term, Term.subst, substArgs]

theorem binderAllowed_renaming {e : Bool} {A : Term} {s : SortTag}
    (h : binderAllowed e A s) (ρ : Nat → Nat) : binderAllowed e (A.rename ρ) s := by
  cases e with
  | false => exact h
  | true =>
      rcases h with hp | hu
      · exact Or.inl hp
      · exact Or.inr (by simpa [Term.rename, renameArgs] using hu.renaming ρ)

theorem binderAllowed_substitution {e : Bool} {A : Term} {s : SortTag}
    (h : binderAllowed e A s) (σ : Nat → Term) : binderAllowed e (A.subst σ) s := by
  cases e with
  | false => exact h
  | true =>
      rcases h with hp | hu
      · exact Or.inl hp
      · exact Or.inr (by simpa [Term.subst, substArgs] using hu.substitution σ)

namespace Ghost

/-- A renaming preserves actual lookup annotations and their erased flags. -/
def Renaming (Γ Δ : Context) (ρ : Nat → Nat) : Prop :=
  ∀ x b, lookup Γ x = some b →
    lookup Δ (ρ x) = some ⟨b.ty.rename ρ, b.erased⟩

private theorem rename_shift (A : Term) (ρ : Nat → Nat) :
    (A.rename Nat.succ).rename (Indexed.liftRenaming ρ) =
      (A.rename ρ).rename Nat.succ := by
  rw [Term.rename_comp, Term.rename_comp]
  rfl

theorem Renaming.lift {Γ Δ : Context} {ρ : Nat → Nat}
    (hρ : Renaming Γ Δ ρ) (A : Term) (e : Bool) :
    Renaming (⟨A,e⟩ :: Γ) (⟨A.rename ρ,e⟩ :: Δ) (Indexed.liftRenaming ρ) := by
  intro x b hx
  cases x with
  | zero =>
      simp only [lookup, Option.some.injEq] at hx
      cases hx
      simp only [Indexed.liftRenaming, lookup, rename_shift]
  | succ x =>
      simp only [lookup] at hx
      obtain ⟨b₀, h₀, he⟩ := Option.map_eq_some_iff.mp hx
      subst b
      simp only [Indexed.liftRenaming, lookup, hρ x b₀ h₀, Option.map_some, rename_shift]

theorem Renaming.shift (Γ : Context) (A : Term) (e : Bool) :
    Renaming Γ (⟨A,e⟩ :: Γ) Nat.succ := by
  intro x b hx
  simp only [lookup, hx, Option.map_some]

end Ghost

private theorem ghost_renaming_mutual :
    (∀ Γ e A s, Binder Γ e A s → ∀ Δ ρ, Ghost.Renaming Γ Δ ρ → Binder Δ e (A.rename ρ) s) ∧
    (∀ Γ mode t A, HasType Γ mode t A → ∀ Δ ρ, Ghost.Renaming Γ Δ ρ →
      HasType Δ true (t.rename ρ) (A.rename ρ)) := by
  constructor
  · intro Γ e A s h
    induction h using Binder.rec
      (motive_2 := fun Γ mode t A _ => ∀ Δ ρ, Ghost.Renaming Γ Δ ρ →
        HasType Δ true (t.rename ρ) (A.rename ρ)) with
    | intro typed allowed ih_typed =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        exact .intro (by simpa using ih_typed Δ ρ hρ) (binderAllowed_renaming allowed ρ)
    | var hx _ =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa only [Term.rename] using HasType.var (hρ _ _ hx) (Or.inl rfl)

    | univ bound =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs] using (HasType.univ (ctx := Δ) (ghost := true) bound)

    | prop =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs] using (HasType.prop (ctx := Δ) (ghost := true))

    | u64 =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs] using (HasType.u64 (ctx := Δ) (ghost := true))

    | i64 =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs] using (HasType.i64 (ctx := Δ) (ghost := true))

    | natural bound =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs] using (HasType.natural (ctx := Δ) (ghost := true) bound)

    | integer lo hi =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs] using (HasType.integer (ctx := Δ) (ghost := true) lo hi)

    | array hn ih_hn =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.array (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hn Δ ρ hρ)

    | lt ha hb ih_ha ih_hb =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.lt (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)

    | eq ha hb ih_ha ih_hb =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.eq (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)

    | pi hA hB ih_hA ih_hB =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.pi (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hA Δ ρ hρ) (by simpa using ih_hB _ _ (hρ.lift _ _))

    | lam hA hb ih_hA ih_hb =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.lam (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hA Δ ρ hρ) (ih_hb _ _ (hρ.lift _ _))

    | @app ctx mode f e A B a hf ha allowed ih_hf ih_ha =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        change HasType Δ true ((Term.app f a).rename ρ) ((B.subst (single a)).rename ρ)
        rw [Term.rename_instantiate]
        simp only [Term.rename, renameArgs, Op.binders, liftRenaming]
        have hf' : HasType Δ true (f.rename ρ)
            (.pi e (A.rename ρ) (B.rename (Indexed.liftRenaming ρ))) := by
          simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ih_hf Δ ρ hρ
        have ha' : HasType Δ (true || e) (a.rename ρ) (A.rename ρ) := by
          simpa using ih_ha Δ ρ hρ
        exact HasType.app hf' ha' (Or.inl rfl)

    | uadd ha hb ih_ha ih_hb =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.uadd (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)

    | usub ha hb hp ih_ha ih_hb ih_hp =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.usub (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)

    | refl ha ih_ha =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.refl (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ)

    | zeroLe ha ih_ha =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.zeroLe (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ)

    | decide ha hb hab =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          (HasType.decide (ctx := Δ) (ghost := true) ha hb hab)

    | decideConverted ha hb ca cb hm hn hmn ih_ha ih_hb =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.decideConverted (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
            (by simpa [Term.rename, renameArgs] using ca.renaming ρ)
            (by simpa [Term.rename, renameArgs] using cb.renaming ρ) hm hn hmn

    | @elements n xs Γ mode hn hb hs ih_hs =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        have ht := HasType.elements (ctx := Δ) (ghost := true)
          (xs := xs.map (Term.rename ρ)) (n := n) (by simpa using hn) (by simpa using hb)
          (fun y hy => by
            obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
            simpa [Term.rename,renameArgs] using ih_hs x hx Δ ρ hρ)
        simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ht

    | index ha hi hp ih_ha ih_hi ih_hp =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.index (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hi Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)

    | arith ha hb ih_ha ih_hb =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.arith (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)

    | strict ha hb ih_ha ih_hb =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.strict (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)

    | ltAdd ha hb hc hp ih_ha ih_hb ih_hc ih_hp =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.ltAdd (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hc Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)

    | ltCancel ha hb hc hp ih_ha ih_hb ih_hc ih_hp =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.ltCancel (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hc Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)

    | ltLe ha hb hc hp hq ih_ha ih_hb ih_hc ih_hp ih_hq =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.ltLe (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hc Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hq Δ ρ hρ)

    | transport hf he hp ih_hf ih_he ih_hp =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.transport
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hf Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_he Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)

    | refine hp ih_hp =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.refine (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)

    | pack hp ha hq ih_hp ih_ha ih_hq =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.pack
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hq Δ ρ hρ)

    | witness hs ih_hs =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.witness (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hs Δ ρ hρ)

    | proof hs ih_hs =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.proof (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hs Δ ρ hρ)

    | convert ht hc ih_ht =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        exact .convert (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ht Δ ρ hρ) (hc.renaming ρ)
  · intro Γ mode t A h
    induction h using HasType.rec
      (motive_1 := fun Γ e A s _ => ∀ Δ ρ, Ghost.Renaming Γ Δ ρ → Binder Δ e (A.rename ρ) s) with
    | intro typed allowed ih_typed =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        exact .intro (by simpa using ih_typed Δ ρ hρ) (binderAllowed_renaming allowed ρ)
    | var hx _ =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa only [Term.rename] using HasType.var (hρ _ _ hx) (Or.inl rfl)

    | univ bound =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs] using (HasType.univ (ctx := Δ) (ghost := true) bound)

    | prop =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs] using (HasType.prop (ctx := Δ) (ghost := true))

    | u64 =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs] using (HasType.u64 (ctx := Δ) (ghost := true))

    | i64 =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs] using (HasType.i64 (ctx := Δ) (ghost := true))

    | natural bound =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs] using (HasType.natural (ctx := Δ) (ghost := true) bound)

    | integer lo hi =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs] using (HasType.integer (ctx := Δ) (ghost := true) lo hi)

    | array hn ih_hn =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.array (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hn Δ ρ hρ)

    | lt ha hb ih_ha ih_hb =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.lt (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)

    | eq ha hb ih_ha ih_hb =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.eq (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)

    | pi hA hB ih_hA ih_hB =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.pi (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hA Δ ρ hρ) (by simpa using ih_hB _ _ (hρ.lift _ _))

    | lam hA hb ih_hA ih_hb =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.lam (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hA Δ ρ hρ) (ih_hb _ _ (hρ.lift _ _))

    | @app ctx mode f e A B a hf ha allowed ih_hf ih_ha =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        change HasType Δ true ((Term.app f a).rename ρ) ((B.subst (single a)).rename ρ)
        rw [Term.rename_instantiate]
        simp only [Term.rename, renameArgs, Op.binders, liftRenaming]
        have hf' : HasType Δ true (f.rename ρ)
            (.pi e (A.rename ρ) (B.rename (Indexed.liftRenaming ρ))) := by
          simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ih_hf Δ ρ hρ
        have ha' : HasType Δ (true || e) (a.rename ρ) (A.rename ρ) := by
          simpa using ih_ha Δ ρ hρ
        exact HasType.app hf' ha' (Or.inl rfl)

    | uadd ha hb ih_ha ih_hb =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.uadd (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)

    | usub ha hb hp ih_ha ih_hb ih_hp =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.usub (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)

    | refl ha ih_ha =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.refl (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ)

    | zeroLe ha ih_ha =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.zeroLe (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ)

    | decide ha hb hab =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          (HasType.decide (ctx := Δ) (ghost := true) ha hb hab)

    | decideConverted ha hb ca cb hm hn hmn ih_ha ih_hb =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.decideConverted (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
            (by simpa [Term.rename, renameArgs] using ca.renaming ρ)
            (by simpa [Term.rename, renameArgs] using cb.renaming ρ) hm hn hmn

    | @elements n xs Γ mode hn hb hs ih_hs =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        have ht := HasType.elements (ctx := Δ) (ghost := true)
          (xs := xs.map (Term.rename ρ)) (n := n) (by simpa using hn) (by simpa using hb)
          (fun y hy => by
            obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
            simpa [Term.rename,renameArgs] using ih_hs x hx Δ ρ hρ)
        simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ht

    | index ha hi hp ih_ha ih_hi ih_hp =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.index (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hi Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)

    | arith ha hb ih_ha ih_hb =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.arith (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)

    | strict ha hb ih_ha ih_hb =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.strict (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)

    | ltAdd ha hb hc hp ih_ha ih_hb ih_hc ih_hp =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.ltAdd (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hc Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)

    | ltCancel ha hb hc hp ih_ha ih_hb ih_hc ih_hp =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.ltCancel (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hc Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)

    | ltLe ha hb hc hp hq ih_ha ih_hb ih_hc ih_hp ih_hq =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.ltLe (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hc Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hq Δ ρ hρ)

    | transport hf he hp ih_hf ih_he ih_hp =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.transport
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hf Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_he Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)

    | refine hp ih_hp =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.refine (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)

    | pack hp ha hq ih_hp ih_ha ih_hq =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.pack
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ)
            (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hq Δ ρ hρ)

    | witness hs ih_hs =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.witness (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hs Δ ρ hρ)

    | proof hs ih_hs =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
          HasType.proof (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hs Δ ρ hρ)

    | convert ht hc ih_ht =>
        first | intro Δ ρ hρ | rename_i Δ ρ hρ
        exact .convert (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ht Δ ρ hρ) (hc.renaming ρ)

theorem Binder.ghostRenaming {Γ : Context} {e : Bool} {A : Term} {s : SortTag}
    (h : Binder Γ e A s) {Δ : Context} {ρ : Nat → Nat}
    (hρ : Ghost.Renaming Γ Δ ρ) : Binder Δ e (A.rename ρ) s :=
  ghost_renaming_mutual.1 Γ e A s h Δ ρ hρ

/-- Transport any input mode to a renamed ghost derivation. -/
theorem HasType.ghostRenaming {Γ : Context} {mode : Bool} {t A : Term}
    (h : HasType Γ mode t A) {Δ : Context} {ρ : Nat → Nat}
    (hρ : Ghost.Renaming Γ Δ ρ) : HasType Δ true (t.rename ρ) (A.rename ρ) :=
  ghost_renaming_mutual.2 Γ mode t A h Δ ρ hρ

/-- Weakening is an instance of proved ghost renaming, with erased flags retained. -/
theorem HasType.ghostWeaken {Γ : Context} {mode : Bool} {t B : Term}
    (h : HasType Γ mode t B) (A : Term) (e : Bool) :
    HasType (⟨A,e⟩ :: Γ) true (t.rename Nat.succ) (B.rename Nat.succ) :=
  h.ghostRenaming (Ghost.Renaming.shift Γ A e)

private theorem shift_subst_lift (t : Term) (σ : Nat → Term) :
    (t.rename Nat.succ).subst (liftSubOne σ) = (t.subst σ).rename Nat.succ := by
  rw [Term.subst_rename, Term.rename_subst]
  rfl

namespace Ghost

/-- A variable substitution is justified by a derivation at its substituted
current-scope lookup type; no requested output typing is assumed. -/
def Substitution (Γ Δ : Context) (σ : Nat → Term) : Prop :=
  ∀ x b, lookup Γ x = some b → HasType Δ true (σ x) (b.ty.subst σ)

theorem Substitution.lift {Γ Δ : Context} {σ : Nat → Term}
    (hσ : Substitution Γ Δ σ) (A : Term) (e : Bool) :
    Substitution (⟨A,e⟩ :: Γ) (⟨A.subst σ,e⟩ :: Δ) (liftSubOne σ) := by
  intro x b hx
  cases x with
  | zero =>
      simp only [lookup, Option.some.injEq] at hx
      cases hx
      simp only [liftSubOne, shift_subst_lift]
      exact HasType.var (b := ⟨(A.subst σ).rename Nat.succ,e⟩) rfl (Or.inl rfl)
  | succ x =>
      simp only [lookup] at hx
      obtain ⟨b₀,h₀,he⟩ := Option.map_eq_some_iff.mp hx
      subst b
      simpa only [liftSubOne,shift_subst_lift] using (hσ x b₀ h₀).ghostWeaken (A.subst σ) e

end Ghost

private theorem ghost_substitution_mutual :
    (∀ Γ e A s, Binder Γ e A s → ∀ Δ σ, Ghost.Substitution Γ Δ σ → Binder Δ e (A.subst σ) s) ∧
    (∀ Γ mode t A, HasType Γ mode t A → ∀ Δ σ, Ghost.Substitution Γ Δ σ →
      HasType Δ true (t.subst σ) (A.subst σ)) := by
  constructor
  · intro Γ e A s h
    induction h using Binder.rec
      (motive_2 := fun Γ mode t A _ => ∀ Δ σ, Ghost.Substitution Γ Δ σ →
        HasType Δ true (t.subst σ) (A.subst σ)) with
    | intro typed allowed ih_typed =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        exact .intro (by simpa using ih_typed Δ σ hσ) (binderAllowed_substitution allowed σ)
    | var hx _ =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa only [Term.subst] using hσ _ _ hx

    | univ bound =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs] using (HasType.univ (ctx := Δ) (ghost := true) bound)

    | prop =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs] using (HasType.prop (ctx := Δ) (ghost := true))

    | u64 =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs] using (HasType.u64 (ctx := Δ) (ghost := true))

    | i64 =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs] using (HasType.i64 (ctx := Δ) (ghost := true))

    | natural bound =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs] using (HasType.natural (ctx := Δ) (ghost := true) bound)

    | integer lo hi =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs] using (HasType.integer (ctx := Δ) (ghost := true) lo hi)

    | array hn ih_hn =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.array (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hn Δ σ hσ)

    | lt ha hb ih_ha ih_hb =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.lt (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)

    | eq ha hb ih_ha ih_hb =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.eq (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)

    | pi hA hB ih_hA ih_hB =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.pi (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hA Δ σ hσ) (by simpa using ih_hB _ _ (hσ.lift _ _))

    | lam hA hb ih_hA ih_hb =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.lam (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hA Δ σ hσ) (ih_hb _ _ (hσ.lift _ _))

    | @app ctx mode f e A B a hf ha allowed ih_hf ih_ha =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        change HasType Δ true ((Term.app f a).subst σ) ((B.subst (single a)).subst σ)
        rw [Term.subst_instantiate]
        simp only [Term.subst, substArgs, Op.binders, liftSub]
        have hf' : HasType Δ true (f.subst σ)
            (.pi e (A.subst σ) (B.subst (liftSubOne σ))) := by
          simpa [Term.subst,substArgs,Op.binders,liftSub] using ih_hf Δ σ hσ
        have ha' : HasType Δ (true || e) (a.subst σ) (A.subst σ) := by
          simpa using ih_ha Δ σ hσ
        exact HasType.app hf' ha' (Or.inl rfl)

    | uadd ha hb ih_ha ih_hb =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.uadd (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)

    | usub ha hb hp ih_ha ih_hb ih_hp =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.usub (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)

    | refl ha ih_ha =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.refl (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ)

    | zeroLe ha ih_ha =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.zeroLe (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ)

    | decide ha hb hab =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          (HasType.decide (ctx := Δ) (ghost := true) ha hb hab)

    | decideConverted ha hb ca cb hm hn hmn ih_ha ih_hb =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.decideConverted (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
            (by simpa [Term.subst, substArgs] using ca.substitution σ)
            (by simpa [Term.subst, substArgs] using cb.substitution σ) hm hn hmn

    | @elements n xs Γ mode hn hb hs ih_hs =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        have ht := HasType.elements (ctx := Δ) (ghost := true)
          (xs := xs.map (Term.subst σ)) (n := n) (by simpa using hn) (by simpa using hb)
          (fun y hy => by
            obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
            simpa [Term.subst,substArgs] using ih_hs x hx Δ σ hσ)
        simpa [Term.subst,substArgs,Op.binders,liftSub] using ht

    | index ha hi hp ih_ha ih_hi ih_hp =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.index (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hi Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)

    | arith ha hb ih_ha ih_hb =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.arith (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)

    | strict ha hb ih_ha ih_hb =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.strict (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)

    | ltAdd ha hb hc hp ih_ha ih_hb ih_hc ih_hp =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.ltAdd (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hc Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)

    | ltCancel ha hb hc hp ih_ha ih_hb ih_hc ih_hp =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.ltCancel (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hc Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)

    | ltLe ha hb hc hp hq ih_ha ih_hb ih_hc ih_hp ih_hq =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.ltLe (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hc Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hq Δ σ hσ)

    | transport hf he hp ih_hf ih_he ih_hp =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.transport
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hf Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_he Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)

    | refine hp ih_hp =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.refine (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)

    | pack hp ha hq ih_hp ih_ha ih_hq =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.pack
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hq Δ σ hσ)

    | witness hs ih_hs =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.witness (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hs Δ σ hσ)

    | proof hs ih_hs =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.proof (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hs Δ σ hσ)

    | convert ht hc ih_ht =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        exact .convert (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ht Δ σ hσ) (hc.substitution σ)
  · intro Γ mode t A h
    induction h using HasType.rec
      (motive_1 := fun Γ e A s _ => ∀ Δ σ, Ghost.Substitution Γ Δ σ → Binder Δ e (A.subst σ) s) with
    | intro typed allowed ih_typed =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        exact .intro (by simpa using ih_typed Δ σ hσ) (binderAllowed_substitution allowed σ)
    | var hx _ =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa only [Term.subst] using hσ _ _ hx

    | univ bound =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs] using (HasType.univ (ctx := Δ) (ghost := true) bound)

    | prop =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs] using (HasType.prop (ctx := Δ) (ghost := true))

    | u64 =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs] using (HasType.u64 (ctx := Δ) (ghost := true))

    | i64 =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs] using (HasType.i64 (ctx := Δ) (ghost := true))

    | natural bound =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs] using (HasType.natural (ctx := Δ) (ghost := true) bound)

    | integer lo hi =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs] using (HasType.integer (ctx := Δ) (ghost := true) lo hi)

    | array hn ih_hn =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.array (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hn Δ σ hσ)

    | lt ha hb ih_ha ih_hb =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.lt (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)

    | eq ha hb ih_ha ih_hb =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.eq (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)

    | pi hA hB ih_hA ih_hB =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.pi (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hA Δ σ hσ) (by simpa using ih_hB _ _ (hσ.lift _ _))

    | lam hA hb ih_hA ih_hb =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.lam (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hA Δ σ hσ) (ih_hb _ _ (hσ.lift _ _))

    | @app ctx mode f e A B a hf ha allowed ih_hf ih_ha =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        change HasType Δ true ((Term.app f a).subst σ) ((B.subst (single a)).subst σ)
        rw [Term.subst_instantiate]
        simp only [Term.subst, substArgs, Op.binders, liftSub]
        have hf' : HasType Δ true (f.subst σ)
            (.pi e (A.subst σ) (B.subst (liftSubOne σ))) := by
          simpa [Term.subst,substArgs,Op.binders,liftSub] using ih_hf Δ σ hσ
        have ha' : HasType Δ (true || e) (a.subst σ) (A.subst σ) := by
          simpa using ih_ha Δ σ hσ
        exact HasType.app hf' ha' (Or.inl rfl)

    | uadd ha hb ih_ha ih_hb =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.uadd (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)

    | usub ha hb hp ih_ha ih_hb ih_hp =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.usub (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)

    | refl ha ih_ha =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.refl (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ)

    | zeroLe ha ih_ha =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.zeroLe (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ)

    | decide ha hb hab =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          (HasType.decide (ctx := Δ) (ghost := true) ha hb hab)

    | decideConverted ha hb ca cb hm hn hmn ih_ha ih_hb =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.decideConverted (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
            (by simpa [Term.subst, substArgs] using ca.substitution σ)
            (by simpa [Term.subst, substArgs] using cb.substitution σ) hm hn hmn

    | @elements n xs Γ mode hn hb hs ih_hs =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        have ht := HasType.elements (ctx := Δ) (ghost := true)
          (xs := xs.map (Term.subst σ)) (n := n) (by simpa using hn) (by simpa using hb)
          (fun y hy => by
            obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
            simpa [Term.subst,substArgs] using ih_hs x hx Δ σ hσ)
        simpa [Term.subst,substArgs,Op.binders,liftSub] using ht

    | index ha hi hp ih_ha ih_hi ih_hp =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.index (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hi Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)

    | arith ha hb ih_ha ih_hb =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.arith (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)

    | strict ha hb ih_ha ih_hb =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.strict (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)

    | ltAdd ha hb hc hp ih_ha ih_hb ih_hc ih_hp =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.ltAdd (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hc Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)

    | ltCancel ha hb hc hp ih_ha ih_hb ih_hc ih_hp =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.ltCancel (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hc Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)

    | ltLe ha hb hc hp hq ih_ha ih_hb ih_hc ih_hp ih_hq =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.ltLe (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hc Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hq Δ σ hσ)

    | transport hf he hp ih_hf ih_he ih_hp =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.transport
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hf Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_he Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)

    | refine hp ih_hp =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.refine (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)

    | pack hp ha hq ih_hp ih_ha ih_hq =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.pack
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ)
            (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hq Δ σ hσ)

    | witness hs ih_hs =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.witness (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hs Δ σ hσ)

    | proof hs ih_hs =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        simpa [Term.subst, substArgs, Op.binders, liftSub] using
          HasType.proof (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hs Δ σ hσ)

    | convert ht hc ih_ht =>
        first | intro Δ σ hσ | rename_i Δ σ hσ
        exact .convert (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ht Δ σ hσ) (hc.substitution σ)

theorem Binder.ghostSubstitution {Γ : Context} {e : Bool} {A : Term} {s : SortTag}
    (h : Binder Γ e A s) {Δ : Context} {σ : Nat → Term}
    (hσ : Ghost.Substitution Γ Δ σ) : Binder Δ e (A.subst σ) s :=
  ghost_substitution_mutual.1 Γ e A s h Δ σ hσ

/-- Simultaneous typed substitution transports every existing rule into ghost
mode, including dependent result types, evidence and refinement projections. -/
theorem HasType.ghostSubstitution {Γ : Context} {mode : Bool} {t A : Term}
    (h : HasType Γ mode t A) {Δ : Context} {σ : Nat → Term}
    (hσ : Ghost.Substitution Γ Δ σ) : HasType Δ true (t.subst σ) (A.subst σ) :=
  ghost_substitution_mutual.2 Γ mode t A h Δ σ hσ

namespace Ghost

theorem Substitution.single {Γ : Context} {a A : Term} (e : Bool)
    (ha : HasType Γ true a A) : Substitution (⟨A,e⟩ :: Γ) Γ (single a) := by
  intro x b hx
  cases x with
  | zero =>
      simp only [lookup,Option.some.injEq] at hx
      cases hx
      simpa only [NativeKernel.single,Term.shift_subst_single] using ha
  | succ x =>
      simp only [lookup] at hx
      obtain ⟨b₀,h₀,he⟩ := Option.map_eq_some_iff.mp hx
      subst b
      simp only [NativeKernel.single,Term.shift_subst_single]
      exact .var h₀ (Or.inl rfl)

end Ghost

/-- Remove one binder using an independently typed argument, retaining the
capture-avoiding dependent substitution in the resulting type. -/
theorem HasType.ghostInstantiate {Γ : Context} {mode e : Bool} {A body B a : Term}
    (hb : HasType (⟨A,e⟩ :: Γ) mode body B) (ha : HasType Γ true a A) :
    HasType Γ true (body.subst (single a)) (B.subst (single a)) :=
  hb.ghostSubstitution (Ghost.Substitution.single e ha)

end Jihoo.NativeKernel
