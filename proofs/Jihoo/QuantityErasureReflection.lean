import Jihoo.QuantityErasure

namespace Jihoo.Quantity.Erasure
open Substitution

/-- Every execution after partial event relabeling has an original execution.
This preserves control choices and termination, not the discarded event names. -/
theorem finishes_relabel_reflect (run : Finishes d xs) :
    ∀ c ρ, c.relabel ρ = d → ∃ ys, Finishes c ys ∧ ys.filterMap ρ = xs := by
  induction run with
  | pure =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case pure => exact ⟨[], .pure, by simp⟩
      case use k =>
        cases hk : ρ k <;> simp_all
        exact ⟨[k], .use, by simp [hk]⟩
  | use =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k =>
        cases hk : ρ k <;> simp_all
        exact ⟨[k], .use, by simp [hk]⟩
  | seq ha hb ia ib =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k => cases hk : ρ k <;> simp_all
      case seq a b =>
        obtain ⟨as, ha, ea⟩ := ia a ρ (by simp_all)
        obtain ⟨bs, hb, eb⟩ := ib b ρ (by simp_all)
        exact ⟨as ++ bs, .seq ha hb, by simp [ea, eb]⟩
  | left ha ih =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k => cases hk : ρ k <;> simp_all
      case branch a b =>
        obtain ⟨ys, hy, ey⟩ := ih a ρ (by simp_all)
        exact ⟨ys, .left hy, ey⟩
  | right ha ih =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k => cases hk : ρ k <;> simp_all
      case branch a b =>
        obtain ⟨ys, hy, ey⟩ := ih b ρ (by simp_all)
        exact ⟨ys, .right hy, ey⟩
  | repeatZero =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k => cases hk : ρ k <;> simp_all
      case «repeat» b => exact ⟨[], .repeatZero, by simp⟩
  | repeatNext ha hb ia ib =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k => cases hk : ρ k <;> simp_all
      case «repeat» b =>
        obtain ⟨as, ha, ea⟩ := ia b ρ (by simp_all)
        obtain ⟨bs, hb, eb⟩ := ib (.repeat b) ρ (by simp_all [Control.relabel])
        exact ⟨as ++ bs, .repeatNext ha hb, by simp [ea, eb]⟩
  | once ha ih =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k => cases hk : ρ k <;> simp_all
      case once b =>
        obtain ⟨ys, hy, ey⟩ := ih b ρ (by simp_all)
        exact ⟨ys, .once hy, ey⟩
  | closure =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k => cases hk : ρ k <;> simp_all
      case closure b => exact ⟨[], .closure, by simp⟩
  | erased =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k => cases hk : ρ k <;> simp_all
      case erased b => exact ⟨[], .erased, by simp⟩
  | bind ha ih =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k => cases hk : ρ k <;> simp_all
      case scope mode b =>
        obtain ⟨ys, hy, ey⟩ := ih b (liftPartial ρ) (by simp_all)
        exact ⟨discharge ys, .bind hy, by rw [← discharge_filterMap, ey]⟩



/-- Reflection also covers finite prefixes that do not finish successfully. -/
theorem prefix_relabel_reflect (run : Prefix d xs) :
    ∀ c ρ, c.relabel ρ = d → ∃ ys, Prefix c ys ∧ ys.filterMap ρ = xs := by
  induction run with
  | start => intro c ρ _; exact ⟨[], .start, rfl⟩
  | use =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k =>
        cases hk : ρ k <;> simp_all
        exact ⟨[k], .use, by simp [hk]⟩
  | seqLeft ha ih =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k => cases hk : ρ k <;> simp_all
      case seq a b =>
        obtain ⟨ys, hy, ey⟩ := ih a ρ (by simp_all)
        exact ⟨ys, .seqLeft hy, ey⟩
  | seqRight ha hb ih =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k => cases hk : ρ k <;> simp_all
      case seq a b =>
        obtain ⟨as, ha, ea⟩ := finishes_relabel_reflect ha a ρ (by simp_all)
        obtain ⟨bs, hb, eb⟩ := ih b ρ (by simp_all)
        exact ⟨as ++ bs, .seqRight ha hb, by simp [ea, eb]⟩
  | left ha ih =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k => cases hk : ρ k <;> simp_all
      case branch a b =>
        obtain ⟨ys, hy, ey⟩ := ih a ρ (by simp_all)
        exact ⟨ys, .left hy, ey⟩
  | right ha ih =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k => cases hk : ρ k <;> simp_all
      case branch a b =>
        obtain ⟨ys, hy, ey⟩ := ih b ρ (by simp_all)
        exact ⟨ys, .right hy, ey⟩
  | repeatNext ha hb ih =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k => cases hk : ρ k <;> simp_all
      case «repeat» b =>
        obtain ⟨as, ha, ea⟩ := finishes_relabel_reflect ha b ρ (by simp_all)
        obtain ⟨bs, hb, eb⟩ := ih (.repeat b) ρ (by simp_all [Control.relabel])
        exact ⟨as ++ bs, .repeatNext ha hb, by simp [ea, eb]⟩
  | repeatBody ha ih =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k => cases hk : ρ k <;> simp_all
      case «repeat» b =>
        obtain ⟨ys, hy, ey⟩ := ih b ρ (by simp_all)
        exact ⟨ys, .repeatBody hy, ey⟩
  | once ha ih =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k => cases hk : ρ k <;> simp_all
      case once b =>
        obtain ⟨ys, hy, ey⟩ := ih b ρ (by simp_all)
        exact ⟨ys, .once hy, ey⟩
  | bind ha ih =>
      intro c ρ h
      cases c <;> simp_all [Control.relabel]
      case use k => cases hk : ρ k <;> simp_all
      case scope mode b =>
        obtain ⟨ys, hy, ey⟩ := ih b (liftPartial ρ) (by simp_all)
        exact ⟨discharge ys, .bind hy, by rw [← discharge_filterMap, ey]⟩



private theorem repeat_finishes_map
    (h : ∀ xs, Finishes b xs → Finishes a xs) (run : Finishes c xs) :
    c = .repeat b → Finishes (.repeat a) xs := by
  induction run <;> intro eq <;> cases eq
  · exact .repeatZero
  · exact .repeatNext (h _ ‹Finishes b _›) (by apply_assumption; rfl)

private theorem repeat_prefix_map
    (hf : ∀ xs, Finishes b xs → Finishes a xs)
    (hp : ∀ xs, Prefix b xs → Prefix a xs) (run : Prefix c xs) :
    c = .repeat b → Prefix (.repeat a) xs := by
  induction run <;> intro eq <;> cases eq
  · exact .start
  · exact .repeatNext (hf _ ‹Finishes b _›) (by apply_assumption; rfl)
  · exact .repeatBody (hp _ ‹Prefix b _›)

/-- Erasure cannot invent a completed outer-resource trace, even for unchecked
controls. It removes ghost observations, not runtime choices or traps. -/
theorem finishes_reflect (c : Control) : Finishes (erase c) xs → Finishes c xs := by
  induction c generalizing xs with
  | pure | use | trap | closure => intro h; cases h <;> constructor
  | erased b => intro h; cases h; exact .erased
  | seq a b ia ib => intro h; cases h with | seq ha hb => exact .seq (ia ha) (ib hb)
  | branch a b ia ib =>
      intro h; cases h with
      | left ha => exact .left (ia ha)
      | right hb => exact .right (ib hb)
  | «repeat» b ih => intro h; exact repeat_finishes_map (fun _ => ih) h rfl
  | once b ih => intro h; cases h with | once hb => exact .once (ih hb)
  | scope mode b ih =>
      intro h
      cases mode with
      | erased =>
          obtain ⟨ys, hy, eq⟩ := finishes_relabel_reflect h (erase b) dropBorrow rfl
          rw [drop_borrow_trace] at eq
          rw [← eq]
          exact .bind (ih hy)
      | linear | unrestricted | borrowed => cases h with | bind hb => exact .bind (ih hb)

/-- No new finite observations are introduced, including observations ending
before a trap and observations of repeated execution. -/
theorem prefix_reflect (c : Control) : Prefix (erase c) xs → Prefix c xs := by
  induction c generalizing xs with
  | pure | use | trap | closure => intro h; cases h <;> constructor
  | erased b => intro h; cases h; exact .start
  | seq a b ia ib =>
      intro h; cases h with
      | start => exact .start
      | seqLeft ha => exact .seqLeft (ia ha)
      | seqRight ha hb => exact .seqRight (finishes_reflect a ha) (ib hb)
  | branch a b ia ib =>
      intro h; cases h with
      | start => exact .start
      | left ha => exact .left (ia ha)
      | right hb => exact .right (ib hb)
  | «repeat» b ih =>
      intro h
      exact repeat_prefix_map (fun _ => finishes_reflect b) (fun _ => ih) h rfl
  | once b ih =>
      intro h; cases h with
      | start => exact .start
      | once hb => exact .once (ih hb)
  | scope mode b ih =>
      intro h
      cases mode with
      | erased =>
          obtain ⟨ys, hy, eq⟩ := prefix_relabel_reflect h (erase b) dropBorrow rfl
          rw [drop_borrow_trace] at eq
          rw [← eq]
          exact .bind (ih hy)
      | linear | unrestricted | borrowed =>
          cases h with
          | start => exact .start
          | bind hb => exact .bind (ih hb)

theorem finishes_iff : Finishes (erase c) xs ↔ Finishes c xs :=
  ⟨finishes_reflect c, finishes_forward⟩

theorem prefix_iff : Prefix (erase c) xs ↔ Prefix c xs :=
  ⟨prefix_reflect c, prefix_forward⟩

/-- An erased program has a terminating execution exactly when the original
control does. This says nothing about values or infinite-trace productivity. -/
theorem may_terminate_iff : (∃ xs, Finishes (erase c) xs) ↔ ∃ xs, Finishes c xs := by
  simp only [finishes_iff]

end Jihoo.Quantity.Erasure
