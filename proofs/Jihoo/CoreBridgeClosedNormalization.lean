import Jihoo.SimpleHeadNormalization
import Jihoo.CoreBridgeBetaEvidence

/-! Unconditional closed head normalization for the existing declarative Raw
fragment, and literal consistency. This is not full contextual normalization,
Core.normal refinement, a resource/fuel bound or semantic evaluation of indices. -/
namespace Jihoo.CoreBridge.Raw.Beta
open SimpleErasure

/-- A purely syntactic progress alternative; neutral open heads are normal.
No typing, termination or arithmetic premise is built into this lemma. -/
theorem head_progress (t : Raw) : headNormal t = true ∨ ∃ u, HeadStep t u := by
  induction t using Raw.rec (motive_2 := fun _ => True)
  case app f a ihf iha =>
    cases f
    case lam e A body => exact .inr ⟨_, .beta⟩
    all_goals
      rcases ihf with hn | ⟨u, hu⟩
      · left
        change (headNormal _ && true) = true
        simpa only [Bool.and_true] using hn
      · exact .inr ⟨_, .function hu⟩
  all_goals first | trivial | exact .inl rfl

theorem head_accessible_normalizes (h : Acc (fun u v => HeadStep v u) t) :
    ∃ u, Steps t u ∧ headNormal u = true := by
  induction h with
  | intro t h ih =>
      rcases head_progress t with hn | ⟨u, hu⟩
      · exact ⟨t, .refl, hn⟩
      · obtain ⟨v, hv, hn⟩ := ih u hu
        exact ⟨v, .next hu.beta_step hv, hn⟩

/-- The simple accessibility premise from #53 is now discharged by typing. -/
theorem HasType.closed_head_accessible (h : HasType (fun _ => none) t A) :
    Acc (fun u v => HeadStep v u) t := by
  obtain ⟨a, _, typed⟩ := closed_erasure h
  exact accessibility_transfer typed.closed_accessible

theorem HasType.closed_head_normalizes (h : HasType (fun _ => none) t A) :
    ∃ u, Steps t u ∧ headNormal u = true :=
  head_accessible_normalizes h.closed_head_accessible

/-- Unlike the earlier finite-witness endpoint, no normalization/trace premise
is required. Internal conversions and higher-order arguments are included. -/
theorem HasType.closed_literal_eq
    (h : HasType (fun _ => none) t (.eq (.natural m) (.natural n))) : m = n := by
  obtain ⟨u, steps, hn⟩ := h.closed_head_normalizes
  exact h.reduces_literal_eq steps hn

theorem HasType.closed_literal_lt
    (h : HasType (fun _ => none) t (.lt (.natural m) (.natural n))) : m < n := by
  obtain ⟨u, steps, hn⟩ := h.closed_head_normalizes
  exact h.reduces_literal_lt steps hn

theorem no_closed_false_equality (hne : m ≠ n) :
    ¬ HasType (fun _ => none) t (.eq (.natural m) (.natural n)) :=
  fun h => hne h.closed_literal_eq

theorem no_closed_false_bound (hn : ¬ m < n) :
    ¬ HasType (fun _ => none) t (.lt (.natural m) (.natural n)) :=
  fun h => hn h.closed_literal_lt

end Jihoo.CoreBridge.Raw.Beta
