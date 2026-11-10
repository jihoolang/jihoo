import Jihoo.CorePrimitiveSafety

/-! Literal subtraction is a genuine contextual computation, with its guards
retained in untyped conversion. Symbolic cancellation and effects are not added. -/
namespace Jihoo.CoreBridge.Raw.Beta

private theorem Par.invalid_sub_shape
    (bad : ¬ (b ≤ a ∧ a < wordBound))
    (h : Par (.usub (.natural a) (.natural b) p) u) :
    ∃ q, u = .usub (.natural a) (.natural b) q := by
  cases h with
  | subLiteral _ _ _ hb ha => exact False.elim (bad ⟨hb, ha⟩)
  | usub ha hb hp => cases ha; cases hb; exact ⟨_, rfl⟩

private theorem Star.invalid_sub_shape (h : Star t u) :
    ∀ a b p, t = .usub (.natural a) (.natural b) p →
      ¬ (b ≤ a ∧ a < wordBound) → ∃ q, u = .usub (.natural a) (.natural b) q := by
  induction h with
  | refl => intro a b p eq _; exact ⟨p, eq⟩
  | cons hs _ ih =>
      intro a b p eq bad
      subst eq
      obtain ⟨q, eq⟩ := hs.invalid_sub_shape bad
      exact ih a b q eq bad

private theorem Star.literal_shape (h : Star t u) (ht : t = .natural n) :
    u = .natural n := by
  induction h with
  | refl => exact ht
  | cons hp _ ih => subst ht; cases hp; exact ih rfl

/-- Even arbitrary untyped beta expansion cannot make an underflowing or
out-of-word subtraction convertible to a numeral by saturating subtraction. -/
theorem Conv.invalid_sub_not_literal (bad : ¬ (b ≤ a ∧ a < wordBound)) :
    ¬ Conv (.usub (.natural a) (.natural b) p) (.natural n) := by
  intro converted
  obtain ⟨u, left, right⟩ := converted.church_rosser
  obtain ⟨q, eq⟩ := left.invalid_sub_shape a b p rfl bad
  have same := eq.symm.trans (right.literal_shape rfl)
  contradiction

theorem Conv.literal_sub_unique (hb : b ≤ a) (ha : a < wordBound)
    (converted : Conv (.usub (.natural a) (.natural b) p) (.natural n)) :
    a - b = n :=
  ((Conv.subLiteral a b p hb ha).symm.trans converted).natural_injective

/-- Closed typing derives the contraction guards, including the maximum-word
case, without requiring the caller to normalize or interpret the proof term. -/
theorem HasType.closed_sub_computes
    (typed : HasType (fun _ => none) (.usub (.natural a) (.natural b) p) T) :
    Computation.Step (.usub (.natural a) (.natural b) p) (.natural (a - b)) ∧
      HasType (fun _ => none) (.natural (a - b)) T := by
  have safe := typed.closed_usub_safe
  have bound := typed.usub_inversion.1.natural_bound
  exact ⟨.subLiteral a b p safe.1 bound, safe.2.2⟩

/-- Compose operand evaluation with the primitive contraction. This returns an
actual reduction trace at the original type, not only a separately typed value. -/
theorem HasType.evaluated_sub_computes
    (typed : HasType (fun _ => none) (.usub a b p) T)
    (ha : Computation.Steps a (.natural x)) (hb : Computation.Steps b (.natural y)) :
    Computation.Steps (.usub a b p) (.natural (x - y)) ∧
      HasType (fun _ => none) (.natural (x - y)) T := by
  have left := ha.map (fun t => .usub t b p) (fun ht => .usubLeft ht)
  have right := hb.map (fun t => .usub (.natural x) t p) (fun ht => .usubRight ht)
  have prepared := left.trans right
  obtain ⟨step, result⟩ := (Computation.preservation_steps typed prepared).closed_sub_computes
  exact ⟨prepared.trans (.next step .refl), result⟩

end Jihoo.CoreBridge.Raw.Beta
