import Jihoo.QuantityErasureReflection

/-! Slot identity for a lowering environment containing ghost holes. Lists here
are newest-binder first; native core_lower.jh stores the reverse orientation and
looks up env[env.len - 1 - k]. This is a specification lemma, not a verification
of native array access or the whole lowering implementation. -/
namespace Jihoo.Quantity.Erasure.Slots

/-- Surviving runtime values in original binder order. -/
def compact (slots : List (Option α)) : List α := slots.filterMap id

/-- The position of a surviving binder after ghost holes are removed. -/
def position : List (Option α) → Nat → Option Nat
  | [], _ => none
  | none :: _, 0 => none
  | some _ :: _, 0 => some 0
  | none :: rest, k + 1 => position rest k
  | some _ :: rest, k + 1 => (position rest k).map Nat.succ

/-- Surviving names resolve to the identical value, without conflating slots
that happen to contain equal values. -/
theorem lookup (slots : List (Option α)) (h : position slots k = some j) :
    (compact slots)[j]? = (slots[k]?).join := by
  induction slots generalizing k j with
  | nil => simp [position] at h
  | cons slot rest ih =>
      cases slot <;> cases k <;> simp_all [position, compact]
      case none.succ k => exact ih h
      case some.zero value => subst j; simp
      case some.succ value k =>
        obtain ⟨i, hi, rfl⟩ := h
        simpa [compact] using ih hi

/-- Removing holes cannot alias two distinct original binder identities. -/
theorem position_injective (slots : List (Option α))
    (hk : position slots k = some j) (hl : position slots l = some j) : k = l := by
  induction slots generalizing k l j with
  | nil => simp [position] at hk
  | cons slot rest ih =>
      cases slot <;> cases k <;> cases l <;> simp_all [position]
      case none.succ.succ k l => exact ih hk hl
      case some.zero.succ value l => obtain ⟨i, _, eq⟩ := hl; omega
      case some.succ.zero value k => obtain ⟨i, _, eq⟩ := hk; omega
      case some.succ.succ value k l =>
        obtain ⟨i, hi, rfl⟩ := hk
        obtain ⟨i', hi', eq⟩ := hl
        have same : i' = i := Nat.succ.inj eq
        subst i'
        exact ih hi hi'

/-- Missing, out-of-range and explicitly erased slots never become readable. -/
theorem missing (slots : List (Option α)) :
    position slots k = none ↔ (slots[k]?).join = none := by
  induction slots generalizing k with
  | nil => simp [position]
  | cons slot rest ih => cases slot <;> cases k <;> simp_all [position]

end Jihoo.Quantity.Erasure.Slots
