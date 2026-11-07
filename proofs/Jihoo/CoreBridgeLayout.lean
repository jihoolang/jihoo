import Jihoo.CoreBridgeChecks

namespace Jihoo.CoreBridge

inductive BinderKind where
  | index
  | value
  deriving DecidableEq, Repr

abbrev Layout := List BinderKind

def count (kind : BinderKind) : Layout → Nat
  | [] => 0
  | k :: ks => (if k = kind then 1 else 0) + count kind ks

def slot (kind : BinderKind) (x : Nat) : Layout → Nat
  | [] => 0
  | k :: ks =>
      if k = kind then match x with
        | 0 => 0
        | n + 1 => slot kind n ks + 1
      else slot kind x ks + 1

/-- A valid two-sorted variable is mapped to an existing unified binder of the
right sort. Invalid indices have a default slot but are outside this theorem. -/
theorem slot_spec (layout : Layout) (h : x < count kind layout) :
    slot kind x layout < layout.length ∧ layout[slot kind x layout]? = some kind := by
  induction layout generalizing x with
  | nil => simp [count] at h
  | cons k ks ih =>
      by_cases hk : k = kind
      · subst k
        cases x with
        | zero => simp [slot]
        | succ x =>
            have hx : x < count kind ks := by simp [count] at h; omega
            have result := ih hx
            simpa [slot] using result
      · have hx : x < count kind ks := by simpa [count, hk] using h
        have result := ih hx
        simpa [slot, hk] using result

/-- Distinct source namespaces cannot silently alias the same core variable. -/
theorem slots_disjoint (hi : i < count .index layout) (hv : v < count .value layout) :
    slot .index i layout ≠ slot .value v layout := by
  intro same
  have a := (slot_spec layout hi).2
  have b := (slot_spec layout hv).2
  rw [same] at a
  rw [b] at a
  cases a

theorem slot_injective (layout : Layout) (hx : x < count kind layout)
    (hy : y < count kind layout) (same : slot kind x layout = slot kind y layout) : x = y := by
  induction layout generalizing x y with
  | nil => simp [count] at hx
  | cons k ks ih =>
      by_cases hk : k = kind
      · subst k
        cases x <;> cases y <;> simp [slot] at same ⊢
        case succ.succ x y =>
          apply ih (by simp [count] at hx; omega)
            (by simp [count] at hy; omega) same
      · apply ih (by simpa [count, hk] using hx) (by simpa [count, hk] using hy)
        simpa [slot, hk] using same

/-- Translation with a real mixed layout always produces unified scoped syntax. -/
theorem layout_encode_scoped {t : Term}
    (h : t.Scoped (count .index layout) (count .value layout)) :
    (t.encode (fun i => slot .index i layout) (fun v => slot .value v layout)).Scoped layout.length := by
  apply Term.encode_scoped h
  · intro i hi
    exact (slot_spec layout hi).1
  · intro v hv
    exact (slot_spec layout hv).1

end Jihoo.CoreBridge
