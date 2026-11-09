import Jihoo.LoweringEnvironment

/-! Compose checked ownership, erasure and capture-layout reconstruction.
Resource names denote already-resolved ownership identities. The native
projection and its relation to actual MIR execution remain explicit obligations. -/
namespace Jihoo.OwnershipLowering
open LoweringEnvironment Quantity Quantity.Substitution

/-- Oldest-first source slot to packed operand position. Ghosts have no
operand; hypotheses reserve their entire node-plus-extra block but are not
scalar owners. -/
def scalarPosition : List Shape → Nat → Option Nat
  | [], _ => none
  | .value :: _, 0 => some 0
  | .ghost :: _, 0 | .hypothesis _ :: _, 0 => none
  | shape :: rest, k + 1 => (scalarPosition rest k).map (shape.width + ·)

/-- Quantity names use newest-first de Bruijn order; packed operands use
oldest-first call order. The guard excludes saturating out-of-range lookup. -/
def resourceMap (shapes : List Shape) (k : Nat) : Option Nat :=
  if k < shapes.length then scalarPosition shapes (shapes.length - 1 - k) else none

theorem scalar_injective (hk : scalarPosition shapes k = some r)
    (hl : scalarPosition shapes l = some r) : k = l := by
  induction shapes generalizing k l r with
  | nil => simp [scalarPosition] at hk
  | cons shape rest ih =>
      cases shape <;> cases k <;> cases l <;> simp_all [scalarPosition, Shape.width]
      case ghost.succ.succ k l => exact ih hk hl
      case value.zero.succ l => obtain ⟨i, _, eq⟩ := hl; omega
      case value.succ.zero k => obtain ⟨i, _, eq⟩ := hk; omega
      case value.succ.succ k l =>
        obtain ⟨i, hi, rfl⟩ := hk
        obtain ⟨j, hj, eq⟩ := hl
        have : j = i := by omega
        subst j
        exact ih hi hj
      case hypothesis.succ.succ extra k l =>
        obtain ⟨i, hi, rfl⟩ := hk
        obtain ⟨j, hj, eq⟩ := hl
        have : j = i := by omega
        subst j
        exact ih hi hj

theorem resource_injective (hk : resourceMap shapes k = some r)
    (hl : resourceMap shapes l = some r) : k = l := by
  simp only [resourceMap] at hk hl
  split at hk <;> try contradiction
  split at hl <;> try contradiction
  have he := scalar_injective hk hl
  omega

/-- A scalar owner is never dropped, and its packed payload is exactly the
original value. Hypothesis blocks shift its location by their full width. -/
theorem scalar_payload (h : env[k]? = some (.value value)) :
    ∃ r, scalarPosition (layout env) k = some r ∧ (pack env)[r]? = some value := by
  induction env generalizing k with
  | nil => simp at h
  | cons slot env ih =>
      cases k with
      | zero =>
          simp at h
          subst slot
          exact ⟨0, rfl, rfl⟩
      | succ k =>
          simp only [List.getElem?_cons_succ] at h
          obtain ⟨r, hr, hv⟩ := ih h
          cases slot with
          | ghost => exact ⟨r, by simpa [layout, Slot.shape, scalarPosition, Shape.width] using hr,
              by simpa [pack, Slot.operands] using hv⟩
          | value a => exact ⟨1 + r,
              by simpa [layout, Slot.shape, scalarPosition, Shape.width] using hr,
              by simpa [pack, Slot.operands, Nat.add_comm] using hv⟩
          | hypothesis node extra =>
              refine ⟨extra.length + 1 + r, ?_, ?_⟩
              · simpa [layout, Slot.shape, scalarPosition, Shape.width] using
                  congrArg (Option.map (extra.length + 1 + ·)) hr
              · change ((node :: extra) ++ pack env)[(node :: extra).length + r]? = some value
                rw [List.getElem?_append_right (by omega)]
                simpa using hv

theorem resource_payload (h : nativeLookup env k = some (.value value)) :
    ∃ r, resourceMap (layout env) k = some r ∧ (pack env)[r]? = some value := by
  simp only [nativeLookup] at h
  split at h
  next hk =>
    obtain ⟨r, hr, hv⟩ := scalar_payload h
    exact ⟨r, by simpa [resourceMap, layout, hk] using hr, hv⟩
  next => contradiction

/-- Abstract runtime ownership control after ghost erasure and capture-slot
lowering. This is not an asserted translation of arbitrary native MIR. -/
def lowerControl (env : List (Slot α)) (c : Control) : Control :=
  (Quantity.Erasure.erase c).relabel (resourceMap (layout env))

/-- The full demand check (not just a chosen execution's count) survives
capture expansion, erasure and call-order conversion for a surviving resource. -/
theorem demand_preserved (mapped : resourceMap (layout env) k = some r)
    (checked : c.demand k = some n) : (lowerControl env c).demand r = some n := by
  have fiber : ∀ x, resourceMap (layout env) x = some r ↔ x = k := by
    intro x
    exact ⟨fun hx => resource_injective hx mapped, fun hx => hx ▸ mapped⟩
  rw [lowerControl, relabel_demand _ fiber]
  exact Quantity.Erasure.demand_preserved c checked

/-- Exact source/target correspondence of observable completed traces after
both transformations. Unmapped ghost/hypothesis events are filtered, so this
is not an assertion that arbitrary source resource names survive. -/
theorem finishes_iff : Finishes (lowerControl env c) xs ↔
    ∃ ys, Finishes c ys ∧ ys.filterMap (resourceMap (layout env)) = xs := by
  constructor
  · intro h
    obtain ⟨ys, hy, eq⟩ := Quantity.Erasure.finishes_relabel_reflect h
      (Quantity.Erasure.erase c) (resourceMap (layout env)) rfl
    exact ⟨ys, Quantity.Erasure.finishes_reflect c hy, eq⟩
  · rintro ⟨ys, hy, rfl⟩
    exact (Quantity.Erasure.finishes_forward hy).relabel _

theorem prefix_iff : Prefix (lowerControl env c) xs ↔
    ∃ ys, Prefix c ys ∧ ys.filterMap (resourceMap (layout env)) = xs := by
  constructor
  · intro h
    obtain ⟨ys, hy, eq⟩ := Quantity.Erasure.prefix_relabel_reflect h
      (Quantity.Erasure.erase c) (resourceMap (layout env)) rfl
    exact ⟨ys, Quantity.Erasure.prefix_reflect c hy, eq⟩
  · rintro ⟨ys, hy, rfl⟩
    exact (Quantity.Erasure.prefix_forward hy).relabel _

/-- One integrated endpoint. Source quantity checking, authentic capture
layout and positional value assignment yield the same owner value in the
callee and exact-once/at-most-once use in EVERY lowered-control execution.
No conclusion about native heap aliasing or actual MIR traces is implicit. -/
theorem checked_owner_pipeline
    (owner : nativeLookup caller k = some (.value value))
    (checked : c.demand k = some 1)
    (decoded : decode (layout caller) references = some callee)
    (assigned : references.map evaluate = pack caller) :
    ∃ r, resourceMap (layout caller) k = some r ∧
      references[r]?.map evaluate = some value ∧
      nativeLookup (callee.map (Slot.map evaluate)) k = some (.value value) ∧
      (∀ xs, Finishes (lowerControl caller c) xs → xs.count r = 1) ∧
      (∀ xs, Prefix (lowerControl caller c) xs → xs.count r ≤ 1) := by
  obtain ⟨r, hr, hv⟩ := resource_payload owner
  refine ⟨r, hr, ?_, ?_, ?_, ?_⟩
  · rw [← assigned] at hv
    simpa using hv
  · rw [callee_environment decoded assigned]
    exact owner
  · intro xs run
    exact run.count_eq (demand_preserved hr checked)
  · intro xs run
    exact run.count_le (demand_preserved hr checked)

end Jihoo.OwnershipLowering
