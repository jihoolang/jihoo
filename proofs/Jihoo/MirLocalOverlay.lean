import Jihoo.BoundedMir

/-! Relocatable finite local roles over an otherwise unchanged MIR local array. -/
namespace Jihoo.MirLocal

open BoundedMir

/-- Replace the selected role, leaving all other role values unchanged. -/
def updateValues {size : Nat} (vals : Fin size → Option Value)
    (role : Fin size) (value : Option Value) : Fin size → Option Value :=
  fun r => if r = role then value else vals r

/-- Overlay role values at their selected physical local slots. Slots outside
    the original array do not extend it. Colliding slots are allowed here;
    lookup and update laws require the role-to-slot map to be injective. -/
noncomputable def overlay {size : Nat} (slots : Fin size → Nat)
    (original : Array (Option Value)) (vals : Fin size → Option Value) :
    Array (Option Value) := by
  classical
  exact Array.ofFn fun i : Fin original.size =>
    if h : ∃ r, slots r = i.val then vals h.choose else original[i]

@[simp] theorem overlay_size {size : Nat} (slots : Fin size → Nat)
    (original : Array (Option Value)) (vals : Fin size → Option Value) :
    (overlay slots original vals).size = original.size := by
  simp [overlay]

theorem overlay_lookup {size : Nat} (slots : Fin size → Nat)
    (original : Array (Option Value)) (vals : Fin size → Option Value)
    (hinj : ∀ a b, slots a = slots b → a = b) (r : Fin size)
    (hbound : slots r < original.size) :
    (overlay slots original vals)[slots r]! = vals r := by
  classical
  have hex : ∃ a, slots a = slots r := ⟨r, rfl⟩
  rw [getElem!_pos (overlay slots original vals) (slots r) (by simpa using hbound)]
  simp only [overlay, Array.getElem_ofFn]
  simp only [dite_eq_left hex]
  congr 1
  exact hinj _ _ hex.choose_spec

theorem overlay_lookup_opt {size : Nat} (slots : Fin size → Nat)
    (original : Array (Option Value)) (vals : Fin size → Option Value)
    (hinj : ∀ a b, slots a = slots b → a = b) (r : Fin size)
    (hbound : slots r < original.size) :
    (overlay slots original vals)[slots r]? = some (vals r) := by
  have hb : slots r < (overlay slots original vals).size := by simpa using hbound
  rw [getElem?_pos (overlay slots original vals) (slots r) hb,
    ← getElem!_pos (overlay slots original vals) (slots r) hb,
    overlay_lookup slots original vals hinj r hbound]

theorem overlay_other {size : Nat} (slots : Fin size → Nat)
    (original : Array (Option Value)) (vals : Fin size → Option Value)
    (i : Nat) (hother : ∀ r, slots r ≠ i) :
    (overlay slots original vals)[i]! = original[i]! := by
  classical
  by_cases hbound : i < original.size
  · have hn : ¬ ∃ r, slots r = i := by simpa using hother
    simp [getElem!_pos, hbound, overlay, hn]
  · simp [getElem!_neg, hbound]

theorem overlay_set! {size : Nat} (slots : Fin size → Nat)
    (original : Array (Option Value)) (vals : Fin size → Option Value)
    (hinj : ∀ a b, slots a = slots b → a = b) (r : Fin size)
    (hbound : slots r < original.size) (value : Option Value) :
    (overlay slots original vals).set! (slots r) value =
      overlay slots original (updateValues vals r value) := by
  apply Array.ext (by simp)
  intro i hi₁ hi₂
  rw [← getElem!_pos ((overlay slots original vals).set! (slots r) value) i hi₁, ← getElem!_pos (overlay slots original (updateValues vals r value)) i hi₂]
  by_cases heq : slots r = i
  · subst i
    rw [Array.getElem!_set!_self _ _ _ (by simpa using hbound),
      overlay_lookup slots original _ hinj r hbound]
    simp [updateValues]
  · rw [Array.getElem!_set!_ne _ _ _ _ heq]
    by_cases hex : ∃ a, slots a = i
    · obtain ⟨a, rfl⟩ := hex
      have hb : slots a < original.size := by simpa using hi₂
      rw [overlay_lookup slots original _ hinj a hb,
        overlay_lookup slots original _ hinj a hb]
      have hne : a ≠ r := by intro h; subst a; exact heq rfl
      simp [updateValues, hne]
    · have hn : ∀ a, slots a ≠ i := by simpa using hex
      rw [overlay_other slots original _ i hn, overlay_other slots original _ i hn]

theorem overlay_same {size : Nat} (slots : Fin size → Nat)
    (original : Array (Option Value)) (vals : Fin size → Option Value)
    (hvals : ∀ r, original[slots r]! = vals r) :
    overlay slots original vals = original := by
  classical
  apply Array.ext (by simp)
  intro i hi₁ hi₂
  simp only [overlay, Array.getElem_ofFn]
  split
  next h =>
    rw [← hvals h.choose, h.choose_spec, getElem!_pos original i hi₂]
  next => rfl

end Jihoo.MirLocal
