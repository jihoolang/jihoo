import Jihoo.OwnershipLowering

/-! Concrete sequential parameter numbering and positional call entry.
This discharges the abstract frame/assignment premises inside the model; native
MIR entry semantics and typed source/control correspondence remain obligations. -/
namespace Jihoo.CallEntry
open LoweringEnvironment Quantity OwnershipLowering

def width (shapes : List Shape) : Nat := (shapes.map Shape.width).sum

def numberSlot (shape : Shape) (base : Nat) : Slot Nat := match shape with
  | .ghost => .ghost
  | .value => .value base
  | .hypothesis n => .hypothesis base (List.range' (base + 1) n)

def number : List Shape → Nat → List (Slot Nat)
  | [], _ => []
  | shape :: rest, base => numberSlot shape base :: number rest (base + shape.width)

private theorem numberSlot_shape (shape : Shape) : (numberSlot shape base).shape = shape := by
  cases shape <;> simp [numberSlot, Slot.shape]

private theorem numberSlot_operands (shape : Shape) :
    (numberSlot shape base).operands = List.range' base shape.width := by
  cases shape <;> simp [numberSlot, Slot.operands, Shape.width, List.range'_succ]

theorem number_layout (shapes : List Shape) : layout (number shapes base) = shapes := by
  induction shapes generalizing base with
  | nil => rfl
  | cons shape rest ih =>
      change (numberSlot shape base).shape :: layout (number rest _) = shape :: rest
      rw [numberSlot_shape, ih]

theorem number_pack (shapes : List Shape) : pack (number shapes base) = List.range' base (width shapes) := by
  induction shapes generalizing base with
  | nil => rfl
  | cons shape rest ih =>
      change (numberSlot shape base).operands ++ pack (number rest _) = _
      rw [numberSlot_operands, ih]
      simp [width]

/-- Native lowering allocates captures first and explicitly applied arguments
second. These two loops agree with numbering the concatenated layout. -/
theorem number_append (first second : List Shape) :
    number (first ++ second) base = number first base ++ number second (base + width first) := by
  induction first generalizing base with
  | nil => simp [number, width]
  | cons shape rest ih => simp [number, width, ih, Nat.add_assoc]

theorem number_decode (caller : List (Slot α)) :
    decode (layout caller) (List.range' base (pack caller).length) = some (number (layout caller) base) := by
  apply decode_iff.mpr
  constructor
  · exact number_layout _
  · rw [number_pack, operand_count]
    rfl

/-- A reserved prefix (including the return slot), then the recursion's own
node, then its positional operands. No previous local is overwritten. -/
def entry (reserved : List α) (node : α) (caller : List (Slot α)) : List α :=
  reserved ++ node :: pack caller

def references (reserved : List α) (caller : List (Slot β)) : List Nat :=
  List.range' (reserved.length + 1) (pack caller).length

private theorem read_appended (before payload suffix : List α) (fallback : α) :
    (List.range' before.length payload.length).map
      (fun i => ((before ++ payload ++ suffix)[i]?).getD fallback) = payload := by
  induction payload generalizing before with
  | nil => simp
  | cons a payload ih =>
      rw [List.length_cons, List.range'_succ, List.map_cons]
      have head : ((before ++ (a :: payload) ++ suffix)[before.length]?).getD fallback = a := by
        simp
      rw [head]
      have tail := ih (before ++ [a])
      simpa [List.length_append, List.append_assoc] using congrArg (List.cons a) tail

/-- Every generated reference is initialized, independently of any fallback
used to represent total store lookup in the assignment lemma. -/
theorem reference_initialized (h : r ∈ references reserved caller) :
    ∃ value, (entry reserved node caller)[r]? = some value := by
  obtain ⟨i, hi, hr⟩ := List.mem_range'.mp h
  have bound : r < (entry reserved node caller).length := by
    simp only [entry, List.length_append, List.length_cons]
    omega
  exact ⟨(entry reserved node caller)[r], by simp [bound]⟩

theorem references_distinct : (references reserved caller).Nodup := List.nodup_range'

theorem references_fresh (h : r ∈ references reserved caller) : reserved.length < r := by
  obtain ⟨i, _, hr⟩ := List.mem_range'.mp h
  omega

theorem reserved_unchanged (h : i < reserved.length) :
    (entry reserved node caller)[i]? = reserved[i]? := List.getElem?_append_left h

/-- Positional assignment is derived from entry construction, not assumed as
a whole-list correspondence. It holds for every choice of lookup fallback. -/
theorem entry_assignment (reserved : List α) (node fallback : α) (caller : List (Slot α)) :
    (references reserved caller).map
      (fun i => ((entry reserved node caller)[i]?).getD fallback) = pack caller := by
  have h := read_appended (reserved ++ [node]) (pack caller) [] fallback
  simpa [references, entry, List.length_append, List.append_assoc] using h

/-- The previous integrated ownership endpoint now has a constructed callee
and parameter assignment. Only source slot designation and checked demand are
premises; the claim remains about the stated entry/control semantics. -/
theorem constructed_owner_pipeline {caller : List (Slot α)} {value : α}
    (owner : nativeLookup caller k = some (.value value))
    (checked : c.demand k = some 1) (reserved : List α) (node fallback : α) :
    let evaluate := fun i => ((entry reserved node caller)[i]?).getD fallback
    let callee := number (layout caller) (reserved.length + 1)
    ∃ r, resourceMap (layout caller) k = some r ∧
      (references reserved caller)[r]?.map evaluate = some value ∧
      nativeLookup (callee.map (Slot.map evaluate)) k = some (.value value) ∧
      (∀ xs, Finishes (lowerControl caller c) xs → xs.count r = 1) ∧
      (∀ xs, Prefix (lowerControl caller c) xs → xs.count r ≤ 1) := by
  exact checked_owner_pipeline owner checked (number_decode caller)
    (entry_assignment reserved node fallback caller)

end Jihoo.CallEntry
