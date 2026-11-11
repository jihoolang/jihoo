import Jihoo.BoundedMir

/-! Typed scalar entry arguments, separate from the closed MIR code format.
The existing closed interpreter and admission API are unchanged. An entry does
not assert that its code is valid: callers must establish `valid c` separately.
No external pointers, address tags, or pre-existing heap objects are accepted.
As in `BoundedMir.constant`, the modeled i64 payload is a nonnegative Nat below
2^63; this is not a model of negative signed arguments. -/
namespace Jihoo.BoundedMir

structure Entry where
  argumentSlots : Array Nat
  deriving DecidableEq, Repr

def argumentTypeSupported : Ty → Bool
  | .i64 | .u64 | .bool => true
  | _ => false

def argumentValueValid : Value → Bool
  | .i64 n => n < scalarBound
  | .u64 n => n < wordBound
  | .boolean _ => true
  | _ => false

/-- Argument positions are ordered, distinct, declared scalar locals other than
return local zero. Missing local declarations are rejected. -/
def entryValid (c : Code) (entry : Entry) : Bool :=
  decide entry.argumentSlots.toList.Nodup &&
  entry.argumentSlots.all (fun slot => slot != 0 &&
    (c.locals[slot]?.map argumentTypeSupported).getD false)

/-- Bind in declaration order. Both lists must end together. This helper is
used only after signature validation by `entryFrame`. -/
def bindArguments (c : Code) : List Nat → List Value → Frame → Option Frame
  | [], [], frame => some frame
  | slot :: slots, value :: values, frame =>
    if argumentValueValid value && c.locals[slot]? == some (valueType value) &&
        slot < frame.locals.size then
      bindArguments c slots values { frame with locals := frame.locals.set! slot (some value) }
    else none
  | _, _, _ => none

/-- Build a fresh empty-heap frame with only the declared argument locals set. -/
def entryFrame (c : Code) (entry : Entry) (values : List Value) : Option Frame :=
  if entryValid c entry then
    bindArguments c entry.argumentSlots.toList values (initial c)
  else none

@[simp] theorem argumentValueValid_i64 :
    argumentValueValid (.i64 n) = decide (n < scalarBound) := rfl
@[simp] theorem argumentValueValid_u64 :
    argumentValueValid (.u64 n) = decide (n < wordBound) := rfl
@[simp] theorem argumentValueValid_bool : argumentValueValid (.boolean b) = true := rfl
@[simp] theorem argumentValueValid_pointer : argumentValueValid (.pointer o i) = false := rfl
@[simp] theorem argumentValueValid_address : argumentValueValid (.address o) = false := rfl

theorem entryFrame_invalid (h : entryValid c entry = false) :
    entryFrame c entry values = none := by simp [entryFrame, h]

theorem bindArguments_arity (h : bindArguments c slots values frame = some out) :
    slots.length = values.length := by
  induction slots generalizing values frame with
  | nil => cases values <;> simp_all [bindArguments]
  | cons slot slots ih =>
    cases values with
    | nil => simp [bindArguments] at h
    | cons value values =>
      simp only [bindArguments] at h
      split at h
      · exact congrArg Nat.succ (ih h)
      · contradiction

theorem entryFrame_arity (h : entryFrame c entry values = some out) :
    entry.argumentSlots.size = values.length := by
  unfold entryFrame at h
  split at h
  · simpa using bindArguments_arity h
  · contradiction

theorem bindArguments_control (h : bindArguments c slots values frame = some out) :
    out.block = frame.block ∧ out.index = frame.index ∧ out.heap = frame.heap := by
  induction slots generalizing values frame with
  | nil => cases values <;> simp_all [bindArguments]
  | cons slot slots ih =>
    cases values with
    | nil => simp [bindArguments] at h
    | cons value values =>
      simp only [bindArguments] at h
      split at h
      · exact ih (frame := { frame with locals := frame.locals.set! slot (some value) }) h
      · contradiction

theorem entryFrame_control (h : entryFrame c entry values = some out) :
    out.block = 0 ∧ out.index = 0 ∧ out.heap = #[] := by
  unfold entryFrame at h
  split at h
  · exact bindArguments_control h
  · contradiction

theorem entryFrame_signature (h : entryFrame c entry values = some out) :
    entryValid c entry = true := by
  unfold entryFrame at h
  split at h
  · assumption
  · contradiction

theorem entryFrame_wrong_arity (h : entry.argumentSlots.size ≠ values.length) :
    entryFrame c entry values = none := by
  cases he : entryFrame c entry values with
  | none => rfl
  | some out => exact False.elim (h (entryFrame_arity he))

theorem entryValid_distinct (h : entryValid c entry = true) :
    entry.argumentSlots.toList.Nodup := by
  simp only [entryValid, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem bindArguments_size (h : bindArguments c slots values frame = some out) :
    out.locals.size = frame.locals.size := by
  induction slots generalizing values frame with
  | nil => cases values <;> simp_all [bindArguments]
  | cons slot slots ih =>
    cases values with
    | nil => simp [bindArguments] at h
    | cons value values =>
      simp only [bindArguments] at h
      split at h
      · simpa using ih (frame := { frame with locals := frame.locals.set! slot (some value) }) h
      · contradiction

theorem entryFrame_size (h : entryFrame c entry values = some out) :
    out.locals.size = c.locals.size := by
  unfold entryFrame at h
  split at h
  · simpa [initial] using bindArguments_size h
  · contradiction

/-! Small executable regression examples exercise the public checked entry API. -/
private def exampleCode : Code :=
  ⟨#[.i64, .u64, .u64, .i64, .bool, .ptr], #[⟨#[], .ret⟩]⟩
private def exampleEntry : Entry := ⟨#[1, 2, 3]⟩

example (hn : n < wordBound) (hi : i < wordBound) (hv : v < scalarBound) :
    (entryFrame exampleCode exampleEntry [.u64 n, .u64 i, .i64 v]).map
      (fun f => f.locals) = some #[none, some (.u64 n), some (.u64 i),
        some (.i64 v), none, none] := by
  have he : entryValid exampleCode exampleEntry = true := by decide +kernel
  unfold entryFrame
  rw [he]
  simp [bindArguments, exampleEntry, exampleCode, initial,
    argumentValueValid, valueType, hn, hi, hv, Array.set!, Array.replicate,
    Array.setIfInBounds]

example : (entryFrame exampleCode exampleEntry [.u64 4, .u64 2, .i64 9]).map
    (fun f => f.locals) = some #[none, some (.u64 4), some (.u64 2),
      some (.i64 9), none, none] := by decide +kernel
example : entryFrame exampleCode exampleEntry [.u64 4, .u64 2] = none := by decide +kernel
example : entryFrame exampleCode ⟨#[1, 1]⟩ [.u64 4, .u64 2] = none := by decide +kernel
example : entryFrame exampleCode ⟨#[0]⟩ [.i64 9] = none := by decide +kernel
example : entryFrame exampleCode ⟨#[6]⟩ [.u64 4] = none := by decide +kernel
example : entryFrame exampleCode ⟨#[1]⟩ [.i64 4] = none := by decide +kernel
example : entryFrame exampleCode ⟨#[3]⟩ [.i64 scalarBound] = none := by decide +kernel
example : entryFrame exampleCode ⟨#[1]⟩ [.u64 wordBound] = none := by decide +kernel
example : entryFrame exampleCode ⟨#[1]⟩ [.address 0] = none := by decide +kernel
example : entryFrame exampleCode ⟨#[5]⟩ [.pointer 0 0] = none := by decide +kernel
example : (entryFrame exampleCode ⟨#[4]⟩ [.boolean true]).map
    (fun f => (f.locals[4]?).join) = some (some (.boolean true)) := by decide +kernel

end Jihoo.BoundedMir
