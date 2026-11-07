import Jihoo.TypeIndexNormalization

/-! The six-artifact envelope fixes the roles of its two schema-5 lists.
No record can silently switch between term-root and type-root reduction. -/
namespace Jihoo.GraphCertificates.TypeIndexNormalization.Wire
open Typing.Wire

def validateBytes (beforeBytes middleBytes afterBytes typingBytes headBytes typeBytes : ByteArray)
    (q : Typing.Evidence.Claim) : Bool :=
  match decodeSnapshot beforeBytes, decodeSnapshot middleBytes, decodeSnapshot afterBytes,
      Typing.Wire.decode typingBytes, HeadNormalization.Wire.decode headBytes,
      HeadNormalization.Wire.decode typeBytes with
  | some before, some middle, some after, some typing, some heads, some types =>
      TypeIndexNormalization.validate before middle after typing heads types q
  | _, _, _, _, _, _ => false

theorem validateBytes_sound
    (h : validateBytes beforeBytes middleBytes afterBytes typingBytes headBytes typeBytes q = true) :
    ∃ before middle after typing heads types,
      encodeSnapshot before = beforeBytes ∧ encodeSnapshot middle = middleBytes ∧
      encodeSnapshot after = afterBytes ∧ Typing.Wire.encode typing = typingBytes ∧
      HeadNormalization.Wire.encode heads = headBytes ∧
      HeadNormalization.Wire.encode types = typeBytes ∧ before.Matches typing ∧
      Sound before middle after heads types ∧ Typing.Evidence.Realized after q := by
  cases hb : decodeSnapshot beforeBytes <;> cases hm : decodeSnapshot middleBytes <;>
    cases ha : decodeSnapshot afterBytes <;> cases ht : Typing.Wire.decode typingBytes <;>
    cases hh : HeadNormalization.Wire.decode headBytes <;>
    cases hs : HeadNormalization.Wire.decode typeBytes <;>
    simp only [validateBytes, hb, hm, ha, ht, hh, hs, Bool.false_eq_true] at h
  case some.some.some.some.some.some before middle after typing heads types =>
    exact ⟨before, middle, after, typing, heads, types, decodeSnapshot_exact hb,
      decodeSnapshot_exact hm, decodeSnapshot_exact ha, Typing.Wire.decode_exact ht,
      HeadNormalization.Wire.decode_exact hh, HeadNormalization.Wire.decode_exact hs,
      TypeIndexNormalization.validate_sound h⟩

theorem validateBytes_truth
    (h : validateBytes beforeBytes middleBytes afterBytes typingBytes headBytes typeBytes q = true) : q.Holds := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, truth⟩ := validateBytes_sound h
  exact truth

end Jihoo.GraphCertificates.TypeIndexNormalization.Wire
