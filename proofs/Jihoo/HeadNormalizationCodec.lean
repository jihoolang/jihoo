import Jihoo.HeadNormalization

namespace Jihoo.GraphCertificates.HeadNormalization.Wire
open Canonical Typing.Wire

/-- Schema 5: a finite list of full schema-4 replay records. Empty is allowed
only when the independently bound input is already head normal. -/
def encodeList (cs : Certificate) : Bytes :=
  encodeNat 5 ++ Canonical.encodeList TypedBeta.Wire.encodeList cs

def parse : Parser Certificate := fun bs => do
  let (version, bs) ← parseNat bs
  if version ≠ 5 then none else parseList TypedBeta.Wire.parse bs

theorem parse_encode (cs : Certificate) (rest : Bytes) :
    parse (encodeList cs ++ rest) = some (cs, rest) := by
  simp [parse, encodeList, List.append_assoc, parseNat_encode,
    parseList_encode TypedBeta.Wire.encodeList TypedBeta.Wire.parse TypedBeta.Wire.parse_encode]

def encode (cs : Certificate) : ByteArray := (encodeList cs).toByteArray

def decode (bytes : ByteArray) : Option Certificate := do
  let (cs, []) ← parse bytes.data.toList | none
  if encodeList cs = bytes.data.toList then some cs else none

theorem decode_encode (cs : Certificate) : decode (encode cs) = some cs := by
  simp [decode, encode, show parse (encodeList cs) = some (cs, []) from
    by simpa using parse_encode cs []]

theorem encode_injective : Function.Injective encode := by
  intro a b h
  have := congrArg decode h
  simpa [decode_encode] using this

theorem decode_exact {bytes : ByteArray} {c : Certificate}
    (h : decode bytes = some c) : encode c = bytes := by
  unfold decode at h
  cases hp : parse bytes.data.toList with
  | none => simp [hp] at h
  | some result =>
      rcases result with ⟨c', rest⟩
      cases rest with
      | cons b rest => simp [hp] at h
      | nil =>
          simp only [hp, bind, Option.bind] at h
          split at h
          next he =>
            cases h
            apply ByteArray.ext
            apply Array.ext'
            simpa [encode, List.toList_data_toByteArray] using he
          next => contradiction

def validateBytes (beforeBytes afterBytes typingBytes chainBytes : ByteArray) : Bool :=
  match decodeSnapshot beforeBytes, decodeSnapshot afterBytes,
      Typing.Wire.decode typingBytes, decode chainBytes with
  | some before, some after, some typing, some cs =>
      HeadNormalization.validate before after typing cs
  | _, _, _, _ => false

theorem validateBytes_sound (h : validateBytes beforeBytes afterBytes typingBytes chainBytes = true) :
    ∃ before after typing cs,
      encodeSnapshot before = beforeBytes ∧ encodeSnapshot after = afterBytes ∧
      Typing.Wire.encode typing = typingBytes ∧ encode cs = chainBytes ∧
      before.Matches typing ∧ Sound before after cs := by
  cases hb : decodeSnapshot beforeBytes <;> cases ha : decodeSnapshot afterBytes <;>
    cases ht : Typing.Wire.decode typingBytes <;> cases hc : decode chainBytes <;>
    simp only [validateBytes, hb, ha, ht, hc, Bool.false_eq_true] at h
  case some.some.some.some before after typing cs =>
    exact ⟨before, after, typing, cs, decodeSnapshot_exact hb, decodeSnapshot_exact ha,
      Typing.Wire.decode_exact ht, decode_exact hc, HeadNormalization.validate_sound h⟩

def validatePrefixBytes (beforeBytes afterBytes typingBytes chainBytes : ByteArray) : Bool :=
  match decodeSnapshot beforeBytes, decodeSnapshot afterBytes,
      Typing.Wire.decode typingBytes, decode chainBytes with
  | some before, some after, some typing, some cs =>
      HeadNormalization.validatePrefix before after typing cs
  | _, _, _, _ => false

theorem validatePrefixBytes_sound (h : validatePrefixBytes beforeBytes afterBytes typingBytes chainBytes = true) :
    ∃ before after typing cs,
      encodeSnapshot before = beforeBytes ∧ encodeSnapshot after = afterBytes ∧
      Typing.Wire.encode typing = typingBytes ∧ encode cs = chainBytes ∧
      before.Matches typing ∧ PrefixSound before after cs := by
  cases hb : decodeSnapshot beforeBytes <;> cases ha : decodeSnapshot afterBytes <;>
    cases ht : Typing.Wire.decode typingBytes <;> cases hc : decode chainBytes <;>
    simp only [validatePrefixBytes, hb, ha, ht, hc, Bool.false_eq_true] at h
  case some.some.some.some before after typing cs =>
    exact ⟨before, after, typing, cs, decodeSnapshot_exact hb, decodeSnapshot_exact ha,
      Typing.Wire.decode_exact ht, decode_exact hc, HeadNormalization.validatePrefix_sound h⟩

def validateLiteralBytes (beforeBytes afterBytes typingBytes chainBytes : ByteArray)
    (q : Typing.Evidence.Claim) : Bool :=
  match decodeSnapshot beforeBytes, decodeSnapshot afterBytes,
      Typing.Wire.decode typingBytes, decode chainBytes with
  | some before, some after, some typing, some cs =>
      HeadNormalization.validateLiteral before after typing cs q
  | _, _, _, _ => false

theorem validateLiteralBytes_sound
    (h : validateLiteralBytes beforeBytes afterBytes typingBytes chainBytes q = true) :
    ∃ before after typing cs,
      encodeSnapshot before = beforeBytes ∧ encodeSnapshot after = afterBytes ∧
      Typing.Wire.encode typing = typingBytes ∧ encode cs = chainBytes ∧
      before.Matches typing ∧ Sound before after cs ∧ Typing.Evidence.Realized after q := by
  cases hb : decodeSnapshot beforeBytes <;> cases ha : decodeSnapshot afterBytes <;>
    cases ht : Typing.Wire.decode typingBytes <;> cases hc : decode chainBytes <;>
    simp only [validateLiteralBytes, hb, ha, ht, hc, Bool.false_eq_true] at h
  case some.some.some.some before after typing cs =>
    exact ⟨before, after, typing, cs, decodeSnapshot_exact hb, decodeSnapshot_exact ha,
      Typing.Wire.decode_exact ht, decode_exact hc, HeadNormalization.validateLiteral_sound h⟩

theorem validateLiteralBytes_truth
    (h : validateLiteralBytes beforeBytes afterBytes typingBytes chainBytes q = true) : q.Holds := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hq⟩ := validateLiteralBytes_sound h
  exact hq

end Jihoo.GraphCertificates.HeadNormalization.Wire
