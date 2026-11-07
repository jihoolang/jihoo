import Jihoo.TypedBetaReplay

namespace Jihoo.GraphCertificates.TypedBeta.Wire
open Canonical Typing.Wire

/-- Version 4 binds the complete before/after snapshots and requested path. -/
def encodeList (c : Certificate) : Bytes :=
  encodeNat 4 ++ encodeSnapshotList c.before ++ encodeSnapshotList c.after ++
    Canonical.encodeList encodeNat c.path

def parse : Parser Certificate := fun bs => do
  let (version, bs) ← parseNat bs
  if version ≠ 4 then none else do
    let (before, bs) ← parseSnapshot bs
    let (after, bs) ← parseSnapshot bs
    let (path, bs) ← parseList parseNat bs
    pure ({ before, after, path }, bs)

theorem parse_encode (c : Certificate) (rest : Bytes) :
    parse (encodeList c ++ rest) = some (c, rest) := by
  simp [parse, encodeList, List.append_assoc, parseNat_encode,
    parseSnapshot_encode, parseList_encode encodeNat parseNat parseNat_encode]

def encode (c : Certificate) : ByteArray := (encodeList c).toByteArray

def decode (bytes : ByteArray) : Option Certificate := do
  let (c, []) ← parse bytes.data.toList | none
  if encodeList c = bytes.data.toList then some c else none

theorem decode_encode (c : Certificate) : decode (encode c) = some c := by
  simp [decode, encode, show parse (encodeList c) = some (c, []) from
    by simpa using parse_encode c []]

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

def validateBytes (beforeBytes afterBytes typingBytes replayBytes : ByteArray)
    (requested : List Nat) : Bool :=
  match decodeSnapshot beforeBytes, decodeSnapshot afterBytes,
      Typing.Wire.decode typingBytes, decode replayBytes with
  | some before, some after, some typing, some replay =>
      TypedBeta.validate before after typing requested replay
  | _, _, _, _ => false

/-- Pure end-to-end boundary: four canonical retained artifacts, both exact
snapshots, an independently supplied path, and derived fixed-type output typing. -/
theorem validateBytes_sound {beforeBytes afterBytes typingBytes replayBytes : ByteArray}
    {requested : List Nat}
    (h : validateBytes beforeBytes afterBytes typingBytes replayBytes requested = true) :
    ∃ before after typing replay,
      encodeSnapshot before = beforeBytes ∧ encodeSnapshot after = afterBytes ∧
      Typing.Wire.encode typing = typingBytes ∧ encode replay = replayBytes ∧
      Matches before after requested replay ∧ Sound before after requested := by
  cases hb : decodeSnapshot beforeBytes <;> cases ha : decodeSnapshot afterBytes <;>
    cases ht : Typing.Wire.decode typingBytes <;> cases hr : decode replayBytes <;>
    simp only [validateBytes, hb, ha, ht, hr, Bool.false_eq_true] at h
  case some.some.some.some before after typing replay =>
    exact ⟨before, after, typing, replay, decodeSnapshot_exact hb,
      decodeSnapshot_exact ha, Typing.Wire.decode_exact ht, decode_exact hr,
      TypedBeta.validate_sound h⟩

end Jihoo.GraphCertificates.TypedBeta.Wire
