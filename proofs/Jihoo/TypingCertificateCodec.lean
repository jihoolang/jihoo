import Jihoo.TypingCertificates
import Jihoo.GraphCertificateCodec

/-! Canonical version-2 typing artifacts bind the entire graph, both selected
roots, both selected derivation steps, and every derivation field. The generic
codec is total; the CLI adds bounded scanning before invoking it. -/
namespace Jihoo.GraphCertificates.Typing.Wire
open Canonical

def encodeStep (s : Step) : Bytes :=
  encodeNat s.rule ++ encodeList encodeNat s.context ++
    encodeNat s.subject ++ encodeNat s.target ++ encodeList encodeNat s.premises

def parseStep : Parser Step := fun bs => do
  let (rule, bs) ← parseNat bs
  let (context, bs) ← parseList parseNat bs
  let (subject, bs) ← parseNat bs
  let (target, bs) ← parseNat bs
  let (premises, bs) ← parseList parseNat bs
  pure ({ rule, context, subject, target, premises }, bs)

theorem parseStep_encode (s : Step) (rest : Bytes) :
    parseStep (encodeStep s ++ rest) = some (s, rest) := by
  simp [parseStep, encodeStep, List.append_assoc, parseNat_encode,
    parseList_encode encodeNat parseNat parseNat_encode]

def encodeList (c : Certificate) : Bytes :=
  encodeNat 2 ++ encodeNat c.termRoot ++ encodeNat c.typeRoot ++
    encodeNat c.typingStep ++ encodeNat c.formationStep ++
    encodeGraph c.graph ++ Canonical.encodeList encodeStep c.steps

def parse : Parser Certificate := fun bs => do
  let (version, bs) ← parseNat bs
  if version ≠ 2 then none else do
    let (termRoot, bs) ← parseNat bs
    let (typeRoot, bs) ← parseNat bs
    let (typingStep, bs) ← parseNat bs
    let (formationStep, bs) ← parseNat bs
    let (graph, bs) ← parseGraph bs
    let (steps, bs) ← parseList parseStep bs
    pure ({ graph, termRoot, typeRoot, typingStep, formationStep, steps }, bs)

theorem parse_encode (c : Certificate) (rest : Bytes) :
    parse (encodeList c ++ rest) = some (c, rest) := by
  simp [parse, encodeList, List.append_assoc, parseNat_encode, parseGraph_encode,
    parseList_encode encodeStep parseStep parseStep_encode]

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

def validateBytes (bytes : ByteArray) : Bool :=
  match decode bytes with
  | none => false
  | some c => validate c

/-- Acceptance of bytes alone implies a closed typing and type-formation
derivation for the exact roots of the exact complete canonical artifact. -/
theorem validateBytes_sound {bytes : ByteArray} (h : validateBytes bytes = true) :
    ∃ c : Certificate, encode c = bytes ∧ Sound c := by
  cases hc : decode bytes with
  | none => simp [validateBytes, hc] at h
  | some c =>
      exact ⟨c, decode_exact hc, validate_sound (by simpa [validateBytes, hc] using h)⟩


/-- Version 3 is the independently retained actual-Core snapshot envelope.
Its provenance is an IO/exporter assumption; its exact canonical content is
bound here without trusting the certificate producer to copy it honestly. -/
structure Snapshot where
  termRoot : Nat
  typeRoot : Nat
  graph : Graph
  deriving DecidableEq, Repr

def encodeSnapshotList (s : Snapshot) : Bytes :=
  encodeNat 3 ++ encodeNat s.termRoot ++ encodeNat s.typeRoot ++ encodeGraph s.graph

def parseSnapshot : Parser Snapshot := fun bs => do
  let (version, bs) ← parseNat bs
  if version ≠ 3 then none else do
    let (termRoot, bs) ← parseNat bs
    let (typeRoot, bs) ← parseNat bs
    let (graph, bs) ← parseGraph bs
    pure ({ termRoot, typeRoot, graph }, bs)

theorem parseSnapshot_encode (s : Snapshot) (rest : Bytes) :
    parseSnapshot (encodeSnapshotList s ++ rest) = some (s, rest) := by
  simp [parseSnapshot, encodeSnapshotList, List.append_assoc, parseNat_encode,
    parseGraph_encode]

def encodeSnapshot (s : Snapshot) : ByteArray := (encodeSnapshotList s).toByteArray

def decodeSnapshot (bytes : ByteArray) : Option Snapshot := do
  let (s, []) ← parseSnapshot bytes.data.toList | none
  if encodeSnapshotList s = bytes.data.toList then some s else none

theorem decodeSnapshot_encode (s : Snapshot) :
    decodeSnapshot (encodeSnapshot s) = some s := by
  simp [decodeSnapshot, encodeSnapshot, show parseSnapshot (encodeSnapshotList s) = some (s, []) from
    by simpa using parseSnapshot_encode s []]

theorem encodeSnapshot_injective : Function.Injective encodeSnapshot := by
  intro a b h
  have := congrArg decodeSnapshot h
  simpa [decodeSnapshot_encode] using this

theorem decodeSnapshot_exact {bytes : ByteArray} {s : Snapshot}
    (h : decodeSnapshot bytes = some s) : encodeSnapshot s = bytes := by
  unfold decodeSnapshot at h
  cases hp : parseSnapshot bytes.data.toList with
  | none => simp [hp] at h
  | some result =>
      rcases result with ⟨s', rest⟩
      cases rest with
      | cons b rest => simp [hp] at h
      | nil =>
          simp only [hp, bind, Option.bind] at h
          split at h
          next he =>
            cases h
            apply ByteArray.ext
            apply Array.ext'
            simpa [encodeSnapshot, List.toList_data_toByteArray] using he
          next => contradiction

def Snapshot.Matches (s : Snapshot) (c : Certificate) : Prop :=
  c.graph = s.graph ∧ c.termRoot = s.termRoot ∧ c.typeRoot = s.typeRoot

instance (s : Snapshot) (c : Certificate) : Decidable (s.Matches c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def Snapshot.Sound (s : Snapshot) : Prop :=
  ∃ t A, GraphCertificates.decode s.graph s.termRoot = some t ∧
    GraphCertificates.decode s.graph s.typeRoot = some A ∧
    CoreBridge.Raw.Beta.HasType (fun _ => none) t A ∧
    CoreBridge.Raw.Beta.IsType (fun _ => none) A

def validateAgainst (s : Snapshot) (c : Certificate) : Bool :=
  decide (s.Matches c) && validate c

theorem validateAgainst_sound {s : Snapshot} {c : Certificate}
    (h : validateAgainst s c = true) : s.Matches c ∧ s.Sound := by
  have hs := Bool.and_eq_true_iff.mp h
  have hm : s.Matches c := of_decide_eq_true hs.1
  obtain ⟨t, A, ht, hA, typed, formed⟩ := validate_sound hs.2
  refine ⟨hm, t, A, ?_, ?_, typed, formed⟩
  · simpa only [hm.1, hm.2.1] using ht
  · simpa only [hm.1, hm.2.2] using hA

def validateAgainstBytes (snapshotBytes certificateBytes : ByteArray) : Bool :=
  match decodeSnapshot snapshotBytes, decode certificateBytes with
  | some s, some c => validateAgainst s c
  | _, _ => false

/-- End-to-end pure boundary: exact independent snapshot bytes, exact artifact
bytes, equality of the COMPLETE graphs and both selected root IDs, and closed
model typing/formation. It does not assume producer or compiler correctness. -/
theorem validateAgainstBytes_sound {snapshotBytes certificateBytes : ByteArray}
    (h : validateAgainstBytes snapshotBytes certificateBytes = true) :
    ∃ s c, encodeSnapshot s = snapshotBytes ∧ encode c = certificateBytes ∧
      s.Matches c ∧ s.Sound := by
  cases hs : decodeSnapshot snapshotBytes <;> cases hc : decode certificateBytes <;>
    simp only [validateAgainstBytes, hs, hc, Bool.false_eq_true] at h
  case some.some s c =>
    have hm := validateAgainst_sound h
    exact ⟨s, c, decodeSnapshot_exact hs, decode_exact hc, hm.1, hm.2⟩

end Jihoo.GraphCertificates.Typing.Wire
