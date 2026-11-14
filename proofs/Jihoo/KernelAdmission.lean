import Jihoo.KernelCheckerSoundness
import Jihoo.TypingCertificateCodec
import Jihoo.CoreBridgeClosedNormalization

/-! Certificate-free admission of exact canonical Core snapshots. The only
inputs are the fuel budget and serialized graph, term root and type root.
Soundness binds typing and formation to these exact bytes; native inference,
export provenance and IO are outside this pure theorem. -/
namespace Jihoo.KernelAdmission

open CoreBridge CoreBridge.Raw GraphCertificates
open GraphCertificates.Typing.Wire

/-- Decode the selected roots of the existing bounded graph format, then run
the executable kernel. No typing derivation or reduction trace is supplied. -/
def checkSnapshot (fuel : Nat) (s : Snapshot) : Bool :=
  match GraphCertificates.decode s.graph s.termRoot,
      GraphCertificates.decode s.graph s.typeRoot with
  | some t, some A => KernelChecker.check fuel [] t A
  | _, _ => false

theorem checkSnapshot_sound {fuel : Nat} {s : Snapshot}
    (h : checkSnapshot fuel s = true) : s.Sound := by
  cases ht : GraphCertificates.decode s.graph s.termRoot <;>
    cases hA : GraphCertificates.decode s.graph s.typeRoot <;>
    simp only [checkSnapshot, ht, hA, Bool.false_eq_true] at h
  case some.some t A =>
    exact ⟨t, A, ht, hA, KernelChecker.check_sound h,
      KernelChecker.check_isType h⟩

/-- Canonical decoding consumes the entire envelope; checking its selected
roots also validates unused graph nodes. Trailing bytes and alternate encodings
are rejected. -/
def checkBytes (fuel : Nat) (bytes : ByteArray) : Bool :=
  match decodeSnapshot bytes with
  | some s => checkSnapshot fuel s
  | none => false

theorem checkBytes_sound {fuel : Nat} {bytes : ByteArray}
    (h : checkBytes fuel bytes = true) :
    ∃ s : Snapshot, encodeSnapshot s = bytes ∧ s.Sound := by
  cases hs : decodeSnapshot bytes with
  | none => simp [checkBytes, hs] at h
  | some s =>
      exact ⟨s, decodeSnapshot_exact hs,
        checkSnapshot_sound (by simpa only [checkBytes, hs] using h)⟩

theorem checkBytes_encode (fuel : Nat) (s : Snapshot) :
    checkBytes fuel (encodeSnapshot s) = checkSnapshot fuel s := by
  simp only [checkBytes, decodeSnapshot_encode]

/-- Accepted bytes determine exact graph representations and closed model
derivations, without trusting an external producer of typing certificates. -/
theorem checkBytes_represents {fuel : Nat} {bytes : ByteArray}
    (h : checkBytes fuel bytes = true) :
    ∃ s : Snapshot, ∃ t A : Raw, encodeSnapshot s = bytes ∧
      Represents s.graph s.termRoot t ∧ Represents s.graph s.typeRoot A ∧
      Beta.HasType (fun _ => none) t A ∧ Beta.IsType (fun _ => none) A := by
  obtain ⟨s, exactBytes, t, A, ht, hA, typed, formed⟩ := checkBytes_sound h
  exact ⟨s, t, A, exactBytes, decode_sound ht, decode_sound hA, typed, formed⟩

/-- Every accepted closed term has a beta head-normal endpoint at its
original type. This does not assert completion within the supplied fuel. -/
theorem checkBytes_normalizes {fuel : Nat} {bytes : ByteArray}
    (h : checkBytes fuel bytes = true) :
    ∃ s : Snapshot, ∃ t A u : Raw, encodeSnapshot s = bytes ∧
      GraphCertificates.decode s.graph s.termRoot = some t ∧
      GraphCertificates.decode s.graph s.typeRoot = some A ∧
      Beta.HasType (fun _ => none) t A ∧ Beta.IsType (fun _ => none) A ∧
      Beta.Steps t u ∧ Beta.HasType (fun _ => none) u A ∧
      Beta.headNormal u = true := by
  obtain ⟨s, exactBytes, t, A, ht, hA, typed, formed⟩ := checkBytes_sound h
  obtain ⟨u, steps, normal⟩ := typed.closed_head_normalizes
  exact ⟨s, t, A, u, exactBytes, ht, hA, typed, formed, steps,
    typed.preservation_steps steps, normal⟩

/-- Any finite contextual beta reduction of an admitted term retains its
exact declared type, including reductions inside annotations. -/
theorem checkSnapshot_preservation {fuel : Nat} {s : Snapshot} {t u A : Raw}
    (h : checkSnapshot fuel s = true)
    (ht : GraphCertificates.decode s.graph s.termRoot = some t)
    (hA : GraphCertificates.decode s.graph s.typeRoot = some A)
    (steps : Beta.Steps t u) : Beta.HasType (fun _ => none) u A := by
  obtain ⟨t', A', ht', hA', typed, _⟩ := checkSnapshot_sound h
  rw [ht] at ht'; cases ht'
  rw [hA] at hA'; cases hA'
  exact typed.preservation_steps steps

/-- The truth of the requested equality follows from admitted evidence; the
admission function never directly decides this requested proposition. -/
theorem checkSnapshot_literal_eq {fuel : Nat} {s : Snapshot} {m n : Nat}
    (h : checkSnapshot fuel s = true)
    (hq : GraphCertificates.decode s.graph s.typeRoot =
      some (.eq (.natural m) (.natural n))) : m = n := by
  obtain ⟨_, A, _, hA, typed, _⟩ := checkSnapshot_sound h
  rw [hq] at hA; cases hA
  exact typed.closed_literal_eq

theorem checkSnapshot_literal_lt {fuel : Nat} {s : Snapshot} {m n : Nat}
    (h : checkSnapshot fuel s = true)
    (hq : GraphCertificates.decode s.graph s.typeRoot =
      some (.lt (.natural m) (.natural n))) : m < n := by
  obtain ⟨_, A, _, hA, typed, _⟩ := checkSnapshot_sound h
  rw [hq] at hA; cases hA
  exact typed.closed_literal_lt

theorem false_equality_rejected {fuel : Nat} {s : Snapshot} {m n : Nat}
    (hq : GraphCertificates.decode s.graph s.typeRoot =
      some (.eq (.natural m) (.natural n))) (hne : m ≠ n) :
    checkSnapshot fuel s = false := by
  cases h : checkSnapshot fuel s with
  | false => rfl
  | true => exact False.elim (hne (checkSnapshot_literal_eq h hq))

theorem false_bound_rejected {fuel : Nat} {s : Snapshot} {m n : Nat}
    (hq : GraphCertificates.decode s.graph s.typeRoot =
      some (.lt (.natural m) (.natural n))) (hne : ¬ m < n) :
    checkSnapshot fuel s = false := by
  cases h : checkSnapshot fuel s with
  | false => rfl
  | true => exact False.elim (hne (checkSnapshot_literal_lt h hq))

end Jihoo.KernelAdmission
