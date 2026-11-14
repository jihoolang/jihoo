import Jihoo.NativeWire
import Jihoo.NativeCheckerSoundness
import Jihoo.NativeModeSafety

/-! Exact-byte admission through the universe- and mode-aware native syntax
checker. Source inference and exporter fidelity are not premises of these
pure soundness theorems; they remain a separate refinement obligation. -/
namespace Jihoo.NativeKernel.NativeAdmission

open NativeWire NativeArena

/-- Both selected roots retain their exact graph meaning. The requested type
is independently checked in ghost position and has an inferred sort. -/
def Sound (s : Snapshot) : Prop :=
  ∃ t ty : Term, ∃ sort : SortTag,
    decode 128 s.arena s.termRoot = some t ∧
    decode 128 s.arena s.typeRoot = some ty ∧
    HasType [] s.ghost t ty ∧ HasType [] true ty sort.term

def checkSnapshot (fuel : Nat) (s : Snapshot) : Bool :=
  graphValid s.arena &&
    match decode 128 s.arena s.termRoot, decode 128 s.arena s.typeRoot with
    | some t, some ty => Checker.isType fuel [] ty && Checker.check fuel [] s.ghost t ty
    | _, _ => false

theorem checkSnapshot_sound {fuel : Nat} {s : Snapshot}
    (h : checkSnapshot fuel s = true) : Sound s := by
  have hc := (Bool.and_eq_true_iff.mp h).2
  cases ht : decode 128 s.arena s.termRoot <;>
    cases hty : decode 128 s.arena s.typeRoot <;>
    simp only [ht, hty, Bool.false_eq_true] at hc
  case some.some t ty =>
    have parts := Bool.and_eq_true_iff.mp hc
    obtain ⟨sort, formed⟩ := Checker.isType_sound parts.1
    exact ⟨t, ty, sort, ht, hty, Checker.check_sound parts.2, formed⟩

theorem checkSnapshot_graphValid {fuel : Nat} {s : Snapshot}
    (h : checkSnapshot fuel s = true) : graphValid s.arena = true :=
  (Bool.and_eq_true_iff.mp h).1

theorem checkSnapshot_backward {fuel : Nat} {s : Snapshot}
    (h : checkSnapshot fuel s = true) : Backward s.arena :=
  graphValid_backward (checkSnapshot_graphValid h)

def checkBytes (fuel : Nat) (bytes : ByteArray) : Bool :=
  match decodeSnapshot bytes with
  | some s => checkSnapshot fuel s
  | none => false

theorem checkBytes_sound {fuel : Nat} {bytes : ByteArray}
    (h : checkBytes fuel bytes = true) :
    ∃ s : Snapshot, encodeSnapshot s = bytes ∧ graphValid s.arena = true ∧ Sound s := by
  cases hs : decodeSnapshot bytes with
  | none => simp [checkBytes, hs] at h
  | some s =>
      have accepted : checkSnapshot fuel s = true := by simpa only [checkBytes, hs] using h
      exact ⟨s, decodeSnapshot_exact hs, checkSnapshot_graphValid accepted,
        checkSnapshot_sound accepted⟩

theorem checkBytes_encode (fuel : Nat) (s : Snapshot) :
    checkBytes fuel (encodeSnapshot s) = checkSnapshot fuel s := by
  simp only [checkBytes, decodeSnapshot_encode]

theorem checkBytes_represents {fuel : Nat} {bytes : ByteArray}
    (h : checkBytes fuel bytes = true) :
    ∃ s : Snapshot, ∃ t ty : Term, ∃ sort : SortTag,
      encodeSnapshot s = bytes ∧ graphValid s.arena = true ∧
      Represents s.arena s.termRoot t ∧ Represents s.arena s.typeRoot ty ∧
      t.WellFormed ∧ ty.WellFormed ∧
      HasType [] s.ghost t ty ∧ HasType [] true ty sort.term := by
  obtain ⟨s, exactBytes, valid, t, ty, sort, ht, hty, typed, formed⟩ := checkBytes_sound h
  exact ⟨s, t, ty, sort, exactBytes, valid, decode_sound ht, decode_sound hty,
    decode_wellFormed ht, decode_wellFormed hty, typed, formed⟩

/-- Both admitted roots are genuinely closed under the full binding layout,
including evidence-binding branches, rather than merely graph-reachable. -/
theorem checkBytes_closed {fuel : Nat} {bytes : ByteArray}
    (h : checkBytes fuel bytes = true) :
    ∃ s : Snapshot, ∃ t ty : Term, ∃ sort : SortTag,
      encodeSnapshot s = bytes ∧ Backward s.arena ∧
      Represents s.arena s.termRoot t ∧ Represents s.arena s.typeRoot ty ∧
      t.Scoped 0 ∧ ty.Scoped 0 ∧
      HasType [] s.ghost t ty ∧ HasType [] true ty sort.term := by
  obtain ⟨s, exactBytes, valid, t, ty, sort, ht, hty, typed, formed⟩ := checkBytes_sound h
  exact ⟨s, t, ty, sort, exactBytes, graphValid_backward valid,
    decode_sound ht, decode_sound hty, typed.term_scoped, formed.term_scoped, typed, formed⟩

end Jihoo.NativeKernel.NativeAdmission
