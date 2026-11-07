import Jihoo.GraphCertificateReplay

/-! Kernel-checked nonvacuity and identity-boundary examples. Runtime importer
and malformed-input coverage additionally live in the integration suite. -/
namespace Jihoo.GraphCertificates
open Canonical CoreBridge

private def first : Certificate :=
  ⟨#[.var 0], #[.var 0, .var 1], 0, 1, .shift 1⟩

private def second : Certificate :=
  ⟨#[.var 0, .var 1], #[.var 0, .var 1, .var 3], 1, 2, .shift 2⟩

private theorem first_valid : validate first = true := by
  have hi : decode first.before first.input = some (.var 0) := rfl
  have ho : decode first.after first.output = some (.var 1) := rfl
  have hp : appendOnly first = true := by decide
  simp only [validate, hp, hi, ho, ↓reduceIte]
  simp [expected, first, Raw.rename, rawEqual, signedBound]

private theorem second_valid : validate second = true := by
  have hi : decode second.before second.input = some (.var 1) := rfl
  have ho : decode second.after second.output = some (.var 3) := rfl
  have hp : appendOnly second = true := by decide
  simp only [validate, hp, hi, ho, ↓reduceIte]
  simp [expected, second, Raw.rename, rawEqual, signedBound]

theorem encodedReplay_accepted :
    validateReplay (encodeCertificate first) (encodeCertificate second) (.shift 2) = true := by
  simp only [validateReplay, decodeCertificate_encode, validateRequested, validateChain,
    first_valid, second_valid, checkFollowing]
  simp [linked, first, second]

theorem requestedOperationMismatch_rejected :
    validateReplay (encodeCertificate first) (encodeCertificate second) (.shift 3) = false := by
  simp [validateReplay, decodeCertificate_encode, validateRequested, second]

/-- Even if two roots could denote equal terms, the selected root must match. -/
theorem differentSelectedRoot_rejected :
    validateChain first [{ second with input := 0 }] = false := by
  simp [validateChain, checkFollowing, linked, first, second]

/-- Changing an otherwise unreachable node breaks full-graph identity. -/
theorem differentPreviousGraph_rejected :
    validateChain first [{ second with before := #[.var 99, .var 1] }] = false := by
  simp [validateChain, checkFollowing, linked, first, second]

theorem trailingByte_rejected :
    decodeCertificate ((encodeCertificateList first ++ [59]).toByteArray) = none := by
  simp [decodeCertificate, parseCertificate_encode]

/-- The natural subparser is permissive, so whole-artifact equality is checked. -/
theorem nonminimalNumeral_isNotCanonical :
    parseNat [48, 59] = some (0, []) ∧ encodeNat 0 ≠ [48, 59] := by
  constructor
  · rfl
  · simp [encodeNat]

theorem negativeZero_rejected : parseInt [49, 59, 59] = none := by rfl

theorem signedInteger_roundtrip :
    parseNode (encodeNode (.integer (-9223372036854775808)) ++ [255]) =
      some (.integer (-9223372036854775808), [255]) := parseNode_encode _ _

/-- Replay composition specializes to the expected cumulative shift. -/
theorem twoShifts_compose :
    ∃ input output, Represents first.before first.input input ∧
      Represents second.after second.output output ∧
      output = (input.rename (fun k => k + 1)).rename (fun k => k + 2) := by
  have h := validateRequested_sound (previous := first) (next := second)
    (requested := .shift 2)
    (by simpa [validateReplay, decodeCertificate_encode] using encodedReplay_accepted)
  obtain ⟨_, _, _, input, middle, output, hi, _, _, ho, hfirst, hsecond⟩ := h
  refine ⟨input, output, hi, ho, ?_⟩
  change middle = input.rename (fun k => k + 1) at hfirst
  change output = middle.rename (fun k => k + 2) at hsecond
  rw [hsecond, hfirst]

end Jihoo.GraphCertificates
