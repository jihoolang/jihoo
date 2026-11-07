import Jihoo.CoreBridgeClosedNormalization
import Jihoo.TypingEvidence

/-! Consequences for the existing exact-snapshot typing checker. No new wire
format, admission rule, observation executable or normalizer is introduced. -/
namespace Jihoo.GraphCertificates.Typing.ClosedConsistency
open CoreBridge CoreBridge.Raw Typing.Wire
variable {q : Typing.Evidence.Claim}

theorem snapshot_normalizes {s : Snapshot} (h : s.Sound) :
    ∃ t A u, decode s.graph s.termRoot = some t ∧
      decode s.graph s.typeRoot = some A ∧ Beta.HasType (fun _ => none) u A ∧
      Beta.Steps t u ∧ Beta.headNormal u = true := by
  obtain ⟨t, A, ht, hA, typed, _⟩ := h
  obtain ⟨u, steps, hn⟩ := typed.closed_head_normalizes
  exact ⟨t, A, u, ht, hA, typed.preservation_steps steps, steps, hn⟩

theorem snapshot_literal_truth {s : Snapshot} (h : s.Sound)
    (hq : decode s.graph s.typeRoot = some q.asType) : q.Holds := by
  obtain ⟨t, A, _, hA, typed, _⟩ := h
  rw [hq] at hA
  cases hA
  cases q with
  | equal m n => exact typed.closed_literal_eq
  | less m n => exact typed.closed_literal_lt

theorem validate_normalizes (h : Typing.Wire.validateAgainst s c = true) :
    s.Matches c ∧ ∃ t A u, decode s.graph s.termRoot = some t ∧
      decode s.graph s.typeRoot = some A ∧ Beta.HasType (fun _ => none) u A ∧
      Beta.Steps t u ∧ Beta.headNormal u = true :=
  ⟨(Typing.Wire.validateAgainst_sound h).1, snapshot_normalizes (Typing.Wire.validateAgainst_sound h).2⟩

theorem validate_literal_truth (h : Typing.Wire.validateAgainst s c = true)
    (hq : decode s.graph s.typeRoot = some q.asType) : q.Holds :=
  snapshot_literal_truth (Typing.Wire.validateAgainst_sound h).2 hq

theorem false_literal_rejected (hq : decode s.graph s.typeRoot = some q.asType)
    (hf : ¬ q.Holds) : Typing.Wire.validateAgainst s c = false := by
  cases hv : Typing.Wire.validateAgainst s c with
  | false => rfl
  | true => exact False.elim (hf (validate_literal_truth hv hq))

/-- The existence theorem retains all exact canonical byte associations from
the original checker. It does not produce an output graph or a bounded trace. -/
theorem validateBytes_normalizes
    (h : Typing.Wire.validateAgainstBytes snapshotBytes certificateBytes = true) :
    ∃ s c t A u, encodeSnapshot s = snapshotBytes ∧ Typing.Wire.encode c = certificateBytes ∧
      s.Matches c ∧ decode s.graph s.termRoot = some t ∧
      decode s.graph s.typeRoot = some A ∧ Beta.HasType (fun _ => none) u A ∧
      Beta.Steps t u ∧ Beta.headNormal u = true := by
  obtain ⟨s, c, hs, hc, hm, sound⟩ := Typing.Wire.validateAgainstBytes_sound h
  obtain ⟨t, A, u, ht, hA, typed, steps, hn⟩ := snapshot_normalizes sound
  exact ⟨s, c, t, A, u, hs, hc, hm, ht, hA, typed, steps, hn⟩

end Jihoo.GraphCertificates.Typing.ClosedConsistency
