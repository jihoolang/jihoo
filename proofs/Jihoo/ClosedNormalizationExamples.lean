import Jihoo.TypingClosedConsistency
import Jihoo.HeadNormalizationCodec

namespace Jihoo.CoreBridge.Raw.Beta.ClosedNormalizationExamples

private def identity : Raw := .lam false .u64 (.var 0)
private theorem identity_typed : HasType (fun _ => none) identity (.pi false .u64 .u64) :=
  .lam .u64 rfl (.var (by simp [Context.extend, rename]))

private def iterated : Nat → Raw
  | 0 => .natural 7
  | n + 1 => .app identity (iterated n)

private theorem iterated_typed (n : Nat) : HasType (fun _ => none) (iterated n) .u64 := by
  induction n with
  | zero => exact .natural (by decide)
  | succ n ih => simpa [iterated, subst] using HasType.app identity_typed ih

theorem arbitrarily_deep_head_normalizes (n : Nat) :
    ∃ u, Steps (iterated n) u ∧ headNormal u = true :=
  (iterated_typed n).closed_head_normalizes

/-- The mathematical theorem does not inherit the producer's 64-step fuel cap. -/
theorem over_producer_fuel_normalizes :
    ∃ u, Steps (iterated 65) u ∧ headNormal u = true := arbitrarily_deep_head_normalizes 65

theorem arbitrary_closed_false_equality :
    ¬ HasType (fun _ => none) t (.eq (.natural 0) (.natural 1)) :=
  no_closed_false_equality (by decide)

theorem arbitrary_closed_false_bound :
    ¬ HasType (fun _ => none) t (.lt (.natural n) (.natural n)) :=
  no_closed_false_bound (Nat.lt_irrefl n)

private def higher : Raw :=
  .app (.lam false (.pi false .u64 .u64) (.app (.var 0) (.natural 7))) identity

private theorem higher_typed : HasType (fun _ => none) higher .u64 := by
  have hf : HasType (fun _ => none)
      (.lam false (.pi false .u64 .u64) (.app (.var 0) (.natural 7)))
      (.pi false (.pi false .u64 .u64) .u64) := by
    apply HasType.lam (.pi .u64 rfl .u64) rfl
    have hv : HasType (Context.extend (fun _ => none) (.pi false .u64 .u64)) (.var 0)
        (.pi false .u64 .u64) := .var (by simp [Context.extend, rename])
    simpa [subst, proposition] using HasType.app hv (HasType.natural (n := 7) (by decide))
  simpa [higher, subst] using HasType.app hf identity_typed

theorem higher_order_normalizes : ∃ u, Steps higher u ∧ headNormal u = true :=
  higher_typed.closed_head_normalizes

/-- The theorem stops beneath a lambda even when contextual beta is possible. -/
theorem head_normal_still_reduces :
    headNormal (.lam false .u64 (.app identity (.var 0))) = true ∧
      Step (.lam false .u64 (.app identity (.var 0))) (.lam false .u64 (.var 0)) := by
  constructor
  · rfl
  · simpa [identity, subst, single] using (Step.lamBody (Step.beta false .u64 (.var 0) (.var 0)))

theorem arithmetic_is_not_evaluated : headNormal (.uadd (.natural 3) (.natural 4)) = true := rfl

end Jihoo.CoreBridge.Raw.Beta.ClosedNormalizationExamples

namespace Jihoo.GraphCertificates.Typing.ClosedConsistency.Examples
open Typing.Wire

/-- A beta-reducible evidence term, with no supplied normalization trace. -/
private def certificate : Typing.Certificate := {
  graph := #[.u64, .var 0, .refl 1, .eq 1 1, .lam false 0 2,
    .pi false 0 3, .natural 7, .app 4 6, .eq 6 6]
  termRoot := 7, typeRoot := 8, typingStep := 5, formationStep := 6
  steps := [⟨0, [], 0, 0, []⟩, ⟨10, [0], 1, 0, []⟩,
    ⟨17, [0], 2, 3, [1]⟩, ⟨19, [], 4, 5, [0, 2]⟩,
    ⟨11, [], 6, 0, []⟩, ⟨20, [], 7, 8, [3, 4]⟩,
    ⟨4, [], 8, 8, [4, 4]⟩] }
private def snapshot : Snapshot := ⟨7, 8, certificate.graph⟩

theorem nonnormal_certificate_truth
    (h : Typing.Wire.validateAgainst snapshot certificate = true) : (7 : Nat) = 7 :=
  validate_literal_truth (q := .equal 7 7) h (by decide +kernel)

#eval show IO Unit from do
  unless Typing.Wire.validateAgainst snapshot certificate do
    throw (IO.userError "nonnormal typing certificate rejected")
  if Typing.Evidence.observe snapshot (.equal 7 7) then
    throw (IO.userError "regression must not be head normal")
  unless Typing.Wire.validateAgainstBytes (encodeSnapshot snapshot) (Typing.Wire.encode certificate) do
    throw (IO.userError "nonnormal certificate byte roundtrip rejected")
  if HeadNormalization.validate snapshot snapshot certificate [] then
    throw (IO.userError "existence must not bypass finite-trace final-normality checks")

end Jihoo.GraphCertificates.Typing.ClosedConsistency.Examples
