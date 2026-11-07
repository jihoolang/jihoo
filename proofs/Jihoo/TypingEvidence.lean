import Jihoo.CoreBridgeBetaEvidence
import Jihoo.TypedBetaReplayCodec

/-! Semantic observations of certified closed weak-head-normal evidence.
The requested literal proposition is independent of the certificate. Its truth
is derived from typing and canonical forms, never supplied as an input proof or
checked by directly deciding the requested arithmetic relation. -/
namespace Jihoo.GraphCertificates.Typing.Evidence
open CoreBridge CoreBridge.Raw
open Typing.Wire

inductive Claim where
  | equal : Nat → Nat → Claim
  | less : Nat → Nat → Claim
  deriving DecidableEq, Repr

def Claim.asType : Claim → Raw
  | .equal m n => .eq (.natural m) (.natural n)
  | .less m n => .lt (.natural m) (.natural n)

def Claim.Holds : Claim → Prop
  | .equal m n => m = n
  | .less m n => m < n

/-- This tests the exact requested type and a function-spine normality flag,
not the truth of the requested arithmetic proposition. -/
def observe (s : Snapshot) (q : Claim) : Bool :=
  match decode s.graph s.termRoot, decode s.graph s.typeRoot with
  | some t, some A => Beta.headNormal t && decide (A = q.asType)
  | _, _ => false

def Realized (s : Snapshot) (q : Claim) : Prop :=
  ∃ t, decode s.graph s.termRoot = some t ∧
    decode s.graph s.typeRoot = some q.asType ∧
    Beta.HasType (fun _ => none) t q.asType ∧
    Beta.IsType (fun _ => none) q.asType ∧ Beta.headNormal t = true ∧ q.Holds

theorem observe_sound (hs : s.Sound) (ho : observe s q = true) : Realized s q := by
  obtain ⟨t, A, ht, hA, typed, formed⟩ := hs
  simp only [observe, ht, hA] at ho
  have hn := (Bool.and_eq_true_iff.mp ho).1
  have he : A = q.asType := of_decide_eq_true (Bool.and_eq_true_iff.mp ho).2
  subst A
  refine ⟨t, ht, hA, typed, formed, hn, ?_⟩
  cases q with
  | equal m n => exact typed.head_literal_eq hn
  | less m n => exact typed.head_literal_lt hn

def validate (s : Snapshot) (c : Typing.Certificate) (q : Claim) : Bool :=
  Typing.Wire.validateAgainst s c && observe s q

theorem validate_sound (h : validate s c q = true) : s.Matches c ∧ Realized s q := by
  have hv := Bool.and_eq_true_iff.mp h
  have hs := Typing.Wire.validateAgainst_sound hv.1
  exact ⟨hs.1, observe_sound hs.2 hv.2⟩

theorem validate_truth (h : validate s c q = true) : q.Holds := by
  obtain ⟨_, _, _, _, _, _, hq⟩ := (validate_sound h).2
  exact hq

theorem false_claim_rejected (hq : ¬ q.Holds) : validate s c q = false := by
  cases hv : validate s c q with
  | false => rfl
  | true => exact False.elim (hq (validate_truth hv))

def validateBytes (snapshotBytes typingBytes : ByteArray) (q : Claim) : Bool :=
  match decodeSnapshot snapshotBytes, Typing.Wire.decode typingBytes with
  | some s, some c => validate s c q
  | _, _ => false

theorem validateBytes_sound (h : validateBytes snapshotBytes typingBytes q = true) :
    ∃ s c, encodeSnapshot s = snapshotBytes ∧ Typing.Wire.encode c = typingBytes ∧
      s.Matches c ∧ Realized s q := by
  cases hs : decodeSnapshot snapshotBytes <;> cases hc : Typing.Wire.decode typingBytes <;>
    simp only [validateBytes, hs, hc, Bool.false_eq_true] at h
  case some.some s c =>
    exact ⟨s, c, decodeSnapshot_exact hs, Typing.Wire.decode_exact hc, validate_sound h⟩

theorem validateBytes_truth (h : validateBytes snapshotBytes typingBytes q = true) : q.Holds := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hq⟩ := validateBytes_sound h
  exact hq

/-- Replay supplies the output typing; no second output typing certificate or
normalization theorem is assumed. The reached output must pass observe. -/
theorem replay_realized (h : TypedBeta.validate before after typing path replay = true)
    (ho : observe after q = true) : Realized after q := by
  obtain ⟨_, _, t, u, A, _, _, hu, hA, _, _, _, typed, formed⟩ := TypedBeta.validate_sound h
  exact observe_sound ⟨u, A, hu, hA, typed, formed⟩ ho

end Jihoo.GraphCertificates.Typing.Evidence
