import Jihoo.LinearEvidence
import Jihoo.CheckedLinearNormalization

/-! A separate per-artifact checker for closed first-order evidence, including
natural quantifiers and symbolic-sum conversion. Source/checker provenance is
not asserted by the theorem; all claims are about the exact retained graph. -/
namespace Jihoo.GraphCertificates.LinearEvidenceCheck
open CoreBridge LinearNaturals LinearEvidence Typing.Wire

def Sound (s : Snapshot) : Prop :=
  ∃ t A, ∃ p : Formula 0, decode s.graph s.termRoot = some t ∧
    decode s.graph s.typeRoot = some A ∧ p.encode = A ∧ Derives t p ∧ ∀ ρ, p.Holds ρ

def check (s : Snapshot) (termRoot typeRoot : Nat) :
    Option (PLift (s.termRoot = termRoot ∧ s.typeRoot = typeRoot ∧ Sound s)) := do
  if ht : s.termRoot = termRoot then do
    if ha : s.typeRoot = typeRoot then do
      if !LinearNormal.bounded s then none else do
        match hi : decode s.graph s.termRoot, hz : decode s.graph s.typeRoot with
        | some t, some A => do
            let result ← LinearEvidence.check 0 t A
            pure ⟨ht, ha, t, A, result.val, hi, hz, result.property.1,
              result.property.2, result.property.2.sound⟩
        | _, _ => none
    else none
  else none

def validate (s : Snapshot) (termRoot typeRoot : Nat) : Bool := (check s termRoot typeRoot).isSome

theorem validate_sound (h : validate s termRoot typeRoot = true) :
    s.termRoot = termRoot ∧ s.typeRoot = typeRoot ∧ Sound s := by
  unfold validate at h
  cases hc : check s termRoot typeRoot with
  | none => simp [hc] at h
  | some p => exact p.down

def validateBytes (bytes : ByteArray) (termRoot typeRoot : Nat) : Bool :=
  match decodeSnapshot bytes with
  | some s => validate s termRoot typeRoot
  | none => false

theorem validateBytes_sound (h : validateBytes bytes termRoot typeRoot = true) :
    ∃ s, encodeSnapshot s = bytes ∧ s.termRoot = termRoot ∧ s.typeRoot = typeRoot ∧ Sound s := by
  cases hs : decodeSnapshot bytes with
  | none => simp [validateBytes, hs] at h
  | some s => exact ⟨s, decodeSnapshot_exact hs, validate_sound (by simpa [validateBytes, hs] using h)⟩

theorem literal_value (e : Expr n) (h : e.encode = .natural v) (ρ : Nat → Nat) : e.eval ρ = v := by
  have he := e.evaluates ρ
  rw [h] at he
  exact he.deterministic .lit

theorem Formula.literal_equal_truth (p : Formula n) (h : p.encode = .eq (.natural a) (.natural b))
    (hp : p.Holds ρ) : a = b := by
  cases p with
  | equal x y =>
      simp only [Formula.encode, Raw.eq.injEq] at h
      simpa only [Formula.Holds, literal_value x h.1 ρ, literal_value y h.2 ρ] using hp
  | less => contradiction
  | all => contradiction

theorem Formula.literal_less_truth (p : Formula n) (h : p.encode = .lt (.natural a) (.natural b))
    (hp : p.Holds ρ) : a < b := by
  cases p with
  | less x y =>
      simp only [Formula.encode, Raw.lt.injEq] at h
      simpa only [Formula.Holds, literal_value x h.1 ρ, literal_value y h.2 ρ] using hp
  | equal => contradiction
  | all => contradiction

theorem false_equal_rejected (ht : decode s.graph s.typeRoot = some (.eq (.natural a) (.natural b)))
    (hf : a ≠ b) : validate s termRoot typeRoot = false := by
  cases hv : validate s termRoot typeRoot with
  | false => rfl
  | true =>
      obtain ⟨_, _, _, A, p, _, hA, he, _, hp⟩ := validate_sound hv
      rw [ht] at hA
      cases hA
      exact False.elim (hf (Formula.literal_equal_truth p he (hp (fun _ => 0))))

theorem false_less_rejected (ht : decode s.graph s.typeRoot = some (.lt (.natural a) (.natural b)))
    (hf : ¬a < b) : validate s termRoot typeRoot = false := by
  cases hv : validate s termRoot typeRoot with
  | false => rfl
  | true =>
      obtain ⟨_, _, _, A, p, _, hA, he, _, hp⟩ := validate_sound hv
      rw [ht] at hA
      cases hA
      exact False.elim (hf (Formula.literal_less_truth p he (hp (fun _ => 0))))

end Jihoo.GraphCertificates.LinearEvidenceCheck
