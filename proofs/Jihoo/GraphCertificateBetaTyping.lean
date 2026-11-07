import Jihoo.CoreBridgeBetaTyping
import Jihoo.GraphCertificates

/-! Conditional target typing for actual accepted graph outputs. Acceptance
certifies a structural transformation, not the typing of every artifact. These
variants use beta-aware target typing. The input and replacement derivations
remain explicit, independent premises. -/
namespace Jihoo.GraphCertificates.Beta
open CoreBridge
open CoreBridge.Raw.Beta

/-- The decoded input is renamed into the decoded, represented actual output.
The context morphism must describe the certificate's exact shift amount. -/
theorem validate_shift_typed (h : validate c = true)
    (hop : c.operation = .shift amount)
    (hin : decode c.before c.input = some input)
    (ht : Raw.Beta.HasType Γ input A)
    (hρ : Raw.Renaming Γ Δ (fun k => k + amount)) :
    ∃ output, decode c.after c.output = some output ∧
      Represents c.after c.output output ∧
      Raw.Beta.HasType Δ output (A.rename (fun k => k + amount)) := by
  obtain ⟨_, input', output, hin', hout, _, hrep, hexpect⟩ := validate_sound h
  rw [hin] at hin'
  cases hin'
  simp only [expected, hop] at hexpect
  split at hexpect
  next =>
    cases hexpect
    exact ⟨_, hout, hrep, ht.renaming hρ⟩
  next => contradiction

/-- Accepted single substitution yields typing of the actual output root,
derived from typed input and replacement roots. Neither acceptance alone nor
an assumed typing judgment about the output is used as a substitute for proof. -/
theorem validate_substitute_typed (h : validate c = true)
    (hop : c.operation = .substitute replacement)
    (hin : decode c.before c.input = some input)
    (hvalue : decode c.before replacement = some value)
    (hbody : Raw.Beta.HasType (Γ.extend A) input B)
    (harg : Raw.Beta.HasType Γ value A) :
    ∃ output, decode c.after c.output = some output ∧
      Represents c.after c.output output ∧
      Raw.Beta.HasType Γ output (B.subst (Raw.single value)) := by
  obtain ⟨_, input', output, hin', hout, _, hrep, hexpect⟩ := validate_sound h
  rw [hin] at hin'
  cases hin'
  simp only [expected, hop] at hexpect
  split at hexpect
  next =>
    simp only [hvalue, pure] at hexpect
    cases hexpect
    exact ⟨_, hout, hrep, hbody.instantiate harg⟩
  next => contradiction

end Jihoo.GraphCertificates.Beta
