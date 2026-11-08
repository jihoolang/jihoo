import Jihoo.CheckedPropositionalEvidence
namespace Jihoo.CoreBridge.PropositionalEvidence.Examples
open LinearNaturals LinearEvidence

def falseType : Ty := .atom (.equal (.lit ⟨0, by decide⟩) (.lit ⟨1, by decide⟩))

theorem false_assumption_is_usable : Derives [falseType] (.var 0) falseType :=
  .hyp rfl

theorem false_identity_is_valid :
    Derives [] (.lam true falseType.encode (.var 0)) (.arrow falseType falseType) :=
  .lam false_assumption_is_usable

theorem no_closed_false_evidence (h : Derives [] t falseType) : False := by
  have hh := h.closed_sound (fun _ => 0)
  change (0 : Nat) = 1 at hh
  omega

theorem composition (A B C : Ty) :
    Derives [] (.lam true (Ty.arrow A B).encode
      (.lam true (Ty.arrow B C).encode (.lam true A.encode
        (.app (.var 1) (.app (.var 2) (.var 0))))))
      (.arrow (.arrow A B) (.arrow (.arrow B C) (.arrow A C))) :=
  .lam (.lam (.lam (.app (.hyp rfl) (.app (.hyp rfl) (.hyp rfl)))))

example : (infer 0 32768 [] (.var 0)).isNone = true := rfl
example : (infer 128 0 [] (.var 0)).isNone = true := rfl
example : (infer 128 32768 [] (.var 0)).isNone = true := by decide
end Jihoo.CoreBridge.PropositionalEvidence.Examples
