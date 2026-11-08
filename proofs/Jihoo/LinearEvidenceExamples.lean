import Jihoo.CheckedLinearEvidence

namespace Jihoo.CoreBridge.LinearEvidence.Examples
open LinearNaturals

private def v : Expr 1 := .var ⟨0, by decide⟩

theorem universal_positive (ρ : Nat → Nat) :
    (Formula.all (.less zero (.add v one))).Holds ρ :=
  (Derives.lam (Derives.zeroLe v)).sound ρ

theorem symbolic_commutativity_checked :
    (check 0 (.lam false .u64 (.lam false .u64 (.refl (.uadd (.var 1) (.var 0)))))
      (.pi false .u64 (.pi false .u64
        (.eq (.uadd (.var 1) (.var 0)) (.uadd (.var 0) (.var 1)))))).isSome = true := by decide

theorem symbolic_zero_le_checked :
    (check 0 (.lam false .u64 (.zeroLe (.var 0)))
      (.pi false .u64 (.lt (.natural 0) (.uadd (.natural 1) (.var 0))))).isSome = true := by decide

theorem closed_computed_decision_checked :
    (check 0 (.decide (.uadd (.natural 1) (.natural 1)) (.natural 3))
      (.lt (.natural 2) (.uadd (.natural 1) (.natural 2)))).isSome = true := by decide

theorem wide_zero_le_checked :
    (check 0 (.zeroLe (.natural (wordBound - 1)))
      (.lt (.natural 0) (.uadd (.natural 1) (.natural (wordBound - 1))))).isSome = true := by decide

theorem distinct_binders_rejected :
    (check 0 (.lam false .u64 (.lam false .u64 (.refl (.var 0))))
      (.pi false .u64 (.pi false .u64 (.eq (.var 1) (.var 0))))).isSome = false := by decide

theorem false_under_quantifier_rejected :
    (check 0 (.lam false .u64 (.refl (.var 0)))
      (.pi false .u64 (.eq (.var 0) (.uadd (.var 0) (.natural 1))))).isSome = false := by decide

theorem true_claim_wrong_evidence_rejected :
    (check 0 (.refl (.natural 0)) (.lt (.natural 0) (.natural 1))).isSome = false := by decide

theorem arbitrary_beta_evidence_rejected :
    (check 0 (.app (.lam false .u64 (.refl (.var 0))) (.natural 1))
      (.eq (.natural 1) (.natural 1))).isSome = false := by decide

end Jihoo.CoreBridge.LinearEvidence.Examples
