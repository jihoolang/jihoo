import Jihoo.MixedProofAdmission
import Jihoo.MixedProofFunctionsExamples

namespace Jihoo.MixedProofFunctions.Checked.Snapshot
open CoreBridge (Raw)
open GraphCertificates

set_option maxRecDepth 4096

def identity : Raw := .lam true (.eq (.natural 7) (.natural 7)) (.var 0)
def identityType : Raw := .pi true (.eq (.natural 7) (.natural 7)) (.eq (.natural 7) (.natural 7))

theorem proof_lambda_admitted : (admit identity identityType).isSome = true := by decide +kernel

theorem mixed_inference_computes :
    inferType 0 [] Examples.retain =
      some (.all (.arrow Examples.same (.all (.eq (.var 1) (.var 1))))) := by decide +kernel

theorem wrong_erasure_rejected :
    (admit (.lam false (.eq (.natural 7) (.natural 7)) (.var 0)) identityType).isSome = false := by decide +kernel

theorem proof_not_an_index :
    formulaCandidate 32 [.value] (.eq (.var 0) (.var 0)) = none := by decide +kernel

theorem forward_index_rejected :
    formulaCandidate 32 [] (.pi true (.eq (.var 0) (.var 0)) (.eq (.natural 0) (.natural 0))) = none := by decide +kernel

theorem false_snapshot_rejected :
    (admitSnapshot ⟨2, 3, #[.natural 0, .natural 1, .refl 0, .eq 0 1]⟩).isSome = false := by decide +kernel

theorem literal_false_type_impossible : ¬ Nonempty (Accepted r (.eq (.natural 0) (.natural 1))) :=
  false_equality_excluded (by decide) (by decide) (by decide)

end Jihoo.MixedProofFunctions.Checked.Snapshot
