import Jihoo.MixedProofAdmission
import Jihoo.CoreEvaluation
import Jihoo.CorePayloadErasure

/-! The mathematical result of the explicit dual-checked operation. Native
checking alone is not the premise. The exact decoded original term and requested
type must independently pass mixed admission. IO/export fidelity remain trusted. -/
namespace Jihoo.VerifiedCore
open CoreBridge
open MixedProofFunctions.Checked.Snapshot

/-- Successful admission gives the same original type along every finite strict
execution, with value/step/explicit overflow-trap progress at its endpoint. -/
theorem execution_safety (a : GraphAccepted s)
    (hs : Raw.Beta.Evaluation.Steps a.rawTerm u) :
    Raw.Beta.HasType (fun _ => none) u a.rawType ∧ Raw.Beta.Evaluation.Outcome u :=
  Raw.Beta.Evaluation.execution_safety a.accepted.raw_typed hs

/-- Removal of annotations and computed proof payloads preserves every admitted
source execution. This retains binder slots and is not native erasure. -/
theorem erased_execution (a : GraphAccepted s)
    (hs : Raw.Beta.Evaluation.Steps a.rawTerm u) :
    Raw.Beta.Evaluation.Steps (Raw.Beta.PayloadErasure.erase a.rawTerm)
      (Raw.Beta.PayloadErasure.erase u) :=
  Raw.Beta.PayloadErasure.steps_erasure hs

/-- The proposition is the separately parsed requested input, not an inferred
replacement. -/
theorem requested_truth (a : GraphAccepted s)
    (hd : GraphCertificates.decode s.graph s.typeRoot = some R)
    (hp : formulaCandidate 32 [] R = some P) (ρ : Arithmetic.Env) : P.Holds ρ :=
  a.input_truth hd hp ρ

end Jihoo.VerifiedCore
