import Jihoo.NativeContextUnifiedExamples
import Jihoo.NativeContextModeSoundness
import Jihoo.NativeContextInterpretation

namespace Jihoo.NativeKernel.Environment.ContextDeltaExamples
open CodeKinds CallReplay ContextModes ContextQuantity

def typeAlias : Environment :=
  ⟨#[⟨.univ 1,.univ 0⟩],#[]⟩
def aliasedType : Term := .node (.global 0) []
def aliasedIdentity : Term := .lam false aliasedType (.lam false (.var 0) (.var 0))
def aliasedSignature : Term := .pi false aliasedType (.pi false (.var 0) (.var 1))

theorem kind_from_actual_delta_lookup :
    lookupKind 48 typeAlias [⟨aliasedType,false⟩] 0 = some (.type 0) := by cbv

theorem delta_context_is_checked : contextOK 48 typeAlias [⟨aliasedType,false⟩] = true := by cbv

theorem delta_generic_binder_representation :
    resolve 48 typeAlias [⟨aliasedType,false⟩] false (.var 0) = some .unrestricted := by cbv

theorem delta_dependent_signature_replay :
    (checked 56 typeAlias [] false aliasedIdentity [.u64,.natural 7]).map Prod.snd = some .u64 := by cbv

theorem delta_generic_closed_gate :
    checkClosed 56 64 typeAlias aliasedIdentity aliasedSignature = true := by cbv

theorem same_unified_delta_kind_and_global_call :
    (UnifiedProgram.checkProgram 64 128 [⟨.univ 1,.univ 0⟩,
      ⟨aliasedSignature,aliasedIdentity⟩,
      ⟨.u64,.app (.app (.node (.global 1) []) .u64) (.natural 7)⟩] []).isSome = true := by cbv

theorem forged_delta_kind_argument_rejected :
    checked 56 typeAlias [] false aliasedIdentity
      [.buffer (.natural 2),.alloc (.natural 2) (.integer 0)] = none := by cbv

end Jihoo.NativeKernel.Environment.ContextDeltaExamples
