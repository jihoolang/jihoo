import Jihoo.NativeContextQuantityExamples
import Jihoo.NativeUnifiedAdmission

namespace Jihoo.NativeKernel.Environment.ContextUnifiedExamples
open ContextReplayExamples ContextQuantityExamples

def genericType : Term := .pi false (.univ 0) (.pi false (.var 0) (.var 1))

theorem same_unified_generic_identity :
    (UnifiedProgram.checkProgram 64 128 [⟨genericType,genericIdentity⟩] []).isSome = true := by cbv

theorem same_unified_global_generic_replay :
    (UnifiedProgram.checkProgram 64 128 [⟨genericType,genericIdentity⟩,
      ⟨.u64,.app (.app (.node (.global 0) []) .u64) (.natural 7)⟩] []).isSome = true := by cbv

theorem same_unified_unknown_owned_callee :
    UnifiedProgram.checkExpanded 64 128 .empty
      ⟨.pi false (.pi false owner owner) (.pi false owner owner),ownerCaller⟩ = true := by cbv

def unknownBody : Term := .lam false .u64 (.lam true (.lt (.var 0) (.natural 2))
  (.lam false owner (.app (.var 3) (.var 0))))

theorem same_unified_owned_fold_unknown_step :
    UnifiedProgram.checkExpanded 64 128 .empty
      ⟨.pi false (.pi false owner owner) owner,
        .lam false (.pi false owner owner) (.fold (.natural 2) allocated unknownBody)⟩ = true := by cbv

theorem same_unified_owned_loop_unknown_step :
    UnifiedProgram.checkExpanded 64 128 .empty
      ⟨.pi false (.pi false owner owner) owner,
        .lam false (.pi false owner owner) (.loop (.natural 2) (.lam false .u64 owner) allocated unknownBody)⟩ = true := by cbv

theorem same_unified_owned_callee_abstract_result :
    (UnifiedProgram.checkProgram 64 128 [⟨indexedOwnerCallerType,indexedOwnerCaller⟩] []).isSome = true := by cbv

end Jihoo.NativeKernel.Environment.ContextUnifiedExamples
