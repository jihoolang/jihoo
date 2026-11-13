import Jihoo

namespace Jihoo.CommonCompositionContract
#print axioms Transfer.then
#print axioms Transfer.steps
#print axioms node_pipeline
#print axioms supported_induction
#print axioms literal_supported
#print axioms opaque_rejected
#print axioms idle
#print axioms two_idles
end Jihoo.CommonCompositionContract

namespace Jihoo.CommonDataCaseRelocatedContext.Checks
open CommonCompositionContract CommonDataTargetContext CommonDataCaseCfg
open CommonDataReference RecursiveLexicalFields CommonDataCaseEntryContext
open CommonDataReferenceChecks (image source)
open CommonDataTargetContext.Checks (heap ctx env)
open CommonDataCaseEntryContext.Checks
#print axioms Jihoo.CommonDataCaseRelocatedContext.node
#print axioms Jihoo.CommonDataCaseRelocatedContext.nil
#print axioms Jihoo.CommonDataCaseRelocatedContext.entryProvider
#print axioms node_transfer
#print axioms node_valid
#print axioms nil_transfer
#print axioms nil_output_valid
#print axioms node_zero_rejected
end Jihoo.CommonDataCaseRelocatedContext.Checks

namespace Jihoo.CommonDataBranchFinishChecks
open CommonDataBranchFinish CommonCompositionContract CommonDataTargetContext
open CommonDataReference
#print axioms finish_context
#print axioms finish_authority
#print axioms finish_result
#print axioms body_finish
#print axioms result_preserved
#print axioms pending_not_result
#print axioms concrete_walk
#print axioms concrete_execution
#print axioms nested_buffers
#print axioms reject_alias
end Jihoo.CommonDataBranchFinishChecks

namespace Jihoo.CommonDataRestrictedCompositionChecks
open ReferenceCfg ReferenceCalls CommonDataCaseCfg CommonDataCaseRelocation
open CommonDataRestrictedComposition
#print axioms Fragment.size
#print axioms linked_eq
#print axioms Placement.program
#print axioms assemble_size
#print axioms assemble_placement
#print axioms Placement.walk
#print axioms Placement.node_entry
#print axioms Placement.nil_entry
#print axioms nested_jump
#print axioms placed_induction
#print axioms nested_run
#print axioms nested_run_framed
#print axioms three_placements
#print axioms nested_steps
end Jihoo.CommonDataRestrictedCompositionChecks

namespace Jihoo.CommonDataCaseRegisterSafetyChecks
open ReferenceCfg ReferenceCalls CommonDataCaseCfg CommonDataCaseRelocation
open CommonDataRestrictedComposition CommonDataCaseRegisterSafety
#print axioms safe_preserves
#print axioms safe_iff_uniform
#print axioms safe_reserved
#print axioms RestrictedPlacement.reserved
#print axioms no_node_layout
#print axioms live_context_rejected
#print axioms unsafe_rejected
#print axioms checked_node
#print axioms checked_nil
#print axioms Agrees.trans
#print axioms node_rejects_sibling
#print axioms nil_preserves_sibling
#print axioms collision_run
#print axioms sibling_overwritten
#print axioms collision_prevented
#print axioms safe_node_runs
#print axioms safe_nil_runs
#print axioms collision_steps
end Jihoo.CommonDataCaseRegisterSafetyChecks

#print axioms Jihoo.CommonCaseIntegration.node_finish
#print axioms Jihoo.CommonCaseIntegration.nil_entry
