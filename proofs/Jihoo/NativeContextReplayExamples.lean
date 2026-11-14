import Jihoo.NativeContextModes
import Jihoo.NativeCallReplay

namespace Jihoo.NativeKernel.Environment.ContextReplayExamples
open CodeKinds CallReplay ContextModes

def typeContext : Context := [⟨.univ 0, false⟩]
def familyContext : Context := [⟨.u64, false⟩, ⟨.pi false .u64 (.univ 0), false⟩]
def owner : Term := .buffer (.natural 2)
def allocated : Term := .alloc (.natural 2) (.integer 0)
def genericIdentity : Term := .lam false (.univ 0) (.lam false (.var 0) (.var 0))

theorem genuine_generic_identity_typed :
    Checker.check 40 .empty [] false genericIdentity
      (.pi false (.univ 0) (.pi false (.var 0) (.var 1))) = true := by cbv

theorem authentic_type_context : contextOK 32 .empty typeContext = true := by cbv

theorem universe_binder_representation : resolve 32 .empty [] false (.univ 0) = some .unrestricted := by cbv

theorem generic_binder_representation : resolve 32 .empty typeContext false (.var 0) = some .unrestricted := by cbv

theorem family_context_checked : contextOK 32 .empty familyContext = true := by cbv

theorem abstract_indexed_family_kind :
    spine 32 .empty familyContext (.app (.var 1) (.var 0)) = some (.type 0) := by cbv

theorem indexed_family_binder_representation :
    resolve 32 .empty familyContext false (.app (.var 1) (.var 0)) = some .unrestricted := by cbv

/-- The index is genuinely U64-typed although recursive raw plainness fails. -/
theorem typed_unplain_index :
    Checker.check 32 .empty [] true (.strict owner (.natural 0)) .u64 = true ∧
      plain .empty (.strict owner (.natural 0)) = false := by cbv

theorem unplain_index_kind_replay :
    spine 40 .empty [⟨.pi false .u64 (.univ 0), false⟩]
      (.app (.var 0) (.strict owner (.natural 0))) = some (.type 0) := by cbv

/-- Additive U64 trees need not collapse to a valid literal payload. -/
theorem above_word_index_replay :
    spine 40 .empty [⟨.pi false .u64 (.univ 0), false⟩]
      (.app (.var 0) (.uadd (.natural (2^64-1)) (.natural (2^64-1)))) = some (.type 0) := by cbv

theorem forged_owner_as_kind_rejected :
    lookupKind 32 .empty [⟨owner, false⟩] 0 = none := by cbv

theorem higher_order_kind_rejected :
    lookupKind 32 .empty [⟨.pi false (.univ 0) (.univ 0), false⟩] 0 = none := by cbv

theorem forged_erased_type_context_rejected :
    contextOK 32 .empty [⟨.univ 0, true⟩] = false := by cbv

theorem unscoped_context_rejected :
    contextOK 32 .empty [⟨.var 0, false⟩] = false := by cbv

theorem unknown_scalar_callee_signature :
    (checked 40 .empty [⟨.pi false .u64 .u64, false⟩] false (.var 0) [.natural 0]).map Prod.snd = some .u64 := by cbv

theorem unknown_owned_callee_signature :
    (checked 40 .empty [⟨.pi false owner owner, false⟩] false (.var 0) [allocated]).map Prod.snd = some owner := by cbv

theorem genuine_dependent_call_replay :
    (checked 48 .empty [⟨.pi false (.univ 0) (.pi false (.var 0) (.var 1)), false⟩]
      false (.var 0) [.u64, .natural 0]).map Prod.snd = some .u64 := by cbv

theorem forged_type_argument_rejected :
    checked 48 .empty [⟨.pi false (.univ 0) (.pi false (.var 0) (.var 1)), false⟩]
      false (.var 0) [owner, allocated] = none := by cbv

def dependentErasures : Term :=
  .pi true .u64 (.pi false (.buffer (.var 0)) (.buffer (.var 1)))

theorem dependent_erasure_replayed :
    ((checked 48 .empty [⟨dependentErasures, false⟩] false (.var 0)
      [.natural 2, allocated]).map fun result => runtimeArguments result.1) = some [allocated] := by cbv

theorem unknown_forged_context_rejected :
    checked 32 .empty [⟨.pi false (.var 0) .u64, false⟩] false (.var 0) [.natural 0] = none := by cbv

theorem owned_partial_capture_rejected :
    partialOK 32 .empty [] [⟨false, owner, allocated⟩] (.pi false .u64 owner) = false := by cbv

theorem owned_completed_call_allowed :
    partialOK 32 .empty [] [⟨false, owner, allocated⟩] owner = true := by cbv

theorem scalar_factory_allowed :
    partialOK 32 .empty [] [⟨false, .u64, .natural 0⟩] (.pi false owner owner) = true := by cbv

theorem erased_owner_not_evaluated :
    runtimeArguments [⟨true, owner, allocated⟩] = [] := by cbv

/-- Consuming an owner may return an abstract indexed type, whose actual kind
certificate excludes function representations under admissible closure. -/
theorem owned_abstract_indexed_result_allowed :
    partialOK 48 .empty familyContext [⟨false,owner,allocated⟩]
      (.app (.var 1) (.var 0)) = true := by cbv

theorem owner_neutral_spelling_without_kind_rejected :
    partialOK 48 .empty [⟨owner,false⟩] [⟨false,owner,allocated⟩] (.var 0) = false := by cbv

theorem forged_indexed_kind_rejected :
    partialOK 48 .empty [⟨.u64,false⟩,⟨.pi false .u64 owner,false⟩]
      [⟨false,owner,allocated⟩] (.app (.var 1) (.var 0)) = false := by cbv

end Jihoo.NativeKernel.Environment.ContextReplayExamples
