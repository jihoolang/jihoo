import Jihoo.NativeContextQuantity
import Jihoo.NativeContextReplayExamples

namespace Jihoo.NativeKernel.Environment.ContextQuantityExamples
open ContextQuantity ContextReplayExamples

theorem generic_identity_quantity :
    checkClosed 48 48 .empty genericIdentity
      (.pi false (.univ 0) (.pi false (.var 0) (.var 1))) = true := by cbv

def scalarCaller : Term := .lam false (.pi false .u64 .u64) (.app (.var 0) (.natural 0))
theorem unknown_scalar_call_quantity :
    checkClosed 48 48 .empty scalarCaller (.pi false (.pi false .u64 .u64) .u64) = true := by cbv

def ownerCaller : Term := .lam false (.pi false owner owner)
  (.lam false owner (.app (.var 1) (.var 0)))
theorem unknown_owned_call_quantity :
    checkClosed 48 48 .empty ownerCaller
      (.pi false (.pi false owner owner) (.pi false owner owner)) = true := by cbv

def leakingOwner : Term := .lam false owner (.natural 0)
theorem typed_owner_leak_rejected :
    Checker.check 48 .empty [] false leakingOwner (.pi false owner .u64) = true ∧
    checkClosed 48 48 .empty leakingOwner (.pi false owner .u64) = false := by cbv

def doubledOwner : Term := .lam false owner (.strict (.var 0) (.var 0))
theorem typed_owner_double_rejected :
    Checker.check 48 .empty [] false doubledOwner (.pi false owner owner) = true ∧
    checkClosed 48 48 .empty doubledOwner (.pi false owner owner) = false := by cbv

def capturedOwner : Term := .lam false owner
  (.strict (.natural 0) (.lam false .u64 (.var 1)))
theorem genuine_outer_capture_rejected :
    Checker.check 48 .empty [] false capturedOwner (.pi false owner (.pi false .u64 owner)) = true ∧
    checkClosed 48 48 .empty capturedOwner (.pi false owner (.pi false .u64 owner)) = false := by cbv

def partialOwner : Term := .app (.lam false owner (.lam false .u64 (.var 1))) allocated
theorem partial_owned_capture_rejected :
    Checker.check 48 .empty [] false partialOwner (.pi false .u64 owner) = true ∧
    checkClosed 48 48 .empty partialOwner (.pi false .u64 owner) = false := by cbv

def scalarFactory : Term := .app (.lam false .u64 (.lam false owner (.var 0))) (.natural 0)
theorem scalar_factory_quantity :
    checkClosed 48 48 .empty scalarFactory (.pi false owner owner) = true := by cbv

def erasedOwnerCaller : Term := .lam false dependentErasures
  (.app (.app (.var 0) (.natural 2)) allocated)
theorem dependent_erasure_call_quantity :
    checkClosed 56 56 .empty erasedOwnerCaller (.pi false dependentErasures owner) = true := by cbv

def genericCaller : Term := .lam false
  (.pi false (.univ 0) (.pi false (.var 0) (.var 1)))
  (.app (.app (.var 0) .u64) (.natural 0))
theorem dependent_generic_call_quantity :
    checkClosed 56 56 .empty genericCaller
      (.pi false (.pi false (.univ 0) (.pi false (.var 0) (.var 1))) .u64) = true := by cbv

def abstractFamilyIdentity : Term := .lam false (.pi false .u64 (.univ 0))
  (.lam false .u64 (.lam false (.app (.var 1) (.var 0)) (.var 0)))
theorem abstract_family_identity_quantity :
    checkClosed 56 56 .empty abstractFamilyIdentity
      (.pi false (.pi false .u64 (.univ 0))
        (.pi false .u64 (.pi false (.app (.var 1) (.var 0)) (.app (.var 2) (.var 1))))) = true := by cbv

def indexedOwnerCaller : Term := .lam false (.pi false .u64 (.univ 0))
  (.lam false .u64 (.lam false (.pi false owner (.app (.var 2) (.var 1)))
    (.lam false owner (.app (.var 1) (.var 0)))))

def indexedOwnerCallerType : Term := .pi false (.pi false .u64 (.univ 0))
  (.pi false .u64 (.pi false (.pi false owner (.app (.var 2) (.var 1)))
    (.pi false owner (.app (.var 3) (.var 2)))))

theorem owned_callee_abstract_result_quantity :
    checkClosed 64 64 .empty indexedOwnerCaller indexedOwnerCallerType = true := by cbv

end Jihoo.NativeKernel.Environment.ContextQuantityExamples
