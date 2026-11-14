import Jihoo.NativeOwnershipAdmission
import Jihoo.NativeResourceSyntax

namespace Jihoo.NativeKernel.NativeOwnershipAdmission.Examples

private abbrev two : Term := .natural 2
private abbrev zero : Term := .natural 0
private abbrev buf : Term := .buffer two
private abbrev emptyEnv : Environment := Environment.empty
private abbrev ownerType : Term := .pi false buf .u64
private abbrev good : Term := .lam false buf (.free (.var 0) zero)
private abbrev leaked : Term := .lam false buf zero
private abbrev doubled : Term := .lam false buf (.free (.var 0) (.free (.var 0) zero))
private abbrev captured : Term := .lam false buf (.strict zero (.lam false .u64 (.var 1)))
private abbrev loadContinuation : Term := .lam false .i64 (.lam false buf (.free (.var 0) (.var 1)))
private abbrev proof : Term := .decide zero two
private abbrev allocated : Term := .alloc two (.integer 0)

/-- Ordinary typing alone cannot serve as code admission for owned binders. -/
example : Environment.Checker.check 32 emptyEnv [] false leaked ownerType = true := by cbv
example : Environment.Checker.check 32 emptyEnv [] false doubled ownerType = true := by cbv
example : Environment.Checker.check 32 emptyEnv [] false captured (.pi false buf (.pi false .u64 buf)) = true := by cbv
example : check 32 32 emptyEnv ⟨ownerType, good⟩ = true := by cbv
example : check 32 32 emptyEnv ⟨ownerType, leaked⟩ = false := by cbv
example : check 32 32 emptyEnv ⟨ownerType, doubled⟩ = false := by cbv
example : check 32 32 emptyEnv ⟨.pi false buf (.pi false .u64 buf), captured⟩ = false := by cbv
example : check 32 32 emptyEnv ⟨buf, allocated⟩ = true := by cbv
example : check 32 32 emptyEnv ⟨buf, .store allocated zero (.integer 7) proof⟩ = true := by cbv
example : check 32 32 emptyEnv ⟨.u64, .free allocated zero⟩ = true := by cbv
example : check 32 32 emptyEnv ⟨.i64, .load allocated zero proof loadContinuation⟩ = true := by cbv
example : check 32 32 emptyEnv ⟨.univ 0, .ref buf⟩ = true := by cbv
example : check 32 32 emptyEnv ⟨.pi false (.ref buf) .i64,
    .lam false (.ref buf) (.index (.var 0) zero proof)⟩ = true := by cbv
example : Environment.Checker.infer 32 emptyEnv [] true (.borrow allocated) = some (.ref buf) := by cbv
example : Environment.Checker.infer 32 emptyEnv [] false (.borrow allocated) = none := by cbv
example : Environment.Checker.infer 32 emptyEnv [] true (.deref (.borrow allocated)) = some buf := by cbv
example : Environment.Checker.infer 32 emptyEnv [] false (.deref (.borrow allocated)) = none := by cbv
example : check 32 32 emptyEnv ⟨.ref buf, .borrow allocated⟩ = false := by cbv
example : check 32 0 emptyEnv ⟨ownerType, good⟩ = false := by cbv
example : check 0 32 emptyEnv ⟨ownerType, good⟩ = false := by cbv

end Jihoo.NativeKernel.NativeOwnershipAdmission.Examples
