import Jihoo.NativeUnifiedProgram
import Jihoo.NativeOwnedLoopQuantity

namespace Jihoo.NativeKernel.Environment.OwnedLoopExamples

private abbrev zero : Term := .natural 0
private abbrev two : Term := .natural 2
private abbrev buf : Term := .buffer two
private abbrev allocated : Term := .alloc two (.integer 0)
private abbrev motive : Term := .lam false .u64 buf
private abbrev identity : Term := .lam false .u64 (.lam true (.lt (.var 0) two)
  (.lam false buf (.var 0)))
private abbrev freeBody : Term := .lam false .u64 (.lam true (.lt (.var 0) two)
  (.lam false buf (.free (.var 0) allocated)))
private abbrev storeBody : Term := .lam false .u64 (.lam true (.lt (.var 0) two)
  (.lam false buf (.store (.var 0) (.var 2) (.integer 7) (.var 1))))
private abbrev leaked : Term := .lam false .u64 (.lam true (.lt (.var 0) two)
  (.lam false buf allocated))
private abbrev doubled : Term := .lam false .u64 (.lam true (.lt (.var 0) two)
  (.lam false buf (.free (.var 0) (.free (.var 0) allocated))))
private abbrev factory : Term := .app (.lam false .u64 identity) zero
private abbrev effectful : Term := .free (.alloc (.natural 1) (.integer 0)) identity
private abbrev growingMotive : Term := .lam false .u64 (.buffer (.var 0))
private abbrev growingBody : Term := .lam false .u64 (.lam true (.lt (.var 0) two)
  (.lam false (.app (growingMotive.rename (fun x => x + 2)) (.var 1))
    (.free (.var 0) (.alloc (.uadd (.var 2) (.natural 1)) (.integer 0)))))

example : Checker.infer 32 empty [] false (.fold two allocated identity) = some buf := by cbv
example : Checker.infer 32 empty [] false (.fold two allocated freeBody) = some buf := by cbv
example : Checker.infer 32 empty [] false (.fold two allocated storeBody) = some buf := by cbv
example : Checker.infer 32 empty [] false (.loop two motive allocated freeBody) = some (.app motive two) := by cbv
example : Checker.infer 32 empty [] false (.loop two motive allocated storeBody) = some (.app motive two) := by cbv
example : Checker.infer 32 empty [] false (.loop two growingMotive (.alloc zero (.integer 0)) growingBody) =
    some (.app growingMotive two) := by cbv
example : UnifiedProgram.checkExpanded 32 64 empty ⟨buf, .loop two growingMotive (.alloc zero (.integer 0)) growingBody⟩ = true := by cbv
example : Checker.infer 32 empty [] false (.fold two allocated factory) = some buf := by cbv
example : UnifiedProgram.checkExpanded 32 64 empty ⟨buf, .fold two allocated factory⟩ = true := by cbv
example : Checker.infer 32 empty [] false (.fold two allocated effectful) = none := by cbv
example : Checker.infer 32 empty [] false (.loop two motive allocated effectful) = none := by cbv
example : Checker.infer 32 empty [] false (.fold two allocated leaked) = some buf := by cbv
example : Checker.infer 32 empty [] false (.loop two motive allocated doubled) = some (.app motive two) := by cbv
example : UnifiedProgram.checkExpanded 32 64 empty ⟨buf, .fold two allocated leaked⟩ = false := by cbv
example : UnifiedProgram.checkExpanded 32 64 empty ⟨buf, .loop two motive allocated doubled⟩ = false := by cbv
example : UnifiedProgram.checkExpanded 32 64 empty ⟨buf, .fold two allocated storeBody⟩ = true := by cbv
example : UnifiedProgram.checkExpanded 32 64 empty ⟨buf, .loop two motive allocated freeBody⟩ = true := by cbv
example : Checker.infer 32 empty [] false (.fold two zero (.lam false .u64
    (.lam true (.lt (.var 0) two) (.lam false .u64 (.var 0))))) = none := by cbv
example : IterationBodyAllowed empty true (.var 0) := Or.inl rfl
example : IterationMotiveAllowed empty true false (.var 0) := Or.inl rfl
example : Checker.iterationBodyOK empty freeBody = true := by cbv
example : iterationMemoryFree empty freeBody = false := by cbv
example : Checker.iterationBodyOK empty factory = true := by cbv
example : Checker.iterationBodyOK empty effectful = false := by cbv

end Jihoo.NativeKernel.Environment.OwnedLoopExamples
