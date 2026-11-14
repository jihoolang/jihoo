import Jihoo.NativeBackMetatheory
import Jihoo.NativeUnifiedProgram

/-! Kernel-reduced owner-return checks use the same environment checker and
closed metadata-derived resource gate as full mixed program admission. -/
namespace Jihoo.NativeKernel.Environment.BackExamples

private abbrev buf : Term := .buffer (.natural 2)
private abbrev zero : Term := .natural 0
private abbrev motive : Term := .lam false buf .u64
private abbrev proofMotive : Term := .lam false buf (.eq zero zero)
private abbrev owner : Term := .alloc (.natural 2) (.integer 0)
private abbrev given : Term := .give false motive owner (.natural 7)
private abbrev erasedGiven : Term := .give true proofMotive owner (.refl zero)
private abbrev continuation : Term := .lam false buf (.lam false .u64 (.free (.var 1) (.var 0)))
private abbrev proofContinuation : Term :=
  .lam false buf (.lam true (.eq zero zero) (.free (.var 1) (.natural 7)))
private abbrev leaked : Term := .lam false buf (.lam false .u64 (.var 0))
private abbrev doubled : Term :=
  .lam false buf (.lam false .u64 (.free (.var 1) (.free (.var 1) (.var 0))))
private abbrev functionContinuation : Term :=
  .lam false buf (.lam false .u64 (.free (.var 1) (.lam false .u64 (.var 0))))

example : Checker.infer 32 empty [] false (.back false buf motive) = some (.univ 0) := by cbv
example : Checker.infer 32 empty [] false (.back true buf proofMotive) = some (.univ 0) := by cbv
example : Checker.infer 32 empty [] false given = some (.back false buf motive) := by cbv
example : Checker.infer 32 empty [] false erasedGiven = some (.back true buf proofMotive) := by cbv
example : Checker.infer 32 empty [] false (.take given continuation) = some .u64 := by cbv
example : Checker.infer 32 empty [] false (.take erasedGiven proofContinuation) = some .u64 := by cbv
example : Checker.infer 32 empty [] false (.take given (.lam false buf (.lam false .u64 (.var 1)))) = some buf := by cbv
example : Checker.infer 32 empty [] true (.take given functionContinuation) = some (.pi false .u64 .u64) := by cbv
example : Checker.infer 32 empty [] false (.take given functionContinuation) = none := by cbv
example : Checker.infer 32 empty [] true (.back false buf (.lam false buf (.pi false .u64 .u64))) = none := by cbv
example : Checker.infer 32 empty [] false (.back false .u64 (.lam false .u64 .u64)) = none := by cbv
example : Checker.infer 32 empty [] false (.back true buf motive) = none := by cbv
example : Checker.infer 32 empty [] false (.back false buf proofMotive) = none := by cbv
example : Checker.infer 32 empty [] false (.back false buf (.lam false buf (.array zero))) = none := by cbv
example : Checker.infer 32 empty [] false (.back false buf (.lam false buf (.ref buf))) = none := by cbv
example : Checker.infer 32 empty [] false (.give false motive owner (.integer 7)) = none := by cbv
example : Checker.infer 32 empty [] false (.take erasedGiven continuation) = none := by cbv
example : Checker.infer 32 empty [] false (.take given (.lam false (.buffer (.natural 3))
    (.lam false .u64 (.free (.var 1) (.var 0))))) = none := by cbv
example : Checker.infer 32 empty [] false (.take given (.lam false buf (.free (.var 0) zero))) = none := by cbv
example : Checker.infer 32 empty [] false (.take given leaked) = some .u64 := by cbv
example : Checker.infer 32 empty [] false (.take given doubled) = some .u64 := by cbv
example : EnvironmentQuantity.check 64 empty (.take given leaked) = false := by cbv
example : EnvironmentQuantity.check 64 empty (.take given doubled) = false := by cbv
example : EnvironmentQuantity.check 64 empty (.take given continuation) = true := by cbv
example : UnifiedProgram.checkExpanded 32 64 empty ⟨.u64, .take given continuation⟩ = true := by cbv
example : UnifiedProgram.checkExpanded 32 64 empty ⟨.u64, .take given leaked⟩ = false := by cbv
example : UnifiedProgram.checkExpanded 32 64 empty ⟨.u64, .take given doubled⟩ = false := by cbv
example : (takeBodyType true buf proofMotive .u64).rename (fun x => x + 3) =
    takeBodyType true buf proofMotive .u64 := by
  rw [rename_takeBodyType]
  simp [Term.rename, renameArgs, Op.binders, liftRenaming]
example : BackRepresentation empty true false (.var 0) := ghost_backRepresentation _ _ _
example : fixedRepresentation empty (.buffer (.var 0)) = true := by cbv
example : fixedRepresentation empty (.ref buf) = false := by cbv

example : Checker.infer 32 empty [] false (.back false (.back false buf motive)
    (.lam false (.back false buf motive) .u64)) = none := by cbv
example : fixedRepresentation empty (.back false buf motive) = true := by cbv
example : fixedRepresentation empty (.refine (.lam false .u64 (.eq (.var 0) (.var 0)))) = true := by cbv
example : fixedRepresentation empty .i64 = true := by cbv

private def ownerDependentContext : Context :=
  [⟨.lt zero zero, true⟩, ⟨.pi false buf (.univ 0), false⟩]
private def resultDependentContext : Context :=
  [⟨.lt zero zero, true⟩, ⟨.pi false .u64 (.univ 0), false⟩]
private def ownerDependent : Term := .lam false buf (.lam false .u64
  (.free (.var 1) (.absurd (.app (.var 3) (.var 1)) (.var 2))))
private def resultDependent : Term := .lam false buf (.lam false .u64
  (.free (.var 1) (.absurd (.app (.var 3) (.var 0)) (.var 2))))
example : Checker.infer 48 empty ownerDependentContext true ownerDependent =
    some (.pi false buf (.pi false .u64 (.app (.var 3) (.var 1)))) := by cbv
example : Checker.infer 48 empty resultDependentContext true resultDependent =
    some (.pi false buf (.pi false .u64 (.app (.var 3) (.var 0)))) := by cbv
example : Checker.infer 48 empty ownerDependentContext true (.take given ownerDependent) = none := by cbv
example : Checker.infer 48 empty resultDependentContext true (.take given resultDependent) = none := by cbv

end Jihoo.NativeKernel.Environment.BackExamples
