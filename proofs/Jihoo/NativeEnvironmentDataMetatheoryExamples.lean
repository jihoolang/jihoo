import Jihoo.NativeEnvironmentContextualPreservation

/-! Checked-history regressions for the expanded same judgment: dependent data
parameters, motive computation, owned iteration, and family references. -/
namespace Jihoo.NativeKernel.Environment.DataMetatheoryExamples

private def paramNat (index : Term) : Term := .node (.ind 0 1) [index]
private def declaration : FamilyDeclaration :=
  ⟨true,1,1,[.pi true .u64 (paramNat (.var 0)),
    .pi true .u64 (.pi false (paramNat (.var 0)) (paramNat (.var 1)))],0⟩
private def entry : CheckedFamily :=
  ⟨declaration,[⟨[⟨true,.u64,none⟩],[.var 0]⟩,
    ⟨[⟨true,.u64,none⟩,⟨false,paramNat (.var 0),some [.var 0]⟩],[.var 1]⟩],true⟩
private def checkedEnv : Environment := ⟨#[],#[entry]⟩
private theorem history : UnifiedProgram.UnifiedProgramChecked [] [declaration] checkedEnv :=
  UnifiedProgram.checkProgram_sound
    (by cbv : UnifiedProgram.checkProgram 32 32 [] [declaration] = some checkedEnv)
private def motive : Term := .lam false (paramNat (.var 0)) .u64
private def branches : List Term :=
  [.natural 0,.lam true (paramNat (.var 0)) (.lam false .u64 (.var 0))]
private def elimination (selectedMotive : Term) : Term :=
  .node (.elim 0 2) (selectedMotive :: (branches ++ [.node (.con 0 0 1) [.var 0]]))
private theorem source : HasType checkedEnv [⟨.u64,false⟩] false (elimination motive) .u64 :=
  Checker.check_sound (by cbv : Checker.check 40 checkedEnv [⟨.u64,false⟩] false (elimination motive) .u64 = true)

/-- Actual authenticated data signatures justify every new dependent branch
telescope while substituting its ambient parameter. -/
theorem data_parameter_instantiated : HasType checkedEnv [] true
    ((elimination motive).subst (single (.natural 7))) .u64 := by
  simpa only [Term.subst,substArgs] using
    source.ghostInstantiate history.wellFormed (HasType.natural (by decide) : HasType checkedEnv [] true (.natural 7) .u64)

theorem data_parameter_weakened : HasType checkedEnv [⟨.i64,true⟩,⟨.u64,false⟩] true
    ((elimination motive).rename Nat.succ) .u64 := by
  simpa only [Term.rename,renameArgs] using source.ghostWeaken history.wellFormed .i64 true

/-- Data and proposition elimination share the actual native Elim operator;
its checked family metadata still determines a unique result across modes. -/
theorem data_elimination_unique (other : HasType checkedEnv [⟨.u64,false⟩] mode (elimination motive) T) :
    Conversion.Conv checkedEnv .u64 T := source.unique history.wellFormed other

private def reducibleMotive : Term := .lam false (paramNat (.var 0))
  (.app (.lam false .u64 .u64) (.natural 0))

/-- The generated data branch types are transported by proved full conversion
when a computation occurs inside the motive. -/
theorem data_motive_contextual_computation : HasType checkedEnv [⟨.u64,false⟩] true
    (elimination motive) .u64 := by
  have typed : HasType checkedEnv [⟨.u64,false⟩] false (elimination reducibleMotive) .u64 :=
    Checker.check_sound (by cbv : Checker.check 40 checkedEnv [⟨.u64,false⟩] false
      (elimination reducibleMotive) .u64 = true)
  have beta : ACU.MixedRed (.app (.lam false .u64 .u64) (.natural 0)) .u64 := by
    simpa only [Term.subst,substArgs] using
      (ACU.MixedRed.compute (.beta false .u64 .u64 (.natural 0)))
  have changed : ACU.MixedRed reducibleMotive motive :=
    .node (.lam false) (.cons (.refl _) (.cons beta .nil))
  exact typed.ghostMixedRed history.wellFormed
    (.node (.elim 0 2) (.cons changed (.cons (.refl _) (.cons (.refl _) (.cons (.refl _) .nil)))))

private abbrev buffer : Term := .buffer (.natural 2)
private abbrev allocated : Term := .alloc (.natural 2) (.integer 0)
private def ownedFold : Term := .fold (.natural 1) allocated
  (.lam false .u64 (.lam true (.lt (.var 0) (.natural 1)) (.lam false buffer (.var 0))))
private theorem foldTyped : HasType empty [] false ownedFold buffer :=
  Checker.check_sound (by cbv : Checker.check 32 empty [] false ownedFold buffer = true)
private theorem emptyWellFormed : UnifiedProgram.EnvWellFormed empty :=
  UnifiedProgram.checkProgram_wellFormed
    (by cbv : UnifiedProgram.checkProgram 24 24 [] [] = some empty)

theorem owned_fold_result_unique (other : HasType empty [] mode ownedFold T) :
    Conversion.Conv empty buffer T := foldTyped.unique emptyWellFormed other

theorem owned_fold_weakened : HasType empty [⟨.u64,true⟩] true
    (ownedFold.rename Nat.succ) buffer := by
  simpa only [rename_buffer,Term.rename,renameArgs] using foldTyped.ghostWeaken emptyWellFormed .u64 true

/-- General owned references include the actual boxed family, beyond Buffer. -/
theorem family_borrow_round_trip : HasType checkedEnv [⟨.u64,false⟩] true
    (.node (.con 0 0 1) [.var 0]) (paramNat (.var 0)) := by
  have typed : HasType checkedEnv [⟨.u64,false⟩] true
      (.deref (.borrow (.node (.con 0 0 1) [.var 0]))) (paramNat (.var 0)) :=
    Checker.check_sound (by cbv : Checker.check 32 checkedEnv [⟨.u64,false⟩] true
      (.deref (.borrow (.node (.con 0 0 1) [.var 0]))) (paramNat (.var 0)) = true)
  exact typed.ghostDerefBorrow history.wellFormed

end Jihoo.NativeKernel.Environment.DataMetatheoryExamples
