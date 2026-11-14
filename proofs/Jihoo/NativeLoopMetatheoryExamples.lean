import Jihoo.NativePreservation
import Jihoo.NativeCheckerSoundness

/-! Typed substitution and contextual computation for native iteration. Initial
derivations come from kernel-reduced runs of the executable raw-term checker.
The proof loop uses its induction hypothesis; no loop-unrolling rule is assumed. -/
namespace Jihoo.NativeKernel.LoopMetatheoryExamples

private def one : Term := .natural 1
private def addition : Term := .uadd one (.natural 2)
private def scalarMotive : Term := .lam false .u64 .i64
private def proofMotive : Term := .lam false .u64 (.lt (.var 0) (.uadd (.var 0) one))
private def proofInit : Term := .decide (.natural 0) one

private def scalarStep (n : Term) : Term :=
  .lam false .u64 (.lam true (.lt (.var 0) (n.rename Nat.succ))
    (.lam false .i64 (.arith .add (.var 0) (.integer 1))))

private def proofStep (n : Term) : Term :=
  .lam false .u64 (.lam true (.lt (.var 0) (n.rename Nat.succ))
    (.lam true (.lt (.var 1) (.uadd (.var 1) one))
      (.ltAdd (.var 2) (.uadd (.var 2) one) one (.var 0))))

private def motiveAlias : Term := .app (.lam false .u64 proofMotive) (.natural 0)

private theorem openProofLoop : HasType [⟨.u64,false⟩] true
    (.loop (.var 0) proofMotive proofInit (proofStep (.var 0))) (.app proofMotive (.var 0)) :=
  Checker.infer_sound (fuel := 64) (by cbv)

theorem dependent_count_substitution : HasType [] true
    (.loop (.natural 3) proofMotive proofInit (proofStep (.natural 3))) (.app proofMotive (.natural 3)) := by
  have result := openProofLoop.ghostInstantiate (HasType.natural (ghost := true) (n := 3) (by decide))
  simpa [Term.subst,substArgs,single,Op.binders,liftSub,liftSubOne,Term.rename,renameArgs,
    one,proofMotive,proofInit,proofStep] using result

theorem fold_code_input_ghost_instantiation : HasType [] true
    (.fold (.natural 4) (.integer 0) (scalarStep (.natural 4))) .i64 := by
  have source : HasType [⟨.u64,false⟩] false
      (.fold (.var 0) (.integer 0) (scalarStep (.var 0))) .i64 :=
    Checker.infer_sound (fuel := 64) (by cbv)
  have result := source.ghostInstantiate (HasType.natural (ghost := true) (n := 4) (by decide))
  simpa [Term.subst,substArgs,single,Op.binders,liftSub,liftSubOne,Term.rename,renameArgs,scalarStep] using result

private theorem closedProofLoop : HasType [] true
    (.loop addition proofMotive proofInit (proofStep addition)) (.app proofMotive addition) :=
  Checker.infer_sound (fuel := 64) (by cbv)

theorem changed_count_keeps_original_result : HasType [] true
    (.loop (.natural 3) proofMotive proofInit (proofStep addition)) (.app proofMotive addition) := by
  exact closedProofLoop.ghostPreservation
    (Reduction.Step.node .loop [] [proofMotive,proofInit,proofStep addition] (.add 1 2 (by decide)))

theorem normalized_loop_keeps_original_result : HasType [] true
    (.loop (.natural 3) proofMotive proofInit (proofStep (.natural 3))) (.app proofMotive addition) := by
  have computed : Conversion.normalize 16 (.loop addition proofMotive proofInit (proofStep addition)) =
      .loop (.natural 3) proofMotive proofInit (proofStep (.natural 3)) := by cbv
  simpa only [computed] using closedProofLoop.ghostNormalize 16

theorem independent_loop_type_normalization : HasType [] true
    (.loop (.natural 3) proofMotive proofInit (proofStep (.natural 3))) (.lt (.natural 3) (.natural 4)) := by
  have term : Conversion.normalize 16 (.loop addition proofMotive proofInit (proofStep addition)) =
      .loop (.natural 3) proofMotive proofInit (proofStep (.natural 3)) := by cbv
  have type : Conversion.normalize 16 (.app proofMotive addition) = .lt (.natural 3) (.natural 4) := by cbv
  simpa only [term,type] using closedProofLoop.ghostNormalizeBoth 16 16

theorem changed_motive_keeps_original_result : HasType [] true
    (.loop (.natural 3) proofMotive proofInit (proofStep (.natural 3))) (.app motiveAlias (.natural 3)) := by
  have source : HasType [] true
      (.loop (.natural 3) motiveAlias proofInit (proofStep (.natural 3))) (.app motiveAlias (.natural 3)) :=
    Checker.infer_sound (fuel := 64) (by cbv)
  have beta : Reduction.Step motiveAlias proofMotive := by
    simpa [motiveAlias,proofMotive,one,Term.subst,substArgs,single,Op.binders,liftSub,liftSubOne,
      Term.rename,renameArgs] using Reduction.Step.beta false .u64 proofMotive (.natural 0)
  exact source.ghostPreservation
    (Reduction.Step.node .loop [.natural 3] [proofInit,proofStep (.natural 3)] beta)

theorem closed_loop_scope :
    (Term.loop (.natural 3) proofMotive proofInit (proofStep (.natural 3))).Scoped 0 :=
  dependent_count_substitution.term_scoped

private def refinementMotive : Term :=
  .lam false .u64 (.refine (.lam false .u64 (.eq (.var 0) (.var 1))))

private def refinementInit : Term :=
  .pack (.lam false .u64 (.eq (.var 0) (.natural 0))) (.natural 0) (.refl (.natural 0))

private def refinementStep (n : Term) : Term :=
  .lam false .u64 (.lam true (.lt (.var 0) (n.rename Nat.succ))
    (.lam false (.refine (.lam false .u64 (.eq (.var 0) (.var 2))))
      (.pack (.lam false .u64 (.eq (.var 0) (.uadd (.var 3) one)))
        (.uadd (.var 2) one) (.refl (.uadd (.var 2) one)))))

theorem refinement_accumulator_substitution : HasType [] true
    (.loop (.natural 4) refinementMotive refinementInit (refinementStep (.natural 4)))
      (.refine (.lam false .u64 (.eq (.var 0) (.natural 4)))) := by
  have source : HasType [⟨.u64,false⟩] false
      (.loop (.var 0) refinementMotive refinementInit (refinementStep (.var 0)))
      (.app refinementMotive (.var 0)) := Checker.infer_sound (fuel := 96) (by cbv)
  have substituted := source.ghostInstantiate (HasType.natural (ghost := true) (n := 4) (by decide))
  have closed : HasType [] true
      (.loop (.natural 4) refinementMotive refinementInit (refinementStep (.natural 4)))
      (.app refinementMotive (.natural 4)) := by
    simpa [refinementMotive,refinementInit,refinementStep,one,Term.subst,substArgs,single,
      Op.binders,liftSub,liftSubOne,Term.rename,renameArgs] using substituted
  have normalType : Conversion.normalize 16 (.app refinementMotive (.natural 4)) =
      .refine (.lam false .u64 (.eq (.var 0) (.natural 4))) := by cbv
  simpa only [Conversion.normalize_zero,normalType] using closed.ghostNormalizeBoth 0 16

end Jihoo.NativeKernel.LoopMetatheoryExamples
