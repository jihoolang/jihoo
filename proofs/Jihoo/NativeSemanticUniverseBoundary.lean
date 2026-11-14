import Jihoo.NativeSemanticCandidates

/-! Exact universe boundaries needed by a future stratified candidate model.
These are facts about every actual typing rule, including admitted globals,
families, resources, and arbitrary result conversions. They are not a supplied
universe interpretation or a full normalization theorem. -/
namespace Jihoo.NativeKernel.Environment.Semantics

private def InputUniverseBound : Term → Prop
  | .univ level => level < 32
  | _ => True

private theorem universe_bound (typed : HasType env ctx mode term type) : InputUniverseBound term := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ term _ _ => InputUniverseBound term)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case dataElim =>
    rename_i family entry analysis ctx motive proof ghost scrutinee indices types branches found isData boxed size motiveTyped scrutineeTyped generated branchTyped allowed ihm ihs ihb
    cases analysis <;> trivial

theorem universe_input_bound (typed : HasType env ctx mode (.univ level) type) : level < 32 :=
  universe_bound typed

theorem administrative_top_not_input : ¬ HasType env ctx mode (.univ 32) type := by
  intro typed
  have bound := universe_input_bound typed
  omega

theorem input_universe_ceiling_rejected (outside : 32 ≤ level) :
    ¬ HasType env ctx mode (.univ level) type := by
  intro typed
  have bound := universe_input_bound typed
  omega

theorem no_universe_self_typing (wf : UnifiedProgram.EnvWellFormed env) : ¬ HasType env ctx mode (.univ level) (.univ level) :=
  HasType.no_type_in_type wf

theorem universe_not_proposition (wf : UnifiedProgram.EnvWellFormed env) : ¬ HasType env ctx mode (.univ level) .prop :=
  HasType.universe_not_proposition wf

theorem proposition_universe_separate (wf : UnifiedProgram.EnvWellFormed env) (proposition : HasType env ctx mode term .prop)
    (classified : HasType env ctx otherMode term (.univ level)) : False :=
  proposition.sorts_do_not_collapse wf classified

end Jihoo.NativeKernel.Environment.Semantics
