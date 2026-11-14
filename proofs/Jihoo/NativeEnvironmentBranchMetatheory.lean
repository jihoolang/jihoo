import Jihoo.NativeEnvironmentContextConversion

/-! The fifth unified mutual judgment inherits the same proved ghost context
operations. Every branch has an independent native typing derivation. -/
namespace Jihoo.NativeKernel.Environment

theorem BranchTypes.ghost (branches : BranchTypes env ctx mode types terms) :
    BranchTypes env ctx true (types) (terms) := by
  apply BranchTypes.rec (t := branches)
    (motive_1 := fun _ _ _ _ _ => True) (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun ctx _ types terms _ => BranchTypes env ctx true (types) (terms))
  all_goals intros
  all_goals first | trivial | skip
  case nil => exact .nil
  case cons =>
    rename_i typed tail _ ihtail
    exact .cons typed.ghost ihtail

theorem BranchTypes.ghostRenaming (wf : UnifiedProgram.EnvWellFormed env)
    (branches : BranchTypes env ctx mode types terms) (related : Ghost.Renaming ctx target ρ) :
    BranchTypes env target true (types.map (Term.rename ρ)) (terms.map (Term.rename ρ)) := by
  revert related
  apply BranchTypes.rec (t := branches)
    (motive_1 := fun _ _ _ _ _ => True) (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun ctx _ types terms _ => Ghost.Renaming ctx target ρ → BranchTypes env target true (types.map (Term.rename ρ)) (terms.map (Term.rename ρ)))
  all_goals intros
  all_goals first | trivial | skip
  case nil => exact .nil
  case cons =>
    rename_i typed tail _ ihtail related
    exact .cons (typed.ghostRenaming wf related) (ihtail related)

theorem BranchTypes.ghostSubstitution (wf : UnifiedProgram.EnvWellFormed env)
    (branches : BranchTypes env ctx mode types terms) (related : Ghost.Substitution env ctx target σ) :
    BranchTypes env target true (types.map (Term.subst σ)) (terms.map (Term.subst σ)) := by
  revert related
  apply BranchTypes.rec (t := branches)
    (motive_1 := fun _ _ _ _ _ => True) (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun ctx _ types terms _ => Ghost.Substitution env ctx target σ → BranchTypes env target true (types.map (Term.subst σ)) (terms.map (Term.subst σ)))
  all_goals intros
  all_goals first | trivial | skip
  case nil => exact .nil
  case cons =>
    rename_i typed tail _ ihtail related
    exact .cons (typed.ghostSubstitution wf related) (ihtail related)

theorem BranchTypes.ghostContext (wf : UnifiedProgram.EnvWellFormed env)
    (branches : BranchTypes env ctx mode types terms) (related : Ghost.ContextConversion ctx target) :
    BranchTypes env target true (types) (terms) := by
  revert related
  apply BranchTypes.rec (t := branches)
    (motive_1 := fun _ _ _ _ _ => True) (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun ctx _ types terms _ => Ghost.ContextConversion ctx target → BranchTypes env target true (types) (terms))
  all_goals intros
  all_goals first | trivial | skip
  case nil => exact .nil
  case cons =>
    rename_i typed tail _ ihtail related
    exact .cons (typed.ghostContext wf related) (ihtail related)

end Jihoo.NativeKernel.Environment
