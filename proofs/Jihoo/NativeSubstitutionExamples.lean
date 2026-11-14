import Jihoo.NativeSubstitution

/-! Capture-avoidance and constructor-layout regression proofs on complete
native syntax. Branch evidence binds only the true child; continuation functions
and constructor case vectors introduce their binders through explicit Lam nodes. -/
namespace Jihoo.NativeKernel.SubstitutionExamples

macro "native_subst_example" : tactic =>
  `(tactic| (simp [Term.rename, renameArgs, Term.subst, substArgs,
    liftRenaming, Indexed.liftRenaming, liftSub, liftSubOne, single, Op.binders]))

theorem ifLt_capture :
    (Term.node .ifLt [.var 0, .var 1, .node .uadd [.var 0, .var 1], .var 0]).subst
      (single (.var 0)) =
    .node .ifLt [.var 0, .var 0, .node .uadd [.var 0, .var 1], .var 0] := by
  native_subst_example

theorem ifEq_evidence :
    (Term.node .ifEq [.var 0, .var 0, .var 0, .var 0]).subst
      (single (.node (.natural 7) [])) =
    .node .ifEq [.node (.natural 7) [], .node (.natural 7) [], .var 0,
      .node (.natural 7) []] := by
  native_subst_example

theorem lambda_capture :
    (Term.node (.lam false) [.node .u64 [], .var 1]).subst (single (.var 0)) =
    .node (.lam false) [.node .u64 [], .var 1] := by native_subst_example

theorem dependent_pi :
    (Term.node (.pi true) [.node .u64 [], .node .eq [.var 0, .var 1]]).rename Nat.succ =
    .node (.pi true) [.node .u64 [], .node .eq [.var 0, .var 2]] := by native_subst_example

theorem owned_continuations :
    (Term.node .load [.var 0, .var 1, .var 2,
      .node (.lam false) [.node .i64 [], .var 1]]).subst (single (.var 0)) =
    .node .load [.var 0, .var 0, .var 1,
      .node (.lam false) [.node .i64 [], .var 1]] := by native_subst_example

theorem eliminated_cases :
    (Term.node (.elim 3 2) [.var 0, .node (.lam true) [.node .u64 [], .var 1],
      .var 2, .var 3]).subst (single (.node (.natural 9) [])) =
    .node (.elim 3 2) [.node (.natural 9) [],
      .node (.lam true) [.node .u64 [], .node (.natural 9) []], .var 1, .var 2] := by
  native_subst_example

theorem false_branch_has_no_binder :
    ¬ (Term.node .ifEq [.node (.natural 0) [], .node (.natural 1) [],
      .node (.natural 7) [], .var 0]).Scoped 0 := by
  intro h
  cases h with
  | node h =>
      have bad := h 3 (.var 0) (by simp)
      cases bad with
      | var bound => simp [Op.binders] at bound

theorem every_constructor_arity (op : Op) (xs : List Term) (ρ : Nat → Nat)
    (h : (Term.node op xs).WellFormed) :
    (Term.node op xs |>.rename ρ).WellFormed := h.rename ρ

end Jihoo.NativeKernel.SubstitutionExamples
