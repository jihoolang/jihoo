import Jihoo.NativeLoopTelescopes

/-! The exact native owned Fold telescope keeps its original count throughout
all iterations. The index proof is Lt(i,n); no iteration rule decrements n. -/
namespace Jihoo.NativeKernel

/-- Core.fold_body_type for any admitted accumulator representation. -/
def foldAccumulatorBodyType (n accumulator : Term) : Term :=
  .pi false .u64 (.pi true (.lt (.var 0) (n.rename Nat.succ))
    (.pi false (accumulator.rename (fun x => x + 2))
      (accumulator.rename (fun x => x + 3))))

/-- Core.binders counts raw leading lambdas, independently of their flags. -/
def hasLeadingLambdas : Nat → Term → Bool
  | 0, _ => true
  | count + 1, .lam _ _ body => hasLeadingLambdas count body
  | _ + 1, _ => false

@[simp] theorem foldAccumulatorBodyType_i64 (n : Term) :
    foldAccumulatorBodyType n .i64 = foldBodyType n := by
  simp only [foldAccumulatorBodyType, foldBodyType, Term.rename, renameArgs]

theorem foldAccumulatorBodyType_rename (n accumulator : Term) (ρ : Nat → Nat) :
    (foldAccumulatorBodyType n accumulator).rename ρ =
      foldAccumulatorBodyType (n.rename ρ) (accumulator.rename ρ) := by
  simp [foldAccumulatorBodyType, Term.rename, renameArgs, Op.binders, liftRenaming,
    Indexed.liftRenaming, Term.rename_comp]

theorem foldAccumulatorBodyType_subst (n accumulator : Term) (σ : Nat → Term) :
    (foldAccumulatorBodyType n accumulator).subst σ =
      foldAccumulatorBodyType (n.subst σ) (accumulator.subst σ) := by
  simp [foldAccumulatorBodyType, Term.subst, substArgs, Op.binders, liftSub, liftSubOne,
    Term.subst_rename, Term.rename_subst, Term.rename_comp]

end Jihoo.NativeKernel
