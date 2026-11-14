import Jihoo.NativeResourceSyntax

/-! Native owner-return syntax and its exact two-argument continuation telescope.
The syntax algebra authorizes neither heap ownership nor a live loan. -/
namespace Jihoo.NativeKernel

namespace Term
@[match_pattern] abbrev back (erased : Bool) (owner motive : Term) : Term :=
  .node (.back erased) [owner, motive]
@[match_pattern] abbrev give (erased : Bool) (motive owner result : Term) : Term :=
  .node (.give erased) [motive, owner, result]
@[match_pattern] abbrev take (value continuation : Term) : Term :=
  .node .take [value, continuation]
end Term

/-- Under the owner binder, the result has the motive applied to that owner. -/
def takeResultType (motive : Term) : Term :=
  .node .app [motive.rename Nat.succ, .var 0]

/-- Exact native continuation: owner:T, result:M(owner), then an outside type
independent of both arguments. Only the motive result may be erased. -/
def takeBodyType (erased : Bool) (owner motive result : Term) : Term :=
  .node (.pi false) [owner, .node (.pi erased)
    [takeResultType motive, result.rename (fun x => x + 2)]]

@[simp] theorem rename_back (e : Bool) (owner motive : Term) (ρ : Nat → Nat) :
    (Term.back e owner motive).rename ρ = .back e (owner.rename ρ) (motive.rename ρ) := by
  simp only [Term.rename, renameArgs, Op.binders, liftRenaming]

@[simp] theorem subst_back (e : Bool) (owner motive : Term) (σ : Nat → Term) :
    (Term.back e owner motive).subst σ = .back e (owner.subst σ) (motive.subst σ) := by
  simp only [Term.subst, substArgs, Op.binders, liftSub]

@[simp] theorem rename_give (e : Bool) (motive owner result : Term) (ρ : Nat → Nat) :
    (Term.give e motive owner result).rename ρ =
      .give e (motive.rename ρ) (owner.rename ρ) (result.rename ρ) := by
  simp only [Term.rename, renameArgs, Op.binders, liftRenaming]

@[simp] theorem subst_give (e : Bool) (motive owner result : Term) (σ : Nat → Term) :
    (Term.give e motive owner result).subst σ =
      .give e (motive.subst σ) (owner.subst σ) (result.subst σ) := by
  simp only [Term.subst, substArgs, Op.binders, liftSub]

@[simp] theorem rename_take (value continuation : Term) (ρ : Nat → Nat) :
    (Term.take value continuation).rename ρ = .take (value.rename ρ) (continuation.rename ρ) := by
  simp only [Term.rename, renameArgs, Op.binders, liftRenaming]

@[simp] theorem subst_take (value continuation : Term) (σ : Nat → Term) :
    (Term.take value continuation).subst σ = .take (value.subst σ) (continuation.subst σ) := by
  simp only [Term.subst, substArgs, Op.binders, liftSub]

@[simp] theorem rename_takeResultType (motive : Term) (ρ : Nat → Nat) :
    (takeResultType motive).rename (liftRenaming 1 ρ) = takeResultType (motive.rename ρ) := by
  simp only [takeResultType, Term.rename, renameArgs, Op.binders, liftRenaming,
    Indexed.liftRenaming, Term.rename_comp]

@[simp] theorem subst_takeResultType (motive : Term) (σ : Nat → Term) :
    (takeResultType motive).subst (liftSub 1 σ) = takeResultType (motive.subst σ) := by
  simp only [takeResultType, Term.subst, substArgs, Op.binders, liftSub]
  rw [Term.subst_rename, Term.rename_subst]
  rfl

@[simp] theorem rename_takeBodyType (e : Bool) (owner motive result : Term) (ρ : Nat → Nat) :
    (takeBodyType e owner motive result).rename ρ =
      takeBodyType e (owner.rename ρ) (motive.rename ρ) (result.rename ρ) := by
  simp only [takeBodyType, takeResultType, Term.rename, renameArgs, Op.binders,
    liftRenaming, Indexed.liftRenaming, Term.rename_comp]

@[simp] theorem subst_takeBodyType (e : Bool) (owner motive result : Term) (σ : Nat → Term) :
    (takeBodyType e owner motive result).subst σ =
      takeBodyType e (owner.subst σ) (motive.subst σ) (result.subst σ) := by
  simp only [takeBodyType, takeResultType, Term.subst, substArgs, Op.binders, liftSub]
  rw [Term.subst_rename, Term.rename_subst, Term.subst_rename, Term.rename_subst]
  simp only [liftSubOne, Term.rename_comp]

/-- Native -2 lowering proves independence of the owner and motive result. -/
theorem take_result_reweakens
    (lowered : PartialRenaming.shift (-2) 0 result = some outside) :
    outside.rename (fun x => x + 2) = result := load_result_reweakens lowered

theorem take_result_rename (ρ : Nat → Nat)
    (lowered : PartialRenaming.shift (-2) 0 result = some outside) :
    result.rename (liftRenaming 2 ρ) = (outside.rename ρ).rename (fun x => x + 2) :=
  load_result_rename ρ lowered

theorem take_result_subst (σ : Nat → Term)
    (lowered : PartialRenaming.shift (-2) 0 result = some outside) :
    result.subst (liftSub 2 σ) = (outside.subst σ).rename (fun x => x + 2) :=
  load_result_subst σ lowered

end Jihoo.NativeKernel
