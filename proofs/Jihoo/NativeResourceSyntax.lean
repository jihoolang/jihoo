import Jihoo.NativePartialRenaming

/-! Syntax and binding algebra for the native buffer fragment. Continuations
carry explicit lambdas; Load introduces no hidden binders on its child edges.
These definitions neither assert typing nor authorize runtime ownership. -/
namespace Jihoo.NativeKernel

namespace Term
@[match_pattern] abbrev buffer (n : Term) : Term := .node .buffer [n]
@[match_pattern] abbrev alloc (n x : Term) : Term := .node .alloc [n, x]
@[match_pattern] abbrev store (b i v p : Term) : Term := .node .store [b, i, v, p]
@[match_pattern] abbrev load (b i p k : Term) : Term := .node .load [b, i, p, k]
@[match_pattern] abbrev free (b rest : Term) : Term := .node .free [b, rest]
@[match_pattern] abbrev ref (t : Term) : Term := .node .ref [t]
@[match_pattern] abbrev borrow (b : Term) : Term := .node .borrow [b]
@[match_pattern] abbrev deref (r : Term) : Term := .node .deref [r]
end Term

/-- Exact Core.infer Load telescope: x:I64, then the same buffer weakened
beneath x, then a result independent of both continuation arguments. -/
def loadBodyType (n result : Term) : Term :=
  .node (.pi false) [.node .i64 [], .node (.pi false)
    [.buffer (n.rename Nat.succ), result.rename (fun x => x + 2)]]

@[simp] theorem rename_buffer (n : Term) (ρ : Nat → Nat) :
    (Term.buffer n).rename ρ = .buffer (n.rename ρ) := by
  simp only [Term.rename, renameArgs, Op.binders, liftRenaming]

@[simp] theorem subst_buffer (n : Term) (σ : Nat → Term) :
    (Term.buffer n).subst σ = .buffer (n.subst σ) := by
  simp only [Term.subst, substArgs, Op.binders, liftSub]

@[simp] theorem rename_ref (n : Term) (ρ : Nat → Nat) :
    (Term.ref n).rename ρ = .ref (n.rename ρ) := by
  simp only [Term.rename, renameArgs, Op.binders, liftRenaming]

@[simp] theorem subst_ref (n : Term) (σ : Nat → Term) :
    (Term.ref n).subst σ = .ref (n.subst σ) := by
  simp only [Term.subst, substArgs, Op.binders, liftSub]

@[simp] theorem rename_alloc (n x : Term) (ρ : Nat → Nat) :
    (Term.alloc n x).rename ρ =
      .alloc (n.rename ρ) (x.rename ρ) := by
  simp only [Term.rename, renameArgs, Op.binders, liftRenaming]

@[simp] theorem subst_alloc (n x : Term) (σ : Nat → Term) :
    (Term.alloc n x).subst σ =
      .alloc (n.subst σ) (x.subst σ) := by
  simp only [Term.subst, substArgs, Op.binders, liftSub]

@[simp] theorem rename_store (b i v p : Term) (ρ : Nat → Nat) :
    (Term.store b i v p).rename ρ =
      .store (b.rename ρ) (i.rename ρ) (v.rename ρ) (p.rename ρ) := by
  simp only [Term.rename, renameArgs, Op.binders, liftRenaming]

@[simp] theorem subst_store (b i v p : Term) (σ : Nat → Term) :
    (Term.store b i v p).subst σ =
      .store (b.subst σ) (i.subst σ) (v.subst σ) (p.subst σ) := by
  simp only [Term.subst, substArgs, Op.binders, liftSub]

@[simp] theorem rename_free (b rest : Term) (ρ : Nat → Nat) :
    (Term.free b rest).rename ρ =
      .free (b.rename ρ) (rest.rename ρ) := by
  simp only [Term.rename, renameArgs, Op.binders, liftRenaming]

@[simp] theorem subst_free (b rest : Term) (σ : Nat → Term) :
    (Term.free b rest).subst σ =
      .free (b.subst σ) (rest.subst σ) := by
  simp only [Term.subst, substArgs, Op.binders, liftSub]

@[simp] theorem rename_borrow (b : Term) (ρ : Nat → Nat) :
    (Term.borrow b).rename ρ =
      .borrow (b.rename ρ) := by
  simp only [Term.rename, renameArgs, Op.binders, liftRenaming]

@[simp] theorem subst_borrow (b : Term) (σ : Nat → Term) :
    (Term.borrow b).subst σ =
      .borrow (b.subst σ) := by
  simp only [Term.subst, substArgs, Op.binders, liftSub]

@[simp] theorem rename_deref (r : Term) (ρ : Nat → Nat) :
    (Term.deref r).rename ρ =
      .deref (r.rename ρ) := by
  simp only [Term.rename, renameArgs, Op.binders, liftRenaming]

@[simp] theorem subst_deref (r : Term) (σ : Nat → Term) :
    (Term.deref r).subst σ =
      .deref (r.subst σ) := by
  simp only [Term.subst, substArgs, Op.binders, liftSub]

/-- The continuation is renamed as an ordinary child, relying on its explicit
Pi/Lam nodes for both local binders. -/
@[simp] theorem rename_load (b i p k : Term) (ρ : Nat → Nat) :
    (Term.load b i p k).rename ρ =
      .load (b.rename ρ) (i.rename ρ) (p.rename ρ) (k.rename ρ) := by
  simp only [Term.rename, renameArgs, Op.binders, liftRenaming]

@[simp] theorem subst_load (b i p k : Term) (σ : Nat → Term) :
    (Term.load b i p k).subst σ =
      .load (b.subst σ) (i.subst σ) (p.subst σ) (k.subst σ) := by
  simp only [Term.subst, substArgs, Op.binders, liftSub]

@[simp] theorem rename_loadBodyType (n result : Term) (ρ : Nat → Nat) :
    (loadBodyType n result).rename ρ = loadBodyType (n.rename ρ) (result.rename ρ) := by
  simp only [loadBodyType, Term.rename, renameArgs, Op.binders, liftRenaming,
    Indexed.liftRenaming, Term.rename_comp]

@[simp] theorem subst_loadBodyType (n result : Term) (σ : Nat → Term) :
    (loadBodyType n result).subst σ = loadBodyType (n.subst σ) (result.subst σ) := by
  simp only [loadBodyType, Term.subst, substArgs, Op.binders, liftSub]
  rw [Term.subst_rename, Term.rename_subst, Term.subst_rename, Term.rename_subst]
  simp only [liftSubOne, Term.rename_comp]

/-- Native's signed -2 shift rejects either local continuation variable. -/
theorem load_result_reweakens
    (lowered : PartialRenaming.shift (-2) 0 result = some outside) :
    outside.rename (fun x => x + 2) = result := by
  have restored := PartialRenaming.shift_negative_reweakens (by decide : (-2 : Int) < 0) lowered
  change outside.rename (PartialRenaming.raiseIndex 0 2) = result at restored
  have index : PartialRenaming.raiseIndex 0 2 = (fun x => x + 2) := by
    funext x
    simp [PartialRenaming.raiseIndex]
  rwa [index] at restored

/-- Lowered continuation results remain independent of both local arguments
when the surrounding context is renamed. -/
theorem load_result_rename (ρ : Nat → Nat)
    (lowered : PartialRenaming.shift (-2) 0 result = some outside) :
    result.rename (liftRenaming 2 ρ) = (outside.rename ρ).rename (fun x => x + 2) := by
  rw [← load_result_reweakens lowered, Term.rename_comp, Term.rename_comp]
  rfl

/-- Simultaneous outer substitution acts below the exact two continuation
binders and preserves the result's independence from them. -/
theorem load_result_subst (σ : Nat → Term)
    (lowered : PartialRenaming.shift (-2) 0 result = some outside) :
    result.subst (liftSub 2 σ) = (outside.subst σ).rename (fun x => x + 2) := by
  rw [← load_result_reweakens lowered, Term.subst_rename, Term.rename_subst]
  congr 1
  funext x
  simp only [liftSub, liftSubOne, Term.rename_comp]

theorem load_result_scoped (scope : result.Scoped (depth + 2))
    (lowered : PartialRenaming.shift (-2) 0 result = some outside) : outside.Scoped depth := by
  exact PartialRenaming.shift_negative_scoped (by decide : (-2 : Int) < 0) scope
    (Nat.zero_le _) lowered

theorem load_result_wellFormed (formed : result.WellFormed)
    (lowered : PartialRenaming.shift (-2) 0 result = some outside) : outside.WellFormed :=
  PartialRenaming.shift_wellFormed formed lowered

@[simp] theorem load_result_rejects_inner :
    PartialRenaming.shift (-2) 0 (.var 0) = none := by
  simp [PartialRenaming.shift, PartialRenaming.lower, PartialRenaming.rename?, PartialRenaming.lowerIndex]

@[simp] theorem load_result_rejects_outer :
    PartialRenaming.shift (-2) 0 (.var 1) = none := by
  simp [PartialRenaming.shift, PartialRenaming.lower, PartialRenaming.rename?, PartialRenaming.lowerIndex]

end Jihoo.NativeKernel
