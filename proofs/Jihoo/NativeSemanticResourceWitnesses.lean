import Jihoo.NativeAtomicRealization

/-! Logical inhabitation witnesses for effectful syntax. Load's result is
independent of both continuation binders, so any typed I64 sample and the typed
owner produce the same result type. This is not an execution/refinement claim. -/
namespace Jihoo.NativeKernel.Environment.Semantics
open Jihoo.NativeKernel.Environment.Conversion

theorem instantiate_two_raised (term first second : Term) :
    ((term.rename (fun x => x + 2)).subst (liftSub 1 (single first))).subst (single second) = term := by
  rw [Term.subst_rename,Term.subst_comp]
  have variables : (fun x => (liftSub 1 (single first) (x + 2)).subst (single second)) = Term.var := by
    funext x
    simp only [liftSub,liftSubOne,NativeKernel.single,Term.rename,Term.subst]
  rw [variables]
  exact Term.subst_id term

theorem load_logical_witness
    (closed : Conversion.Closed env)
    (buffer : HasType env ctx mode owner (.buffer count))
    (continuation : HasType env ctx mode function (.pi false valueDomain (.pi false ownerDomain result)))
    (valueDomainConv : Conv env valueDomain .i64)
    (ownerDomainConv : Conv env ownerDomain (.buffer (count.rename Nat.succ)))
    (resultConv : Conv env result normal)
    (lowered : PartialRenaming.shift (-2) 0 normal = some outside) :
    HasType env ctx true (.app (.app function (.integer 0)) owner) outside := by
  let sample : Term := .integer 0
  have sampleTyped : HasType env ctx true sample valueDomain :=
    (HasType.integer (by decide) (by decide)).convert (.symm valueDomainConv)
  have first : HasType env ctx true (.app function sample)
      (.pi false (ownerDomain.subst (single sample)) (result.subst (liftSub 1 (single sample)))) := by
    have applied : HasType env ctx true (.app function sample)
        ((Term.pi false ownerDomain result).subst (single sample)) :=
      HasType.app continuation.ghost sampleTyped (Or.inl rfl)
    simpa only [Term.pi,Term.subst,substArgs,Op.binders,liftSub] using applied
  have ownerConverted := ownerDomainConv.substitution (single sample) closed
  rw [subst_buffer,Term.shift_subst_single] at ownerConverted
  have second := HasType.app first (buffer.ghost.convert (.symm ownerConverted)) (Or.inl rfl)
  have converted := (resultConv.substitution (liftSub 1 (single sample)) closed).substitution (single owner) closed
  rw [←load_result_reweakens lowered,instantiate_two_raised] at converted
  exact second.convert converted

end Jihoo.NativeKernel.Environment.Semantics
