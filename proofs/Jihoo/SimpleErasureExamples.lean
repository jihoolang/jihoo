import Jihoo.TypingSimpleErasure

namespace Jihoo.CoreBridge.Raw.Beta.SimpleErasure.Examples

private def expanded : Raw := .app (.lam false .u64 .u64) (.natural 0)
private theorem expansion : Conv expanded .u64 := by
  simpa [expanded, Raw.subst] using Conv.beta false .u64 .u64 (.natural 0)

theorem expanded_no_shape : ¬ Shape expanded a := by intro h; cases h

theorem expanded_arity : Arity expanded .base := Shape.u64.arity.conversion expansion.symm

theorem expanded_result_erasure : Typed (fun _ => none) (erase (.natural 7)) .base := by
  have ht : HasType (fun _ => none) (.natural 7) expanded :=
    .convert (.natural (by decide)) expansion.symm
  exact typed_at_arity ht (fun _ _ hx => by cases hx) expanded_arity

private def size : Ty → Nat
  | .base => 1
  | .arrow a b => size a + size b + 1

private theorem no_recursive_arrow (h : a = Ty.arrow a b) : False := by
  have hs := congrArg size h
  simp only [size] at hs
  omega

theorem self_application_not_typed : ¬ Typed Δ (.app (.var x) (.var x)) a := by
  intro h
  cases h with
  | app hf hx =>
      cases hf with
      | var hf =>
          cases hx with
          | var hx =>
              exact no_recursive_arrow (Option.some.inj (hx.symm.trans hf))

private theorem delta_not_typed : ¬ Typed Δ (.lam (.app (.var 0) (.var 0))) a := by
  intro h
  cases h with
  | lam hb => exact self_application_not_typed hb

private def delta : Raw := .lam false .u64 (.app (.var 0) (.var 0))

theorem closed_omega_not_typed : ¬ HasType (fun _ => none) (.app delta delta) A := by
  intro h
  obtain ⟨_, _, ht⟩ := closed_erasure h
  cases ht with
  | app hf _ => exact delta_not_typed hf

theorem capture_avoiding_erasure :
    erase ((Raw.lam false .u64 (.app (.var 1) (.var 0))).subst (Raw.single (.var 2))) =
      .lam (.app (.var 3) (.var 0)) := by
  simp [Raw.subst, Raw.single, Raw.liftSub, Raw.rename, erase]

theorem higher_order_erasure :
    Typed (fun _ => none)
      (erase (.lam false (.pi false .u64 .u64) (.app (.var 0) (.natural 7))))
      (.arrow (.arrow .base .base) .base) := by
  have ht : HasType (fun _ => none)
      (.lam false (.pi false .u64 .u64) (.app (.var 0) (.natural 7)))
      (.pi false (.pi false .u64 .u64) .u64) := by
    apply HasType.lam (.pi .u64 rfl .u64) rfl
    have hf : HasType (Raw.Context.extend (fun _ => none) (.pi false .u64 .u64)) (.var 0)
        (.pi false .u64 .u64) := .var (by simp [Raw.Context.extend, Raw.rename])
    simpa [Raw.subst, Raw.proposition] using HasType.app hf (HasType.natural (by decide) (n := 7))
  exact typed_at_arity ht (fun _ _ hx => by cases hx)
    (Shape.pi (Shape.pi .u64 .u64) .u64).arity

/-- A contextual beta step under Refl disappears. One-step simulation is
intentionally restricted to the function spine. -/
theorem erased_context_is_not_simple_step :
    ¬ SimpleStep (erase (.refl (.app (.lam false .u64 (.var 0)) (.natural 7))))
      (erase (.refl (.natural 7))) := by intro h; cases h

/-- The simple base type carries no arithmetic truth or array-length meaning. -/
theorem different_literals_same_erasure : erase (.natural 0) = erase (.natural 1) := rfl

end Jihoo.CoreBridge.Raw.Beta.SimpleErasure.Examples
