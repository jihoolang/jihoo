import Jihoo.NativeContextQuantity

namespace Jihoo.NativeKernel.Environment.ContextQuantity
open Jihoo.Quantity NativeQuantity ContextModes CallReplay
variable {control : Control}

 theorem project_origin (h : project fuel env ctx term = some control) :
    projectRaw fuel env ctx term = some control ∧ scopeCheck ctx.length control = true := by
  unfold project at h
  obtain ⟨candidate, raw, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i accepted
    cases h
    exact ⟨raw,accepted⟩
  · contradiction

private theorem app_step : projectRaw (fuel + 1) env ctx (.app function argument) = (do
    let (head, supplied) ← splitSpine fuel (.app function argument) []
    let (entries, result) ← CallReplay.checked fuel env ctx false head supplied
    if !partialOK fuel env ctx entries result then none else
    let opened ← openHead fuel env ctx head supplied
    let runtime ← (runtimeArguments entries).mapM (projectRaw fuel env ctx)
    let body ← projectRaw fuel env opened.context opened.body
    pure (if opened.modes.isEmpty then callControl body runtime
      else .seq (sequence runtime) (.scopes opened.modes body))) := by
  simp [projectRaw, Op.arity]

 theorem app_origin (h : projectRaw (fuel + 1) env ctx (.app function argument) = some control) :
    ∃ head supplied entries result opened runtime body,
      splitSpine fuel (.app function argument) [] = some (head,supplied) ∧
      CallReplay.checked fuel env ctx false head supplied = some (entries,result) ∧
      partialOK fuel env ctx entries result = true ∧
      openHead fuel env ctx head supplied = some opened ∧
      (runtimeArguments entries).mapM (projectRaw fuel env ctx) = some runtime ∧
      projectRaw fuel env opened.context opened.body = some body ∧
      control = (if opened.modes.isEmpty then callControl body runtime
        else .seq (sequence runtime) (.scopes opened.modes body)) := by
  rw [app_step] at h
  obtain ⟨⟨head,supplied⟩,split,h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨⟨entries,result⟩,replayed,h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · contradiction
  · rename_i allowed
    have partialGuard : partialOK fuel env ctx entries result = true := by
      cases resultFlag : partialOK fuel env ctx entries result <;> simp_all
    obtain ⟨opened,openedHead,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨runtime,arguments,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨body,projected,same⟩ := Option.bind_eq_some_iff.mp h
    cases same
    exact ⟨head,supplied,entries,result,opened,runtime,body,split,replayed,partialGuard,
      openedHead,arguments,projected,rfl⟩

/-- Every emitted call has a genuine same-checker signature replay and the
native owner/partialGuard-function boundary. The runtime callee is not normalized. -/
theorem app_authenticated (h : projectRaw (fuel + 1) env ctx (.app function argument) = some control) :
    ∃ head supplied entries result signature,
      splitSpine fuel (.app function argument) [] = some (head,supplied) ∧
      CodeKinds.ContextFormed env ctx ∧ HasType env ctx false head signature ∧
      CallReplay.Steps env ctx false signature supplied entries result ∧
      HasType env ctx false (applications head supplied) result ∧
      (entries.any (ownsArgument env) = false ∨ ResultShape env ctx result) := by
  obtain ⟨head,supplied,entries,result,opened,runtime,body,split,replayed,partialGuard,_⟩ := app_origin h
  obtain ⟨signature,typed,trace,applied⟩ := CallReplay.infer_sound (CallReplay.checked_origin replayed).2
  exact ⟨head,supplied,entries,result,signature,split,CodeKinds.contextOK_sound (CallReplay.checked_origin replayed).1,typed,trace,applied,partialOK_sound partialGuard⟩

private theorem lam_step : projectRaw (fuel + 1) env ctx (.lam erased domain term) = (do
    if !CodeKinds.contextOK fuel env ctx || !(Checker.binder fuel env ctx erased domain).isSome then none else
    let mode ← resolve fuel env ctx erased domain
    let body ← projectRaw fuel env (⟨domain,erased⟩ :: ctx) term
    pure (.closure (.scope mode (functionTail term body)))) := by
  simp [projectRaw, Op.arity]

 theorem lam_origin (h : projectRaw (fuel + 1) env ctx (.lam erased domain term) = some control) :
    ∃ mode body sort,
      CodeKinds.ContextFormed env ctx ∧ Binder env ctx erased domain sort ∧ Resolved env ctx erased domain mode ∧
      projectRaw fuel env (⟨domain,erased⟩ :: ctx) term = some body ∧
      control = .closure (.scope mode (functionTail term body)) := by
  rw [lam_step] at h
  split at h
  · contradiction
  · rename_i isBinder
    have contextGate : CodeKinds.contextOK fuel env ctx = true := by
      cases found : CodeKinds.contextOK fuel env ctx <;> simp_all
    have someBinder : (Checker.binder fuel env ctx erased domain).isSome = true := by
      cases found : Checker.binder fuel env ctx erased domain <;> simp_all
    obtain ⟨mode,resolved,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨body,projected,same⟩ := Option.bind_eq_some_iff.mp h
    cases same
    cases binder : Checker.binder fuel env ctx erased domain with
    | none => simp [binder] at someBinder
    | some sort => exact ⟨mode,body,sort,CodeKinds.contextOK_sound contextGate,Checker.binder_sound binder,resolve_sound resolved,projected,rfl⟩

end Jihoo.NativeKernel.Environment.ContextQuantity
