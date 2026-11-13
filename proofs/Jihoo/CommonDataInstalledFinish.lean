import Jihoo.CommonDataBranchFinish

/-! Installed, one-tick pending-shell retirement. No body compiler or global
provider is assumed. The same program and explicit continuation are retained.
The legacy certificate requires unit scratch; the live certificate permits any
old scratch value, provided all active bindings and the result exclude it. -/
namespace Jihoo.CommonDataInstalledFinish
open CommonDataBranchFinish CommonCompositionContract CommonDataTargetContext
open CommonDataReference RecursiveLexicalFields

/-- The instruction is fetched in the current function, with no call override.
The destination is a direct, in-bounds unit-typed local; the continuation exists.
No constraint is imposed on the old destination value or on shell children. -/
structure Site (p : ReferenceCalls.Program) (a : Boundary) (shell : Pending)
    (src dest continuation : Nat) : Prop where
  installed : ∃ fn, p[a.target.function]? = some fn ∧
    ReferenceCfg.fetch fn.code.base a.target.frame =
      some (.term (.free (.copy ⟨src,false⟩) ⟨dest,false⟩ continuation)) ∧
    ReferenceCalls.extension fn.code a.target.frame = none ∧
    fn.code.base.locals[dest]? = some .unit ∧ continuation < fn.code.base.blocks.size
  pointer : Local a.target.frame src (.pointer shell.target 0)
  space : dest < a.target.frame.locals.size

def stopped (a : Boundary) (shell : Pending) (dest continuation : Nat) :=
  TreeDropCall.resume a.target dest continuation
    (retired a.target.frame.heap shell.target shell.object)

/-- Build actual execution from installed instruction and pending authority. -/
theorem installed_walk (site : Site p a shell src dest continuation)
    (valid : a.Valid) (head : a.pending = shell :: tail)
    (depth : a.target.stack.length ≤ limit) :
    CommonDataCaseRelocation.walk p 1 limit a.target =
      some (stopped a shell dest continuation, [.free shell.target]) := by
  obtain ⟨fn, found, fetch, extension, ty, block⟩ := site.installed
  obtain ⟨_, obj, alive⟩ := valid.shells shell (by simp [head])
  have release : ReferenceCfg.freeHeap a.target.frame.heap shell.target 0 =
      some (retired a.target.frame.heap shell.target shell.object) :=
    ReferenceHeap.Frame.release_success_iff.mpr ⟨shell.object, obj, alive, rfl, rfl⟩
  have operand := local_operand site.pointer
  have write : ReferenceCfg.write fn.code.base
      {a.target.frame with heap := retired a.target.frame.heap shell.target shell.object}
      ⟨dest,false⟩ .unit = some
      {a.target.frame with
        heap := retired a.target.frame.heap shell.target shell.object
        locals := a.target.frame.locals.set! dest (some .unit)} := by
    simp [ReferenceCfg.write, ty, ReferenceCfg.valueType, site.space]
  have step := ReferenceCalls.Step.legacy found extension
    (ReferenceCfg.Step.free fetch operand release write block)
    (show ReferenceCalls.liftLegacy a.target
      ⟨.running (ReferenceCfg.jump
        {a.target.frame with
          heap := retired a.target.frame.heap shell.target shell.object
          locals := a.target.frame.locals.set! dest (some .unit)} continuation),
        [.free shell.target]⟩ =
      some ⟨.running (stopped a shell dest continuation), [.free shell.target]⟩ from rfl)
  have tick := ReferenceCalls.tick_complete step
  simp [CommonDataCaseRelocation.walk, ReferenceCalls.stackDepth, depth,
    Nat.not_lt.mpr depth, tick, stopped, TreeDropCall.resume]

/-- The original certificate is constructed, never assumed. -/
theorem installed_execution (site : Site p a shell src dest continuation)
    (valid : a.Valid) (head : a.pending = shell :: tail)
    (depth : a.target.stack.length ≤ limit)
    (unit : a.target.frame.locals[dest]? = some (some .unit)) :
    FinishExecution p limit 1 a shell (stopped a shell dest continuation) := by
  refine ⟨installed_walk site valid head depth, rfl, ?_, rfl⟩
  change a.target.frame.locals.set! dest (some .unit) = a.target.frame.locals
  apply Array.ext_getElem?
  intro i
  by_cases eq : i = dest
  · subst i
    simpa [Array.set!, Array.getElem?_setIfInBounds, site.space] using unit.symm
  · simp [Array.set!, Ne.symm eq]

/-- Weaker local condition sufficient for the frozen FinishResult interface. -/
structure LiveFinishExecution (p : ReferenceCalls.Program) (limit ticks : Nat)
    (a : Boundary) (shell : Pending) (machine : ReferenceCalls.State)
    (resultSlot : Nat) : Prop where
  run : CommonDataCaseRelocation.walk p ticks limit a.target =
    some (machine, [.free shell.target])
  heap : machine.frame.heap = retired a.target.frame.heap shell.target shell.object
  live : ∀ (k : Nat) e (slot : Nat), a.ctx[k]? = some e → a.slots[k]? = some slot → Active e →
    machine.frame.locals[slot]? = a.target.frame.locals[slot]?
  result : machine.frame.locals[resultSlot]? = a.target.frame.locals[resultSlot]?
  callers : machine.stack = a.target.stack

theorem installed_live_execution (site : Site p a shell src dest continuation)
    (valid : a.Valid) (head : a.pending = shell :: tail)
    (depth : a.target.stack.length ≤ limit)
    (reserved : CommonDataCaseEntryContext.Reserved a.ctx a.slots [dest])
    (resultApart : resultSlot ≠ dest) :
    LiveFinishExecution p limit 1 a shell (stopped a shell dest continuation) resultSlot := by
  refine ⟨installed_walk site valid head depth, rfl, ?_,
    TreeDropCall.resume_local resultApart, rfl⟩
  intro k e slot he hs active
  apply TreeDropCall.resume_local
  simpa using reserved k e slot he hs active

/-- Reuse shell retirement on a frame with old locals, then transport only live
bindings. Resources, Buffer lengths/payloads and pending parents are unchanged. -/
theorem live_finish_context (valid : a.Valid) (head : a.pending = shell :: tail)
    (exec : LiveFinishExecution p limit ticks a shell machine resultSlot) :
    (finished a shell tail machine).Valid := by
  let shadow : ReferenceCalls.State :=
    {machine with frame := {machine.frame with locals := a.target.frame.locals}}
  have old := finish_context valid head (machine := shadow) exec.heap rfl
  have bindings := CommonDataCaseEntryContext.Bindings.reframe old.bindings
    (g := machine.frame) exec.live
  exact ⟨CommonDataCaseEntryContext.Context.reframe old.toContext rfl bindings,
    old.bufferSizes⟩

theorem live_finish_result (valid : a.Valid) (head : a.pending = shell :: tail)
    (post : CommonData.Post kind a.source v (a.pending.map Pending.source ++ a.sf))
    (exec : LiveFinishExecution p limit ticks a shell machine resultSlot) :
    FinishResult p limit ticks a (finished a shell tail machine) shell tail kind v resultSlot := by
  exact ⟨exec.result, head, rfl, rfl, rfl, rfl, rfl, ⟨rfl,rfl,rfl⟩,
    ⟨exec.run, fun h => live_finish_context h head exec, exec.callers, rfl, rfl⟩,
    (finish_authority valid head post).2.1⟩

/-- The body result survives even when its slot is not in the lexical map. -/
theorem live_result_preserved
    (body : BodyResult g term kind p limit n a b v se te resultSlot)
    (exec : LiveFinishExecution p limit m b shell machine resultSlot) :
    match v with
    | .scalar n => Local machine.frame resultSlot (.i64 n)
    | .data ref => ∃ image ∈ (finished b shell tail machine).images,
        RecursiveFieldRuntime.root image.source = ref ∧
          Local machine.frame resultSlot (.pointer image.target 0)
    | _ => False := by
  have result := body.result
  cases v with
  | scalar n => exact exec.result.trans result
  | data ref =>
    obtain ⟨image, member, root, loc⟩ := result
    exact ⟨image, member, root, exec.result.trans loc⟩
  | _ => exact result

/-- An actual installed free composes with the body in its same program. -/
theorem installed_body_finish (valid : a.Valid)
    (body : BodyResult g term kind p limit n a b v se te resultSlot)
    (head : b.pending = shell :: tail) (site : Site p b shell src dest continuation)
    (depth : b.target.stack.length ≤ limit)
    (reserved : CommonDataCaseEntryContext.Reserved b.ctx b.slots [dest])
    (resultApart : resultSlot ≠ dest) :
    Transfer p limit (n+1) a (finished b shell tail (stopped b shell dest continuation))
      (te ++ [.free shell.target]) ∧
    FinishResult p limit 1 b (finished b shell tail (stopped b shell dest continuation))
      shell tail kind v resultSlot := by
  have fin := live_finish_result (body.transfer.context valid) head body.post
    (installed_live_execution site (body.transfer.context valid) head depth reserved resultApart)
  exact ⟨body.transfer.then fin.transfer, fin⟩
end Jihoo.CommonDataInstalledFinish
