import Jihoo.CommonDataCaseRelocatedContext
import Jihoo.CommonDataBranchFinish
import Jihoo.CommonDataCaseRegisterSafety

/-! The implemented entry provider composes with conditional body/finish
certificates, in one installed program and under a covered safe register layout.
This is not a body compiler or a general register-renaming theorem. -/
namespace Jihoo.CommonCaseIntegration
open CommonCompositionContract CommonDataCaseRegisterSafety CommonDataBranchFinish

/-- Discharge entry and its register reservation; body and finish execution
remain explicit inputs in the very same program. -/
theorem node_finish (i : CaseInput) x j l r rest limit
    (valid : i.before.Valid) (shape : i.before.images = .node x j l r :: rest)
    (layout : RestrictedPlacement i.program ⟨i.nilBody, i.nodeBody, i.src⟩
      .node i.before.ctx i.before.slots)
    (bound : i.before.target.stack.length ≤ limit)
    (body : BodyResult g term kind i.program limit n
      (i.nodeOut x j l r rest) c v se te slot)
    (head : c.pending = shell :: tail)
    (exec : FinishExecution i.program limit m c shell machine) :
    Transfer i.program limit (11+n+m) i.before
      (finished c shell tail machine) (te ++ [.free shell.target]) ∧
    FinishResult i.program limit m c (finished c shell tail machine)
      shell tail kind v slot := by
  have entry := (CommonDataCaseRelocatedContext.entryProvider.node
    i x j l r rest limit valid shape layout.reserved bound).2
  have fin := finish_result (body.transfer.context (entry.context valid)) head body.post exec (slot := slot)
  exact ⟨CommonCompositionContract.node_pipeline entry body fin, fin⟩

/-- Nil consumes the boxed object under the surviving-context reservation. -/
theorem nil_entry (i : CaseInput) j rest limit
    (valid : i.before.Valid) (shape : i.before.images = .nil j :: rest)
    (layout : RestrictedPlacement i.program ⟨i.nilBody, i.nodeBody, i.src⟩
      .nil (CommonData.removeHead i.before.ctx) i.before.slots)
    (bound : i.before.target.stack.length ≤ limit) :
    Transfer i.program limit 5 i.before (i.nilOut j rest) [.free j] :=
  (CommonDataCaseRelocatedContext.entryProvider.nil
    i j rest limit valid shape layout.reserved bound).2
end Jihoo.CommonCaseIntegration
