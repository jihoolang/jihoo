import Jihoo.CommonDataCaseRelocatedContext
import Jihoo.CommonDataCaseEntryContextChecks

namespace Jihoo.CommonDataCaseRelocatedContext.Checks
open CommonCompositionContract CommonDataTargetContext CommonDataCaseCfg
open CommonDataReference RecursiveLexicalFields CommonDataCaseEntryContext
open CommonDataReferenceChecks (image source)
open CommonDataTargetContext.Checks (heap ctx env)
open CommonDataCaseEntryContext.Checks

def slots : List Nat := [11,11,7,8,9,10]
def locals : Array (Option ReferenceCfg.Value) :=
  Fixture.locals.push (some (.pointer 3 0))
def before : Boundary :=
  ⟨[image, .nil 4], [(4,0)], [2], [], [], [10], ctx, env, slots, source,
    stateAt heap locals 8 Fixture.stack⟩
def input : CaseInput :=
  { before := before, pre := #[CommonDataCaseCfg.Checks.stop, CommonDataCaseCfg.Checks.stop]
    post := #[CommonDataCaseCfg.Checks.stop]
    nilBody := CommonDataCaseCfg.Checks.stop, nodeBody := CommonDataCaseCfg.Checks.stop
    index := 1, src := 11, ghostSlots := [99]
    selected := rfl, slot := rfl, pc := rfl, space := by decide }

theorem valid : before.Valid := by
  have old := Fixture.initial
  refine ⟨⟨old.valid, old.agreement, ?_, old.resources, old.owned, old.separated, old.shells⟩,
    old.bufferSizes⟩
  exact .cons ⟨_, rfl, rfl⟩ (.cons ⟨_, rfl, rfl⟩
    (.cons ⟨_, rfl, rfl⟩ (.cons ⟨_, _, rfl, rfl⟩ (.cons ⟨_, rfl⟩ (.cons rfl .nil)))))

theorem reserved : Reserved before.ctx before.slots [0,1,2,3,4,5] := by
  intro k e sl _ hs _
  have member := List.mem_of_getElem? hs
  simp [before, slots] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Nonzero placement, selected alias at lexical index one/local eleven,
retained Buffer/scalar/natural, arbitrary ghost local, suspended caller. -/
theorem node_transfer : Transfer input.program 1 11 before
    (input.nodeOut 7 3 (.nil 1) (.nil 2) [.nil 4]) [] :=
  (entryProvider.node input 7 3 (.nil 1) (.nil 2) [.nil 4] 1 valid rfl reserved (by decide)).2

theorem node_valid : (input.nodeOut 7 3 (.nil 1) (.nil 2) [.nil 4]).Valid :=
  node_transfer.context valid

/-- A second relocated Case consumes a child while retaining its pending
parent, the other child, aliases already retired, and the same live frame. -/
def nilBefore : Boundary :=
  { input.nodeOut 7 3 (.nil 1) (.nil 2) [.nil 4] with
    target := stateAt heap (nodeLocals (locals.set! 0 (some (.pointer 3 0))) 3 1 2)
      7 Fixture.stack }
def nilInput : CaseInput :=
  { before := nilBefore, pre := #[CommonDataCaseCfg.Checks.stop]
    post := #[], nilBody := CommonDataCaseCfg.Checks.stop, nodeBody := CommonDataCaseCfg.Checks.stop
    index := 1, src := 4, ghostSlots := []
    selected := rfl, slot := rfl, pc := rfl, space := by decide }

theorem nil_valid : nilBefore.Valid := by
  have h := node_valid
  exact ⟨Context.reframe h.toContext rfl
    (Bindings.reframe h.bindings (by intros; rfl)), h.bufferSizes⟩

theorem nil_reserved : Reserved (CommonData.removeHead nilBefore.ctx)
    nilBefore.slots [0,1,6] := by
  intro k e sl _ hs _
  have member := List.mem_of_getElem? hs
  simp [nilBefore, CaseInput.nodeOut, input, before, slots] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem nil_transfer : Transfer nilInput.program 1 5 nilBefore
    (nilInput.nilOut 1 [.nil 2, .nil 4]) [.free 1] :=
  (entryProvider.nil nilInput 1 [.nil 2, .nil 4] 1 nil_valid rfl nil_reserved (by decide)).2

theorem nil_output_valid : (nilInput.nilOut 1 [.nil 2, .nil 4]).Valid :=
  nil_transfer.context nil_valid

theorem node_zero_rejected : ¬ Reserved [.data 0] [0] [0,1,2,3,4,5] := by
  intro h
  exact h 0 (.data 0) 0 rfl rfl trivial (by simp)

#print axioms Jihoo.CommonDataCaseRelocatedContext.node
#print axioms Jihoo.CommonDataCaseRelocatedContext.nil
#print axioms Jihoo.CommonDataCaseRelocatedContext.entryProvider
#print axioms node_transfer
#print axioms node_valid
#print axioms nil_transfer
#print axioms nil_output_valid
#print axioms node_zero_rejected
end Jihoo.CommonDataCaseRelocatedContext.Checks
