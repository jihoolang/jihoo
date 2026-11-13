import Jihoo.CommonDataInstalledFinish
import Jihoo.CommonDataCaseEntryContextChecks

namespace Jihoo.CommonDataInstalledFinishChecks
open CommonDataInstalledFinish CommonDataBranchFinish CommonCompositionContract
open CommonDataTargetContext CommonDataReference RecursiveLexicalFields
open CommonDataReferenceChecks (image source)
open CommonDataTargetContext.Checks (heap ctx env)
open CommonDataCaseEntryContext.Checks.Fixture (slots locals stack)

def shell : Pending := ⟨7,3,image.object⟩
def before (scratch : ReferenceCfg.Value) : Boundary :=
  { images := [.nil 2, .nil 4], buffers := [(4,0)], sizes := [2]
    pending := [shell], sf := [], tf := [10]
    ctx := CommonData.removeHead (bindContext 1 ctx)
    env := bindValues 1 ⟨none,none⟩ env
    slots := 5 :: 4 :: 99 :: slots
    source := source
    target := ⟨0, ⟨0,0,(CommonDataCaseCfg.nodeLocals locals 3 1 2).set! 6 (some scratch),
      retired heap 1 ReferenceHeap.nilObject⟩, stack⟩ }

def fn : ReferenceCalls.Function :=
  ⟨⟨⟨#[.ptr,.u64,.ptr,.ptr,.ptr,.ptr,.unit,.ptr,.ptr,.i64,.u64],
    #[⟨#[],.free (.copy ⟨0,false⟩) ⟨6,false⟩ 1⟩, ⟨#[],.goto 1⟩]⟩, #[]⟩, #[]⟩
def program : ReferenceCalls.Program := #[fn]
def after (scratch : ReferenceCfg.Value) := stopped (before scratch) shell 6 1

theorem valid (scratch : ReferenceCfg.Value) : (before scratch).Valid := by
  have old := CommonDataCaseEntryContext.Checks.Fixture.pending_after_child
  refine ⟨CommonDataCaseEntryContext.Context.reframe old.toContext rfl ?_, old.bufferSizes⟩
  apply CommonDataCaseEntryContext.Bindings.reframe old.bindings
  intro k e slot he hs active
  have member := List.mem_of_getElem? hs
  change slot ∈ 5 :: 4 :: 99 :: slots at member
  simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem site (scratch : ReferenceCfg.Value) : Site program (before scratch) shell 0 6 1 := by
  refine ⟨⟨fn, rfl, ?_, ?_, rfl, by decide⟩, ?_, by change 6 < 11; decide⟩ <;> rfl

theorem reserved (scratch : ReferenceCfg.Value) :
    CommonDataCaseEntryContext.Reserved (before scratch).ctx (before scratch).slots [6] := by
  intro k e slot he hs active
  have member := List.mem_of_getElem? hs
  change slot ∈ 5 :: 4 :: 99 :: slots at member
  simp [slots] at member
  simp only [List.mem_singleton]
  omega

/-- Closed inhabitant of the original contract, with a stale child and Buffer frame. -/
theorem unit_execution : FinishExecution program 1 1 (before .unit) shell (after .unit) :=
  installed_execution (site .unit) (valid .unit) rfl (by decide) rfl

/-- Any old scratch value works for live preservation, including i64 in a unit slot. -/
theorem live_execution (scratch : ReferenceCfg.Value) :
    LiveFinishExecution program 1 1 (before scratch) shell (after scratch) 5 :=
  installed_live_execution (site scratch) (valid scratch) rfl (by change 1 ≤ 1; decide)
    (reserved scratch) (by decide)

theorem final_valid (scratch : ReferenceCfg.Value) :
    (finished (before scratch) shell [] (after scratch)).Valid :=
  live_finish_context (valid scratch) rfl (live_execution scratch)

theorem result_post (scratch : ReferenceCfg.Value) :
    CommonData.Post .data (before scratch).source (.data none)
      ((before scratch).pending.map Pending.source ++ (before scratch).sf) := by
  refine ⟨RecursiveFieldOwnership.Tree.empty, rfl, trivial, ?_⟩
  refine ⟨by change ([7] : List Nat).Nodup; decide, ?_, ?_⟩
  · intro x hx
    change x ∈ [7] at hx
    have eq : x = 7 := by simpa using hx
    subst x
    rfl
  · intro x hx l
    simp [before, source]

theorem concrete_finish_result (scratch : ReferenceCfg.Value) :
    FinishResult program 1 1 (before scratch)
      (finished (before scratch) shell [] (after scratch)) shell [] .data (.data none) 5 :=
  live_finish_result (valid scratch) rfl (result_post scratch) (live_execution scratch)

-- Independent reduction checks: free event, continuation, caller and live result.
example : CommonDataCaseRelocation.walk program 1 1 (before (.i64 123)).target =
    some (after (.i64 123), [.free 3]) := by decide
example : (after (.i64 123)).frame.block = 1 ∧ (after (.i64 123)).frame.index = 0 := by decide
example : (after (.i64 123)).stack = stack := rfl
example : (before (.i64 123)).target.frame.locals[6]? = some (some (.i64 123)) ∧
    (after (.i64 123)).frame.locals[6]? = some (some .unit) := by decide
example : (after (.i64 123)).frame.locals[5]? = some (some (.pointer 2 0)) ∧
    (after (.i64 123)).frame.heap[2]? = some ReferenceHeap.nilObject := by decide
example : ReferenceHeap.loadRef (before (.i64 123)).target.frame.heap (.object 3 1) =
    some (.object 1 0) ∧
    ReferenceHeap.loadScalar (before (.i64 123)).target.frame.heap (.object 1 0) = none := by decide
example : ReferenceHeap.loadScalar (after (.i64 123)).frame.heap (.object 0 1) = some 42 := by decide
example : BufferRelated (finished (before (.i64 123)) shell [] (after (.i64 123))).source
    (after (.i64 123)).frame.heap 4 0 :=
  (final_valid (.i64 123)).resources (.buffer 4 0) (by simp [finished, before, inventory])

-- The old all-locals certificate really is impossible for this changed scratch.
theorem nonunit_rejects_old :
    ¬ FinishExecution program 1 1 (before (.i64 123)) shell (after (.i64 123)) := by
  intro h
  have slot := congrArg (fun xs => xs[6]?) h.locals
  change some (some ReferenceCfg.Value.unit) = some (some (.i64 123)) at slot
  contradiction

-- Live/result destinations must not overlap the scratch write.
example : ¬ CommonDataCaseEntryContext.Reserved (before (.i64 123)).ctx
    (before (.i64 123)).slots [5] := by
  intro h
  exact h 0 (.data 0) 5 rfl rfl trivial (by simp)
example : (after (.i64 123)).frame.locals[6]? ≠ (before (.i64 123)).target.frame.locals[6]? := by decide
example : CommonDataCaseRelocation.walk program 1 0 (before (.i64 123)).target = none := by decide

#print axioms installed_walk
#print axioms installed_execution
#print axioms installed_live_execution
#print axioms live_finish_context
#print axioms live_finish_result
#print axioms live_result_preserved
#print axioms installed_body_finish
#print axioms concrete_finish_result
#print axioms unit_execution
#print axioms live_execution
#print axioms final_valid
#print axioms nonunit_rejects_old
end Jihoo.CommonDataInstalledFinishChecks
