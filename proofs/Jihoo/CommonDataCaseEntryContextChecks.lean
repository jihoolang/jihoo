import Jihoo.CommonDataCaseEntryContext
import Jihoo.CommonDataTargetContextChecks
import Jihoo.CommonDataCaseCfgChecks

namespace Jihoo.CommonDataCaseEntryContext.Checks
open CommonDataTargetContext CommonDataCaseCfg CommonDataReference RecursiveLexicalFields
open CommonDataReferenceChecks (image source)
namespace Fixture
open CommonDataTargetContext.Checks (heap ctx env)
def slots : List Nat := [0,0,7,8,9,10]
def locals : Array (Option ReferenceCfg.Value) :=
  #[some (.pointer 3 0), none, none, none, some (.i64 999), some .null, none,
    some (.pointer 4 0), some (.pointer 0 0), some (.i64 77), some (.u64 9)]
def stack := [CommonDataCaseCfg.Checks.caller]
theorem initial : CommonContext [image, .nil 4] [(4,0)] [2] [] [] [10]
    ctx env slots source (stateAt heap locals 0 stack).frame := by
  have old := CommonDataTargetContext.Checks.initial
  refine ⟨⟨old.valid, old.agreement, ?_, old.resources, old.owned, old.separated, old.shells⟩,
    old.bufferSizes⟩
  exact .cons ⟨_, rfl, rfl⟩ (.cons ⟨_, rfl, rfl⟩
    (.cons ⟨_, rfl, rfl⟩ (.cons ⟨_, _, rfl, rfl⟩ (.cons ⟨_, rfl⟩ (.cons rfl .nil)))))
theorem reserved : Reserved ctx slots [1,2,3,4,5] := by
  intro k e sl _ hs _
  have member := List.mem_of_getElem? hs
  simp [slots] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Poisoned children are overwritten by actual loads. Retained Nil, Buffer,
scalar/nat, a ghost slot outside the array, and a suspended caller coexist. -/
theorem node_context :
    CommonContext [.nil 1, .nil 2, .nil 4] [(4,0)] [2]
      [⟨7,3,image.object⟩] [] [10] (bindContext 1 ctx)
      (bindValues 1 ⟨none,none⟩ env) (5 :: 4 :: 99 :: slots) source
      (stateAt heap (nodeLocals locals 3 1 2) 4 stack).frame :=
  (node_entry_context (nb := CommonDataCaseCfg.Checks.stop) (cb := CommonDataCaseCfg.Checks.stop)
    initial (index := 0) rfl rfl reserved (by decide) (limit := 1) (by decide)
    (fuel := 9) (by decide) [99]).2.2.2

/-- After entry, dropping a child preserves the pending shell even though its
saved child reference now points at a dead Nil box. -/
theorem pending_after_child :
    CommonContext [.nil 2, .nil 4] [(4,0)] [2] [⟨7,3,image.object⟩] [] [10]
      (CommonData.removeHead (bindContext 1 ctx)) (bindValues 1 ⟨none,none⟩ env)
      (5 :: 4 :: 99 :: slots) source
      (TreeDropCall.resume (stateAt heap (nodeLocals locals 3 1 2) 4 stack)
        6 0 (retired heap 1 ReferenceHeap.nilObject)).frame := by
  apply node_context.after_drop CommonData.Destroy.empty
  · exact Frees.cons (by decide +kernel) Frees.nil
  · intro k e sl _ hs _
    have member := List.mem_of_getElem? hs
    simp [slots] at member
    omega

theorem aliases_retired : (bindContext 1 ctx)[3]? = some .dead ∧
    (bindContext 1 ctx)[4]? = some .dead := by decide

/-- Retained scalar collision really changes its value; reservation excludes it. -/
theorem scalar_clobbered : (nodeLocals locals 3 1 2)[4]? ≠ locals[4]? := by decide

theorem active_collision_rejected : ¬ Reserved [.scalar] [4] [1,2,3,4,5] := by
  intro h; exact h 0 .scalar 4 rfl rfl trivial (by simp)

theorem nil_unit_collision_rejected : ¬ Reserved [.nat 9] [6] [1,6] := by
  intro h; exact h 0 (.nat 9) 6 rfl rfl trivial (by simp)

theorem target_overlap_rejected :
    ¬ (targets [.data (.nil 1), .buffer 4 1] ++ [3,10]).Nodup := by decide

/-- Nil fixture has a nonempty source frame and retained Buffer/scalar. -/
def nilCtx : List Entry := [.data 0, .data 0, .buffer 1, .scalar]
def nilEnv : List Value := [.data none, .data none, .buffer 4, .scalar 77]
def nilSlots : List Nat := [0,0,7,8]
def nilVs : Array (Option ReferenceCfg.Value) :=
  #[some (.pointer 4 0), none, none, none, none, none, none,
    some (.pointer 0 0), some (.i64 77)]
theorem nil_initial : CommonContext [.nil 4] [(4,0)] [2] [] [7] [3,2,10]
    nilCtx nilEnv nilSlots source (stateAt heap nilVs 0 stack).frame := by
  constructor
  · constructor
    · exact CommonDataReferenceChecks.source_valid
    · exact .cons ⟨_, rfl, rfl⟩ (.cons ⟨_, rfl, rfl⟩
        (.cons ⟨_, rfl, rfl⟩ (.cons ⟨_, rfl⟩ .nil)))
    · exact .cons ⟨_, rfl, rfl⟩ (.cons ⟨_, rfl, rfl⟩
        (.cons ⟨_, _, rfl, rfl⟩ (.cons ⟨_, rfl⟩ .nil)))
    · intro r hr
      have member : r ∈ inventory [image, .nil 4] [(4,0)] := by
        simp [inventory] at hr ⊢
        rcases hr with rfl | rfl <;> simp
      exact CommonDataTargetContext.Checks.initial.resources r member
    · refine ⟨by decide, ?_, ?_⟩
      · intro x hx
        change x ∈ [4,7] at hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> rfl
      · simp [source, HeapLeases.Unborrowed]
    · decide
    · intro a ha; cases ha
  · exact CommonDataTargetContext.Checks.initial.bufferSizes

theorem nil_reserved : Reserved (CommonData.removeHead nilCtx) nilSlots [1,6] := by
  intro k e sl _ hs _
  have member := List.mem_of_getElem? hs
  simp [nilSlots] at member
  rcases member with rfl | rfl | rfl <;> decide

theorem nil_context : CommonContext [] [(4,0)] [2] [] [7] [3,2,10]
    (CommonData.removeHead nilCtx) nilEnv nilSlots source
    (stateAt (retired heap 4 ReferenceHeap.nilObject) (nilLocals nilVs) 3 stack).frame :=
  (nil_entry_context (nb := CommonDataCaseCfg.Checks.stop) (cb := CommonDataCaseCfg.Checks.stop)
    nil_initial (index := 0) rfl rfl nil_reserved (by decide) (limit := 1) (by decide)
    (fuel := 3) (ghosts := 2) (by decide)).2.2.2

theorem nil_aliases_retired : CommonData.removeHead nilCtx = [.dead,.dead,.buffer 0,.scalar] := rfl
end Fixture
end Jihoo.CommonDataCaseEntryContext.Checks
