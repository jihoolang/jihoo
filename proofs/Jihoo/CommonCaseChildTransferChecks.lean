import Jihoo.CommonCaseChildTransfer
import Jihoo.CommonDataCaseRelocatedContext
import Jihoo.CommonDataReferenceChecks

set_option linter.unusedSimpArgs false
namespace Jihoo.CommonCaseChildTransfer.Checks
open CommonCompositionContract CommonDataTargetContext CommonDataReference RecursiveLexicalFields
open CommonDataReferenceChecks (image source heap)
open CommonDataInstalledFinish CommonDataBranchFinish

def stop : ReferenceCfg.Block := ⟨#[], .goto 10⟩
def locals : Array (Option ReferenceCfg.Value) :=
  #[none,none,none,none,none,none,none,some (.pointer 3 0),some (.i64 77)]
def callers : List ReferenceCalls.Continuation := [⟨0,10,#[],⟨6,false⟩⟩]
def before : Boundary :=
  { images := [image], buffers := [], sizes := [], pending := [], sf := [4], tf := [0],
    ctx := [.data 0,.scalar], env := [.data (some 7),.scalar 77], slots := [7,8],
    source := source, target := CommonDataCaseCfg.stateAt heap locals 6 callers }
def input : CaseInput :=
  { before := before, pre := #[], post := #[], nilBody := stop, nodeBody := stop,
    index := 0, src := 7, ghostSlots := [99], selected := rfl, slot := rfl, pc := rfl,
    space := by exact of_decide_eq_true rfl }
def entered := input.nodeOut 7 3 (.nil 1) (.nil 2) []
/-- Installed caller extends the copied-entry code with two call exits and
literal/free blocks. Its live scalar local 8 and suspended caller survive. -/
def fn : ReferenceCalls.Function :=
  let base := CommonDataCaseCfg.body stop stop
  ⟨⟨⟨base.code.base.locals ++ #[.ptr,.i64], base.code.base.blocks ++
      #[CommonDataCaseRelocation.failure,
        ⟨#[⟨⟨0,false⟩,.use (TreeDropCall.arg 7)⟩],.goto 0⟩] ++
      #[stop, CommonLiteralBody.block 1 7 9,
        ⟨#[], .free (TreeDropCall.arg 0) ⟨6,false⟩ 10⟩, stop]⟩,
    #[none,none,none,none,
      some (.call (TreeDropCall.call 1 (TreeDropCall.arg 4) 6 7)),none,none,
      some (.call (TreeDropCall.call 1 (TreeDropCall.arg 5) 6 8))]⟩,#[]⟩
def program : ReferenceCalls.Program := #[fn, TreeDropCall.body 1]
def shell : Pending := ⟨7,3,image.object⟩

theorem valid : before.Valid := by
  constructor
  · constructor
    · exact CommonDataReferenceChecks.source_valid
    · exact .cons ⟨_,rfl,rfl⟩ (.cons ⟨77,rfl⟩ .nil)
    · exact .cons ⟨_,rfl,rfl⟩ (.cons ⟨77,rfl⟩ .nil)
    · intro r hr
      have eq : r = .data image := by simpa [before, inventory] using hr
      subst r; exact CommonDataReferenceChecks.related
    · refine ⟨by exact of_decide_eq_true rfl, ?_, ?_⟩
      · intro x hx
        change x ∈ [7,4] at hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> rfl
      · simp [before, source, HeapLeases.Unborrowed]
    · decide
    · intro a ha; cases ha
  · exact ⟨rfl, by intro k x n hx; simp [before] at hx⟩

theorem reserved : CommonDataCaseEntryContext.Reserved before.ctx before.slots [0,1,2,3,4,5] := by
  intro k e slot _ hs _
  have member := List.mem_of_getElem? hs
  change slot ∈ [7,8] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide

/-- Context follows the established ownership entry theorem; execution is
checked in the actual larger program, not transferred between programs. -/
theorem entry : Transfer program 3 11 before entered [] := by
  have old := (CommonDataCaseRelocatedContext.entryProvider.node input 7 3 (.nil 1) (.nil 2) [] 3
    valid rfl reserved (by exact of_decide_eq_true rfl)).2
  exact ⟨by exact of_decide_eq_true rfl, old.context, rfl, rfl, rfl⟩

theorem entered_valid : entered.Valid := entry.context valid

def middle (source : CommonData.State) (K L : ReferenceHeap.Heap) :=
  CommonLiteralBody.out (consumed entered 6 7 6 8 source K L) 1 7 9

theorem literal_site (source K L) : LiteralSite program
    (consumed entered 6 7 6 8 source K L) 1 7 9 :=
  ⟨fn,rfl,rfl,rfl,rfl,rfl,by exact of_decide_eq_true rfl,by exact of_decide_eq_true rfl⟩

theorem fresh_left : Fresh (CommonData.removeHead entered.ctx) entered.slots 6 := by
  intro k e slot _ hs _
  have member := List.mem_of_getElem? hs
  change slot ∈ [5,4,99,7,8] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> decide

theorem fresh_after (dest : Nat) (different : dest ≠ 8) :
    Fresh (CommonData.removeHead (CommonData.removeHead entered.ctx)) entered.slots dest := by
  intro k e slot he hs active
  change [Entry.dead,.dead,.ghost,.dead,.scalar][k]? = some e at he
  change [5,4,99,7,8][k]? = some slot at hs
  match k with
  | 0 | 1 | 2 | 3 => cases Option.some.inj he; contradiction
  | 4 => have eq : slot = 8 := Option.some.inj hs.symm
         exact eq ▸ Ne.symm different
  | k+5 => simp at he

theorem result_collision_rejected :
    ¬ Fresh (CommonData.removeHead (CommonData.removeHead entered.ctx)) entered.slots 8 := by
  intro collision
  exact collision 4 .scalar 8 rfl rfl trivial rfl

theorem body_constructed : ∃ source K L,
    BodyResult (CommonCaseChildConsumption.graph 7) 4 .scalar program 3 12 entered
      (middle source K L) (.scalar 7) [] [.free 1,.free 2] 1 := by
  apply body entered (left := .nil 1) (right := .nil 2) (ghosts := 1) (ctx := before.ctx)
    rfl rfl rfl rfl entered_valid (by exact of_decide_eq_true rfl) (dropId := 1) rfl
    (destLeft := 6) (next := 7) (destRight := 6) (continuation := 8)
  · exact ⟨⟨fn,rfl,by exact of_decide_eq_true rfl,rfl⟩,by exact of_decide_eq_true rfl⟩
  · intro slot hs
    have eq : slot = 4 := by simpa [entered, input, before, CaseInput.nodeOut] using hs.symm
    subst slot; exact ⟨fn,rfl,rfl⟩
  · intro K; exact ⟨⟨fn,rfl,by exact of_decide_eq_true rfl,rfl⟩,by exact of_decide_eq_true rfl⟩
  · intro K slot hs
    have eq : slot = 5 := by simpa [entered, input, before, CaseInput.nodeOut] using hs.symm
    subst slot; exact ⟨fn,rfl,rfl⟩
  · exact fresh_left
  · exact fresh_after 6 (by exact of_decide_eq_true rfl)
  · exact fresh_after 1 (by exact of_decide_eq_true rfl)
  · decide
  · decide
  · exact literal_site

theorem finish_site (source K L) : Site program (middle source K L) shell 0 6 10 :=
  ⟨⟨fn,rfl,rfl,rfl,rfl,by exact of_decide_eq_true rfl⟩,rfl,by exact of_decide_eq_true rfl⟩

theorem finish_reserved (source K L) : CommonDataCaseEntryContext.Reserved
    (middle source K L).ctx (middle source K L).slots [6] := by
  intro k e slot he hs active
  simpa using fresh_after 6 (by exact of_decide_eq_true rfl) k e slot he hs active

/-- Closed entry + explicit source drops/literal + installed shell free.
No desired body, walk or finish certificate is taken as a premise. -/
theorem pipeline : ∃ source K L,
    Transfer program 3 24 before
      (finished (middle source K L) shell [] (stopped (middle source K L) shell 6 10))
      [.free 1,.free 2,.free 3] ∧
    FinishResult program 3 1 (middle source K L)
      (finished (middle source K L) shell [] (stopped (middle source K L) shell 6 10))
      shell [] .scalar (.scalar 7) 1 := by
  obtain ⟨source,K,L,b⟩ := body_constructed
  have fin := installed_body_finish (shell := shell) (tail := []) entered_valid b rfl (finish_site source K L)
    (by exact of_decide_eq_true rfl) (finish_reserved source K L) (by exact of_decide_eq_true rfl)
  exact ⟨source,K,L,by simpa [shell] using entry.then fin.1,fin.2⟩

/-- The certificates preserve authority and observable results, including an
ambient source owner, target buffer reservation, scalar and suspended caller. -/
theorem complete : ∃ d : Boundary,
    Transfer program 3 24 before d [.free 1,.free 2,.free 3] ∧ d.Valid ∧
    CommonData.Post .scalar d.source (.scalar 7) [4] ∧
    Local d.target.frame 1 (.i64 7) ∧ Local d.target.frame 8 (.i64 77) ∧
    d.target.stack = callers ∧ d.sf = [4] ∧ d.tf = [0] ∧ d.pending = [] := by
  obtain ⟨source,K,L,b⟩ := body_constructed
  have exec := installed_live_execution (limit := 3) (tail := []) (finish_site source K L)
    (b.transfer.context entered_valid) rfl
    (by exact of_decide_eq_true rfl) (finish_reserved source K L) (by decide : 1 ≠ 6)
  have fin := live_finish_result (b.transfer.context entered_valid) (tail := []) rfl b.post exec
  refine ⟨_, ?_, fin.transfer.context (b.transfer.context entered_valid), fin.post,
    live_result_preserved (tail := []) b exec, ?_, rfl, rfl, rfl, rfl⟩
  · simpa [shell] using (entry.then b.transfer).then fin.transfer
  · rfl

def leftHeap := retired heap 1 ReferenceHeap.nilObject
def childrenHeap := retired leftHeap 2 ReferenceHeap.nilObject
def done := finished (middle source leftHeap childrenHeap) shell []
  (stopped (middle source leftHeap childrenHeap) shell 6 10)

theorem exact_walk : CommonDataCaseRelocation.walk program 24 3 before.target =
    some (done.target, [.free 1,.free 2,.free 3]) := by decide

theorem one_tick_short : CommonDataCaseRelocation.walk program 23 3 before.target =
    some ((middle source leftHeap childrenHeap).target, [.free 1,.free 2]) := by decide

theorem insufficient_stack : CommonDataCaseRelocation.walk program 24 1 before.target = none := by decide

theorem buffer_survives : done.target.frame.heap[0]? = heap[0]? := rfl

theorem all_consumed : done.target.frame.heap[1]?.map ReferenceHeap.Object.alive = some false ∧
    done.target.frame.heap[2]?.map ReferenceHeap.Object.alive = some false ∧
    done.target.frame.heap[3]?.map ReferenceHeap.Object.alive = some false := by decide

/-- Operational regression with a nonempty recursive left child. The generic
body theorem above is polymorphic in both trees; this additional computation
checks recursive call placement and its larger exact count in the same program. -/
def recursiveHeap : ReferenceHeap.Heap := #[CommonDataReferenceChecks.buffer,
  ReferenceHeap.nilObject, ReferenceHeap.nilObject,
  ReferenceHeap.node (.object 4 0) (.object 5 0),
  ReferenceHeap.node (.object 1 0) (.object 2 0), ReferenceHeap.nilObject]
def recursiveStart := CommonDataCaseCfg.stateAt recursiveHeap locals 6 callers
def recursiveChildren := retired
  (retired (retired (retired recursiveHeap 4 (ReferenceHeap.node (.object 1 0) (.object 2 0)))
    1 ReferenceHeap.nilObject) 2 ReferenceHeap.nilObject) 5 ReferenceHeap.nilObject
def recursiveEnd : ReferenceCalls.State :=
  { done.target with frame :=
    { done.target.frame with
      heap := retired recursiveChildren 3 (ReferenceHeap.node (.object 4 0) (.object 5 0))
      locals := ((done.target.frame.locals.set! 3 (some (.referenceWord (.object 5 0)))).set!
        4 (some (.pointer 4 0))).set! 5 (some (.pointer 5 0)) } }

theorem recursive_walk : CommonDataCaseRelocation.walk program 40 4 recursiveStart =
    some (recursiveEnd, [.free 4,.free 1,.free 2,.free 5,.free 3]) := by decide

#print axioms invoke_exact
#print axioms drop_exact
#print axioms body
#print axioms entry
#print axioms body_constructed
#print axioms pipeline
#print axioms complete
#print axioms result_collision_rejected
#print axioms exact_walk
#print axioms one_tick_short
#print axioms insufficient_stack
#print axioms buffer_survives
#print axioms all_consumed
#print axioms recursive_walk
end Jihoo.CommonCaseChildTransfer.Checks
