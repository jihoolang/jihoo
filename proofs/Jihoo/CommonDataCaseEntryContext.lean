import Jihoo.CommonDataCaseCfg
import Jihoo.CommonDataTargetContext

/-! Connect the executed fixed Case ABI to the common resource context.
Only entry prefixes execute: arbitrary branch blocks remain unproved. -/
set_option maxHeartbeats 1000000

namespace Jihoo.CommonDataCaseEntryContext
open CommonDataTargetContext CommonDataCaseCfg CommonDataReference
open RecursiveLexicalFields RecursiveFieldRuntime RecursiveFieldOwnership

-- Keep array updates opaque while transporting frame projections.
attribute [local irreducible] nodeLocals nilLocals

/-- Reserve overwritten locals for every active lexical binding. Dead/ghost
bindings need no reservation. Node conservatively reserves parent aliases too. -/
def Reserved (ctx : List Entry) (slots writes : List Nat) : Prop :=
  ∀ (k : Nat) e slot, ctx[k]? = some e → slots[k]? = some slot → Active e → slot ∉ writes

theorem Binding.reframe (h : Binding rs f e slot)
    (same : Active e → g.locals[slot]? = f.locals[slot]?) : Binding rs g e slot := by
  cases e with
  | data k => obtain ⟨i, hi, hv⟩ := h; exact ⟨i, hi, (same trivial).trans hv⟩
  | buffer k => obtain ⟨x, j, hi, hv⟩ := h; exact ⟨x, j, hi, (same trivial).trans hv⟩
  | nat n => exact (same trivial).trans h
  | scalar => obtain ⟨n, hv⟩ := h; exact ⟨n, (same trivial).trans hv⟩
  | ghost | dead => trivial

theorem Bindings.reframe (h : Bindings rs f ctx slots)
    (same : ∀ (k : Nat) e slot, ctx[k]? = some e → slots[k]? = some slot →
      Active e → g.locals[slot]? = f.locals[slot]?) : Bindings rs g ctx slots := by
  induction h with
  | nil => exact .nil
  | @cons e slot ctx slots head tail ih =>
    exact .cons (Binding.reframe head (same 0 e slot rfl rfl))
      (ih (fun k e slot he hs => same (k+1) e slot he hs))

theorem Context.reframe (h : Context rs pending sf tf ctx env slots source f)
    (heap : g.heap = f.heap) (bindings : Bindings rs g ctx slots) :
    Context rs pending sf tf ctx env slots source g := by
  exact ⟨h.valid, h.agreement, bindings, by simpa [heap] using h.resources,
    h.owned, h.separated, by simpa [heap] using h.shells⟩

/-- Node executes nine ticks, derives child locals 4/5, retires every parent
alias, and moves its shell to pending. Both ambient ownership frames and the
suspended call stack are retained. Source state and target heap are unchanged. -/
theorem node_entry_context
    (h : CommonContext (.node x j left right :: images) buffers sizes pending sf tf
      ctx env slots source (stateAt H vs 0 ks).frame)
    (selected : ctx[index]? = some (.data 0)) (slot : slots[index]? = some 0)
    (reserved : Reserved ctx slots [1,2,3,4,5])
    (space : 7 ≤ vs.size) (bound : ks.length ≤ limit) (enough : 9 ≤ fuel)
    (ghostSlots : List Nat) :
    sourceEnter source env index ghostSlots.length = some
      (bindValues ghostSlots.length ⟨root left.source, root right.source⟩ env, some x) ∧
    runPrefix nb cb fuel 9 limit (stateAt H vs 0 ks) =
      some (stateAt H (nodeLocals vs j left.target right.target) 4 ks, []) ∧
    BoundedPrefix nb cb limit 9 (stateAt H vs 0 ks) []
      (stateAt H (nodeLocals vs j left.target right.target) 4 ks) ∧
    CommonContext (left :: right :: images) buffers sizes
      (⟨x, j, (Image.node x j left right).object⟩ :: pending) sf tf
      (bindContext ghostSlots.length ctx)
      (bindValues ghostSlots.length ⟨root left.source, root right.source⟩ env)
      (5 :: 4 :: (ghostSlots ++ slots)) source
      (stateAt H (nodeLocals vs j left.target right.target) 4 ks).frame := by
  obtain ⟨i, loc, hi, hs, value, operand, related⟩ := h.toContext.data_lookup selected
  have eq : i = .node x j left right := by simpa [inventory] using hi.symm
  subst i
  have locEq : loc = 0 := by simpa [slot] using hs.symm
  subst loc
  have connected : vs[0]? = some (some (.pointer j 0)) := by
    obtain ⟨_, _, hv⟩ := h.bindings.lookup selected
    simp_all [Binding, inventory, Local, Image.target, stateAt, ReferenceCfg.operand, TreeDropCall.arg]
  obtain ⟨entered, run, pre, ll, rl, _, _, _⟩ :=
    node_entry nb cb related value connected space bound enough (ghosts := ghostSlots.length)
  have bindings : Bindings (inventory (.node x j left right :: images) buffers)
      (stateAt H (nodeLocals vs j left.target right.target) 4 ks).frame ctx slots := by
    apply Bindings.reframe (f := (stateAt H vs 0 ks).frame)
      (g := (stateAt H (nodeLocals vs j left.target right.target) 4 ks).frame) h.bindings
    intro k e sl he hs ha
    dsimp only [stateAt]
    change (nodeLocals vs j left.target right.target)[sl]? = vs[sl]?
    exact node_frame (vs := vs) (j := j) (l := left.target) (r := right.target)
      (reserved k e sl he hs ha)
  have moved := Context.reframe h.toContext
    (g := (stateAt H (nodeLocals vs j left.target right.target) 4 ks).frame) rfl bindings
  obtain ⟨_, _, opened⟩ := moved.open_case (leftSlot := 4) (rightSlot := 5) selected
    (show Local (stateAt H (nodeLocals vs j left.target right.target) 4 ks).frame 4
      (.pointer left.target 0) from ll)
    (show Local (stateAt H (nodeLocals vs j left.target right.target) 4 ks).frame 5
      (.pointer right.target 0) from rl) ghostSlots
  exact ⟨entered, run, pre, opened, h.bufferSizes⟩

/-- Nil executes three ticks and frees only the physical Nil box. Source
state stutters; consumed aliases become dead; retained resources and pending
shells survive by the source/target separation carried in Context. -/
theorem nil_entry_context
    (h : CommonContext (.nil j :: images) buffers sizes pending sf tf
      ctx env slots source (stateAt H vs 0 ks).frame)
    (selected : ctx[index]? = some (.data 0)) (slot : slots[index]? = some 0)
    (reserved : Reserved (CommonData.removeHead ctx) slots [1,6])
    (space : 7 ≤ vs.size) (bound : ks.length ≤ limit) (enough : 3 ≤ fuel) :
    sourceEnter source env index ghosts = some (env, none) ∧
    runPrefix nb cb fuel 3 limit (stateAt H vs 0 ks) =
      some (stateAt (retired H j ReferenceHeap.nilObject) (nilLocals vs) 3 ks, [.free j]) ∧
    BoundedPrefix nb cb limit 3 (stateAt H vs 0 ks) [.free j]
      (stateAt (retired H j ReferenceHeap.nilObject) (nilLocals vs) 3 ks) ∧
    CommonContext images buffers sizes pending sf tf (CommonData.removeHead ctx) env slots source
      (stateAt (retired H j ReferenceHeap.nilObject) (nilLocals vs) 3 ks).frame := by
  obtain ⟨i, loc, hi, hs, value, operand, related⟩ := h.toContext.data_lookup selected
  have eq : i = .nil j := by simpa [inventory] using hi.symm
  subst i
  have locEq : loc = 0 := by simpa [slot] using hs.symm
  subst loc
  have connected : vs[0]? = some (some (.pointer j 0)) := by
    obtain ⟨_, _, hv⟩ := h.bindings.lookup selected
    simp_all [Binding, inventory, Local, Image.target, stateAt, ReferenceCfg.operand, TreeDropCall.arg]
  obtain ⟨entered, run, pre, _, _⟩ := nil_entry nb cb related value connected space bound enough
  have fresh : Fresh (CommonData.removeHead ctx) slots 6 := by
    intro k e sl he hs ha eq
    have outside := reserved k e sl he hs ha
    simp [eq] at outside
  have frees : Frees H (Image.nil j).ids (retired H j ReferenceHeap.nilObject) :=
    .cons (empty_case_total related.layout).2.1 .nil
  have after := h.after_drop (dest := 6) (continuation := 3) CommonData.Destroy.empty frees fresh
  have bindings := Bindings.reframe after.bindings
    (g := (stateAt (retired H j ReferenceHeap.nilObject) (nilLocals vs) 3 ks).frame)
    (by
      intro k e sl he hs ha
      have apart := reserved k e sl he hs ha
      have a : sl ≠ 1 := by simp_all
      have b : sl ≠ 6 := by simp_all
      exact (nil_frame a b).trans (TreeDropCall.resume_local (s := stateAt H vs 0 ks) b).symm)
  exact ⟨entered, run, pre, Context.reframe after.toContext rfl bindings, h.bufferSizes⟩

end Jihoo.CommonDataCaseEntryContext
