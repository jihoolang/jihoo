import Jihoo.CommonCaseChildConsumption
import Jihoo.CommonLiteralBody
import Jihoo.CommonDataInstalledFinish

set_option linter.unusedSimpArgs false
namespace Jihoo.CommonCaseChildTransfer
open CommonDataTargetContext CommonDataReference RecursiveLexicalFields
open RecursiveFieldRuntime RecursiveFieldOwnership HeapLeases LinearHeapPrograms
open CommonCompositionContract

/-- The two independently introduced bounded walkers have identical semantics. -/
theorem walk_eq (p : ReferenceCalls.Program) (n limit : Nat) (s : ReferenceCalls.State) :
    CommonDataCaseRelocation.walk p n limit s = TreeDropCall.walk p n limit s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [CommonDataCaseRelocation.walk, TreeDropCall.walk]
    split <;> try rfl
    cases ht : ReferenceCalls.tick p s with
    | none => simp
    | some next => cases hm : next.machine <;> simp [hm, ih]

/-- Exact caller instruction + recursive body + return; no run premise. -/
theorem invoke_exact
    (installed : p[dropId]? = some (TreeDropCall.body dropId))
    (site : TreeDropCall.Site p s dest continuation)
    (atCall : ∃ fn, p[s.function]? = some fn ∧
      ReferenceCalls.extension fn.code s.frame = some (.call (TreeDropCall.call dropId owner dest continuation)))
    (selected : ReferenceCfg.operand s.frame owner = some (.pointer i.target 0))
    (layout : Layout s.frame.heap i) (unique : i.ids.Nodup)
    (depth : s.stack.length + 1 + i.depth ≤ limit) :
    ∃ K, CommonDataCaseRelocation.walk p (1 + TreeDropCall.ticks i + 1) limit s =
      some (TreeDropCall.resume s dest continuation K, i.ids.map HeapLifecycle.Event.free) ∧
      Frees s.frame.heap i.ids K := by
  obtain ⟨fn, found, ext⟩ := atCall
  obtain ⟨K, run, frees⟩ := TreeDropCall.tree_prefix installed layout unique
    (ks := TreeDropCall.suspension s dest continuation :: s.stack) (limit := limit) depth
  refine ⟨K, ?_, frees⟩
  have h0 : s.stack.length ≤ limit := by omega
  have h1 : s.stack.length + 1 ≤ limit := by omega
  have enter := TreeDropCall.enter_owner installed site selected
  have ret := TreeDropCall.return_owner installed (K := K) (vs := TreeDropCall.finalLocals i) site
  rw [walk_eq, TreeDropCall.walk_add]
  have first : TreeDropCall.walk p (1 + TreeDropCall.ticks i) limit s =
      some (TreeDropCall.stateAt dropId K (TreeDropCall.finalLocals i) 5
        (TreeDropCall.suspension s dest continuation :: s.stack), i.ids.map HeapLifecycle.Event.free) := by
    rw [Nat.add_comm 1, TreeDropCall.walk]
    simp [ReferenceCalls.stackDepth, h0, Nat.not_lt.mpr h0,
      ReferenceCalls.tick, found, ext, enter, run]
  rw [first]
  have budget : ReferenceCalls.stackDepth (TreeDropCall.stateAt dropId K
      (TreeDropCall.finalLocals i) 5 (TreeDropCall.suspension s dest continuation :: s.stack)) ≤ limit := h1
  have last : TreeDropCall.walk p 1 limit
      (TreeDropCall.stateAt dropId K (TreeDropCall.finalLocals i) 5
        (TreeDropCall.suspension s dest continuation :: s.stack)) =
      some (TreeDropCall.resume s dest continuation K, []) := by
    rw [TreeDropCall.walk]
    rw [ite_eq_right (Nat.not_lt.mpr budget), ret]
    simp [TreeDropCall.walk, ReferenceCalls.stackDepth, TreeDropCall.resume, h0]
  simp [last]

/-- Resource-aware exact prefix, including the source destruction and lexical
lookup needed to build a source Eval. All pending and ambient ownership survives. -/
theorem drop_exact {k : Nat}
    (h : CommonContext (i :: images) buffers sizes pending sf tf ctx env slots source s.frame)
    (selected : ctx[k]? = some (.data 0))
    (installed : p[dropId]? = some (TreeDropCall.body dropId))
    (site : TreeDropCall.Site p s dest continuation)
    (callAt : ∀ slot, slots[k]? = some slot → ∃ fn, p[s.function]? = some fn ∧
      ReferenceCalls.extension fn.code s.frame = some (.call
        (TreeDropCall.call dropId (TreeDropCall.arg slot) dest continuation)))
    (fresh : Fresh (CommonData.removeHead ctx) slots dest)
    (depth : s.stack.length + 1 + i.depth ≤ limit) :
    env[k]? = some (.data (root i.source)) ∧ ∃ middle K,
      CommonData.Destroy (root i.source) source (i.source.owners.map Event.free) middle ∧
      CommonDataCaseRelocation.walk p (1 + TreeDropCall.ticks i + 1) limit s =
        some (TreeDropCall.resume s dest continuation K, i.ids.map HeapLifecycle.Event.free) ∧
      CommonContext images buffers sizes pending sf tf (CommonData.removeHead ctx) env slots middle
        (TreeDropCall.resume s dest continuation K).frame := by
  obtain ⟨a, slot, ha, hs, lookup, operand, related⟩ := h.toContext.data_lookup selected
  have eq : i = a := by simpa [inventory] using ha
  subst a
  have own : Owns source.buffers.heap
      (i.source.owners ++ (footprint (sources (inventory images buffers)) ++ (pending.map Pending.source ++ sf))) := by
    simpa [inventory, sources, footprint, Resource.source, Capability.owners, List.append_assoc] using h.owned
  obtain ⟨middle, destroyed, _, _, _⟩ := CommonData.destroy_total related.fields h.valid own
  obtain ⟨K, run, frees⟩ := invoke_exact installed site (callAt slot hs) operand related.layout related.distinct depth
  refine ⟨lookup, middle, K, destroyed, run, ⟨h.toContext.after_drop destroyed frees fresh, h.bufferSizes.length, ?_⟩⟩
  intro k x n hx hn
  rw [destroyed.lengths]
  exact h.bufferSizes.lookup k x n hx hn

/-- Explicit output of the two calls. Retired aliases stay in the lexical map. -/
def consumed (a : Boundary) (destLeft next destRight continuation : Nat)
    (source : CommonData.State) (K L : ReferenceHeap.Heap) : Boundary :=
  { a with
    images := []
    buffers := []
    sizes := []
    ctx := CommonData.removeHead (CommonData.removeHead a.ctx)
    source := source
    target := TreeDropCall.resume (TreeDropCall.resume a.target destLeft next K)
      destRight continuation L }

/-- Pure installed-code and local ABI checks for the final literal. -/
def LiteralSite (p : ReferenceCalls.Program) (a : Boundary)
    (slot n continuation : Nat) : Prop :=
  ∃ fn : ReferenceCalls.Function,
    p[a.target.function]? = some fn ∧
    fn.code.base.blocks[a.target.frame.block]? = some (CommonLiteralBody.block slot n continuation) ∧
    (fn.code.exits[a.target.frame.block]?).join = none ∧
    a.target.frame.index = 0 ∧
    fn.code.base.locals[slot]? = some .i64 ∧
    slot < a.target.frame.locals.size ∧
    continuation < fn.code.base.blocks.size

/-- Constructs typing, source Eval, exact Transfer, scalar ownership and its
local ABI from resource invariants and installed instruction premises. -/
theorem body (a : Boundary)
    (images : a.images = [left, right]) (buffers : a.buffers = []) (sizes : a.sizes = [])
    (context : a.ctx = bindContext ghosts ctx) (valid : a.Valid)
    (bound : n < 2^63)
    (installed : p[dropId]? = some (TreeDropCall.body dropId))
    (siteLeft : TreeDropCall.Site p a.target destLeft next)
    (callLeft : ∀ slot, a.slots[1]? = some slot → ∃ fn, p[a.target.function]? = some fn ∧
      ReferenceCalls.extension fn.code a.target.frame = some (.call
        (TreeDropCall.call dropId (TreeDropCall.arg slot) destLeft next)))
    (siteRight : ∀ K, TreeDropCall.Site p
      (TreeDropCall.resume a.target destLeft next K) destRight continuation)
    (callRight : ∀ K slot, a.slots[0]? = some slot → ∃ fn,
      p[(TreeDropCall.resume a.target destLeft next K).function]? = some fn ∧
      ReferenceCalls.extension fn.code (TreeDropCall.resume a.target destLeft next K).frame =
        some (.call (TreeDropCall.call dropId (TreeDropCall.arg slot) destRight continuation)))
    (freshLeft : Fresh (CommonData.removeHead a.ctx) a.slots destLeft)
    (freshRight : Fresh (CommonData.removeHead (CommonData.removeHead a.ctx)) a.slots destRight)
    (freshResult : Fresh (CommonData.removeHead (CommonData.removeHead a.ctx)) a.slots resultSlot)
    (depthLeft : a.target.stack.length + 1 + left.depth ≤ limit)
    (depthRight : a.target.stack.length + 1 + right.depth ≤ limit)
    (literalSite : ∀ source K L, LiteralSite p
      (consumed a destLeft next destRight continuation source K L) resultSlot n finish) :
    ∃ source K L, BodyResult (CommonCaseChildConsumption.graph n) 4 .scalar p limit
      ((1 + TreeDropCall.ticks left + 1) + (1 + TreeDropCall.ticks right + 1) + 2)
      a (CommonLiteralBody.out (consumed a destLeft next destRight continuation source K L)
        resultSlot n finish) (.scalar n)
      (left.source.owners.map Event.free ++ right.source.owners.map Event.free)
      (left.ids.map HeapLifecycle.Event.free ++ right.ids.map HeapLifecycle.Event.free) resultSlot := by
  have h : CommonContext [left, right] [] [] a.pending a.sf a.tf a.ctx a.env a.slots a.source a.target.frame := by
    simpa [Boundary.Valid, images, buffers, sizes] using valid
  obtain ⟨lookupLeft, middle, K, destroyLeft, runLeft, afterLeft⟩ :=
    drop_exact h (k := 1) (by rw [context]; rfl) installed siteLeft callLeft freshLeft depthLeft
  obtain ⟨lookupRight, final, L, destroyRight, runRight, afterRight⟩ :=
    drop_exact afterLeft (k := 0) (by rw [context]; rfl) installed (siteRight K) (callRight K)
      freshRight (by simpa [TreeDropCall.resume] using depthRight)
  let c := consumed a destLeft next destRight continuation final K L
  have cv : c.Valid := afterRight
  have transfer : Transfer p limit
      ((1 + TreeDropCall.ticks left + 1) + (1 + TreeDropCall.ticks right + 1)) a c
      (left.ids.map HeapLifecycle.Event.free ++ right.ids.map HeapLifecycle.Event.free) := by
    refine ⟨?_, fun _ => cv, rfl, rfl, rfl⟩
    rw [CommonDataCaseRelocation.walk_add, runLeft]
    simp [runRight, c, consumed]
  obtain ⟨fn, found, code, ext, start, ty, space, nextBound⟩ := literalSite final K L
  have literal := CommonLiteralBody.literal (g := CommonCaseChildConsumption.graph n) (term := 2)
    c fn rfl bound rfl rfl rfl cv freshResult found code ext start ty space nextBound
    (show c.target.stack.length ≤ limit from by change a.target.stack.length ≤ limit; omega)
  refine ⟨final, K, L, ?_, ?_, ?_, literal.post, literal.result⟩
  · simpa [images, sizes, context] using (CommonCaseChildConsumption.typed (ghosts := ghosts) (ctx := ctx) bound)
  · simpa using (CommonDataSourceExecution.Eval.drop (g := CommonCaseChildConsumption.graph n)
      (term := 4) rfl rfl lookupLeft destroyLeft
      (.drop (term := 3) rfl rfl lookupRight destroyRight literal.sourceRun))
  · simpa using transfer.then literal.transfer

end Jihoo.CommonCaseChildTransfer
