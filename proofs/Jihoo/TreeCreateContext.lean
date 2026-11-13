import Jihoo.CommonDataTargetContext
import Jihoo.TreeCreateRelocationCorrectness

/-! Constructor prefixes at the common resource boundary. No continuation,
return ABI, native allocator, or whole-program correctness is asserted. -/
set_option maxHeartbeats 200000
namespace Jihoo.TreeCreateContext
open CommonDataTargetContext CommonDataReference TreeCreateRelocation TreeCreateCfg
open RecursiveLexicalFields RecursiveFieldRuntime RecursiveFieldOwnership
open HeapLeases LinearHeapPrograms OwnedCoreContinuation
variable {slots : List Nat} {li ri : Nat}

/-- Every surviving lexical value (including scalars) avoids the write set.
Consumed aliases are dead and may occupy operand/scratch destinations. -/
def Preserved (ctx : List Entry) (slots writes : List Nat) : Prop :=
  ∀ (k : Nat) e slot, ctx[k]? = some e → slots[k]? = some slot → Active e → slot ∉ writes

theorem Binding.transport (h : Binding rs f e slot)
    (same : Active e → g.locals[slot]? = f.locals[slot]?) : Binding rs g e slot := by
  cases e with
  | data k => obtain ⟨i, hi, hv⟩ := h; exact ⟨i, hi, (same trivial).trans hv⟩
  | buffer k => obtain ⟨x, j, hi, hv⟩ := h; exact ⟨x, j, hi, (same trivial).trans hv⟩
  | nat n => exact (same trivial).trans h
  | scalar => obtain ⟨n, hv⟩ := h; exact ⟨n, (same trivial).trans hv⟩
  | ghost | dead => trivial

theorem Bindings.transport (h : Bindings rs f ctx slots)
    (fresh : Preserved ctx slots writes)
    (same : ∀ slot, slot ∉ writes → g.locals[slot]? = f.locals[slot]?) :
    Bindings rs g ctx slots := by
  induction h with
  | nil => exact .nil
  | @cons e slot ctx slots head tail ih =>
    exact .cons (Binding.transport head (fun active => same slot (fresh 0 e slot rfl rfl active)))
      (ih (fun k e slot he hs => fresh (k+1) e slot he hs))

private theorem local_of_join (h : (f.locals[slot]?).join = some v) : Local f slot v := by
  cases he : f.locals[slot]? with
  | none => simp [he] at h
  | some a => cases a <;> simp_all [Local]

theorem node_frame_local (q : Slots) (fn start cont : Nat) (H : ReferenceHeap.Heap)
    (vs : Array (Option ReferenceCfg.Value)) (ks : List ReferenceCalls.Continuation)
    (l r slot : Nat) (outside : slot ∉ q.writes) :
    (nodeOut q fn cont H l r vs ks).frame.locals[slot]? =
      (stateAt fn start H vs ks).frame.locals[slot]? := by
  simp only [nodeOut, stateAt]
  exact TreeCreateRelocation.locals_preserved (q := q) (vs := vs) (H := H) (l := l) (r := r) (k := slot) outside

/-- Derive actual copy operands and joint child separation from one inventory.
Even two source Nil values require distinct target boxes. -/
theorem operands
    (h : CommonContext (l :: r :: images) buffers sizes pending sf tf ctx env slots source f)
    (left : ctx[li]? = some (.data 0)) (right : ctx[ri]? = some (.data 1)) :
    ∃ ls rs, slots[li]? = some ls ∧ slots[ri]? = some rs ∧
      Local f ls (.pointer l.target 0) ∧ Local f rs (.pointer r.target 0) ∧
      env[li]? = some (.data (root l.source)) ∧ env[ri]? = some (.data (root r.source)) ∧
      (l.ids ++ r.ids).Nodup := by
  obtain ⟨ls, hls, a, ha, hl⟩ := h.bindings.lookup left
  obtain ⟨rs, hrs, b, hb, hr⟩ := h.bindings.lookup right
  have ea : a = l := by simpa [inventory] using ha.symm
  have eb : b = r := by simpa [inventory] using hb.symm
  subst a; subst b
  refine ⟨ls, rs, hls, hrs, hl, hr, ?_, ?_, ?_⟩
  · exact CommonData.data_lookup h.agreement left rfl
  · exact CommonData.data_lookup h.agreement right rfl
  · have sep : ((l.ids ++ r.ids) ++ (targets (inventory images buffers) ++
        (pending.map Pending.target ++ tf))).Nodup := by
      simpa [inventory, targets, Resource.ids, List.append_assoc] using h.separated
    exact (List.nodup_append.mp sep).1

/-- Prefix plus complete common inventory transition. Target freshness against
ambient reservations is explicit: Context permits absent external target IDs.
The child ownership, layouts, operands and separation are derived from h. -/
theorem node_prefix_context
    (h : CommonContext (l :: r :: images) buffers sizes pending sf tf ctx env slots source
      (stateAt fn start H vs ks).frame)
    (left : ctx[li]? = some (.data 0)) (right : ctx[ri]? = some (.data 1))
    (leftSlot : slots[li]? = some ls) (rightSlot : slots[ri]? = some rs)
    (installed : p[fn]? = some f) (place : Placement f q true ls rs start work cont)
    (safe : Safe f q vs ls rs) (capacity : Budget H 3)
    (fresh : Preserved (ctx.map (CommonData.capturedEntry 2 images.length 0)) slots q.writes)
    (reserved : H.size ∉ targets (inventory (l :: r :: images) buffers) ++
      (pending.map Pending.target ++ tf)) :
    let result := Image.node source.buffers.heap.nextObject H.size l r
    let middle := CommonData.allocate source (root l.source) (root r.source)
    let out := nodeOut q fn cont H l.target r.target vs ks
    Prefix p 13 (stateAt fn start H vs ks) [.alloc H.size 24] out ∧
    CommonContext (result :: images) buffers sizes pending sf tf
      (CommonData.capturedContext 2 images.length 0 ctx)
      (.data (root result.source) :: env) (q.result :: slots) middle out.frame := by
  obtain ⟨a, b, ha, hb, hl, hr, _, _, separate⟩ := operands h left right
  have ea : a = ls := Option.some.inj (ha.symm.trans leftSlot)
  have eb : b = rs := Option.some.inj (hb.symm.trans rightSlot)
  subst a; subst b
  have lr : Related source H l := h.resources (.data l) (by simp [inventory])
  have rr : Related source H r := h.resources (.data r) (by simp [inventory])
  have own : Owns source.buffers.heap (l.source.owners ++ r.source.owners ++
      (footprint (sources (inventory images buffers)) ++ (pending.map Pending.source ++ sf))) := by
    simpa [inventory, sources, footprint, Resource.source, Capability.owners, List.append_assoc] using h.owned
  have hjl : (vs[ls]?).join = some (.pointer l.target 0) := by rw [show vs[ls]? = _ from hl]; rfl
  have hjr : (vs[rs]?).join = some (.pointer r.target 0) := by rw [show vs[rs]? = _ from hr]; rfl
  obtain ⟨run, rel, valid, owned, _⟩ := TreeCreateRelocation.node_total installed place safe
    hjl hjr h.valid lr.fields rr.fields own lr.layout rr.layout separate capacity
  refine ⟨run, ⟨valid, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have agreement := CommonData.agrees_captured (active := [l.source, r.source])
      (retained := images.map Image.source) (used := []) (saved := buffers.map Prod.fst)
      (result := (Image.node source.buffers.heap.nextObject H.size l r).source)
      (by simpa [sources_inventory] using h.agreement)
    simpa [sources_inventory] using agreement
  · have old : Bindings (inventory (Image.node source.buffers.heap.nextObject H.size l r :: images) buffers)
        (stateAt fn start H vs ks).frame (ctx.map (CommonData.capturedEntry 2 images.length 0)) slots :=
      h.bindings.map (fun _ _ hb => Binding.captured
      (result := Image.node source.buffers.heap.nextObject H.size l r)
      (active := [l,r]) (retained := images) (used := []) (saved := buffers) hb)
    have kept := Bindings.transport (f := (stateAt fn start H vs ks).frame) (writes := q.writes) (g := (nodeOut q fn cont H l.target r.target vs ks).frame) old fresh
      (node_frame_local q fn start cont H vs ks l.target r.target)
    exact .cons ⟨_, rfl, local_of_join (f := (nodeOut q fn cont H l.target r.target vs ks).frame)
      (TreeCreateRelocation.node_result_pointer (fn := fn) (cont := cont) (H := H)
        (l := l.target) (r := r.target) (ks := ks) safe)⟩ kept
  · intro resource member
    simp only [inventory, List.map_cons, List.cons_append, List.mem_cons] at member
    rcases member with rfl | member
    · exact rel
    · have kept := h.resources resource (by simpa [inventory] using Or.inr (Or.inr member))
      cases resource with
      | data i => exact kept.allocate h.valid _
      | buffer x j => exact kept.allocate h.valid _
  · simpa [inventory, sources, footprint, Resource.source, Capability.owners, Image.source,
      List.append_assoc] using owned
  · have sep := List.nodup_cons.mpr ⟨reserved, h.separated⟩
    simpa [inventory, targets, Resource.ids, Image.ids, List.append_assoc] using sep
  · intro shell member
    obtain ⟨live, obj, alive⟩ := h.shells shell member
    have bound := h.valid.allocated shell.source live
    have targetBound : shell.target < H.size := (Array.getElem_of_getElem? obj).1
    refine ⟨?_, ?_, alive⟩
    · simpa [CommonData.allocate, allocatedState, put, Nat.ne_of_lt bound] using live
    · simpa [nodeOut, stateAt, Array.getElem?_push, targetBound, Nat.ne_of_lt targetBound] using obj
  · exact ⟨h.bufferSizes.length, h.bufferSizes.lookup⟩

/-- Boxed Nil extends the inventory without source allocation or alias consumption. -/
theorem nil_prefix_context
    (h : CommonContext images buffers sizes pending sf tf ctx env slots source
      (stateAt fn start H vs ks).frame)
    (installed : p[fn]? = some f) (place : Placement f q false ls rs start work cont)
    (resultType : f.code.base.locals[q.result]? = some .ptr)
    (resultBound : q.result < vs.size) (capacity : Budget H 1)
    (fresh : Preserved (ctx.map (CommonData.capturedEntry 0 images.length 0)) slots [q.result])
    (reserved : H.size ∉ targets (inventory images buffers) ++ (pending.map Pending.target ++ tf)) :
    Prefix p 3 (stateAt fn start H vs ks) [.alloc H.size 8] (nilOut q fn cont H vs ks) ∧
    CommonContext (.nil H.size :: images) buffers sizes pending sf tf
      (CommonData.capturedContext 0 images.length 0 ctx) (.data none :: env)
      (q.result :: slots) source (nilOut q fn cont H vs ks).frame := by
  obtain ⟨run, rel⟩ := TreeCreateRelocation.nil_total installed place resultType resultBound capacity source
  refine ⟨run, ⟨h.valid, ?_, ?_, ?_, ?_, ?_, ?_⟩, h.bufferSizes⟩
  · have agreement := CommonData.agrees_captured (active := [])
      (retained := images.map Image.source) (used := []) (saved := buffers.map Prod.fst)
      (result := Tree.empty) (by simpa [sources_inventory] using h.agreement)
    simpa [sources_inventory, Image.source, root] using agreement
  · have old := h.bindings.map (fun _ _ hb => Binding.captured (result := .nil H.size)
      (active := []) (retained := images) (used := []) (saved := buffers) hb)
    have kept := Bindings.transport (f := (stateAt fn start H vs ks).frame) (writes := [q.result]) (g := (nilOut q fn cont H vs ks).frame) old fresh (by
      intro slot outside
      exact TreeCreateRelocation.nil_locals_preserved q vs H (by simpa using outside))
    exact .cons ⟨_, rfl, local_of_join (f := (nilOut q fn cont H vs ks).frame)
      (TreeCreateRelocation.nil_result_pointer (fn := fn) (cont := cont) (H := H) (ks := ks) resultBound)⟩ kept
  · intro resource member
    simp only [inventory, List.map_cons, List.cons_append, List.mem_cons] at member
    rcases member with rfl | member
    · exact rel
    · have kept := h.resources resource member
      cases resource with
      | data i => exact kept.push _
      | buffer x j => exact kept.push _
  · simpa [inventory, sources, footprint, Resource.source, Capability.owners, Image.source, Tree.owners] using h.owned
  · simpa [inventory, targets, Resource.ids, Image.ids] using List.nodup_cons.mpr ⟨reserved, h.separated⟩
  · intro shell member
    obtain ⟨live, obj, alive⟩ := h.shells shell member
    have bound : shell.target < H.size := (Array.getElem_of_getElem? obj).1
    exact ⟨live, by simpa [nilOut, stateAt, Array.getElem?_push, bound, Nat.ne_of_lt bound] using obj, alive⟩

/-- The common constructor typing rule fixes operand order independently of
physical local placement. It has no continuation premise. -/
theorem typing_construct
    (typed : CommonData.Typing g ctx count sizes term kind)
    (shape : CommonData.nodeAt g term = .construct left right)
    (leftShape : CommonData.nodeAt g left = .core (.var li))
    (rightShape : CommonData.nodeAt g right = .core (.var ri)) :
    ctx[li]? = some (.data 0) ∧ ctx[ri]? = some (.data 1) := by
  cases typed <;> simp_all

/-- Source construction uses the same selected values as the target prefix;
source allocation events deliberately differ from byte-sized target events. -/
theorem source_construct
    (h : CommonContext (l :: r :: images) buffers sizes pending sf tf ctx env slots source f)
    (selectedLeft : ctx[li]? = some (.data 0)) (selectedRight : ctx[ri]? = some (.data 1))
    (shape : CommonData.nodeAt g term = .construct left right)
    (leftShape : CommonData.nodeAt g left = .core (.var li))
    (rightShape : CommonData.nodeAt g right = .core (.var ri)) :
    CommonData.Eval g env term source (.data (some source.buffers.heap.nextObject))
      [.alloc source.buffers.heap.nextObject 0]
      (CommonData.allocate source (root l.source) (root r.source)) := by
  obtain ⟨_, _, _, _, _, _, hl, hr, _⟩ := operands h selectedLeft selectedRight
  exact .construct shape leftShape hl rightShape hr

end Jihoo.TreeCreateContext
