import Jihoo.TreeCreateRelocation

namespace Jihoo.TreeCreateRelocation
open ReferenceCfg ReferenceCalls CommonDataReference TreeCreateCfg
open HeapLeases LinearHeapPrograms OwnedCoreContinuation RecursiveFieldOwnership RecursiveFieldRuntime

/-- The exact write footprint; every other caller local is unchanged, including
source operands that lie outside the scratch/child/result destination set. -/
theorem locals_preserved (outside : k ∉ q.writes) :
    (resultLocals q vs H l r)[k]? = vs[k]? := by
  simp only [Slots.writes, List.mem_cons,
    List.not_mem_nil, not_false_eq_true, not_or, and_true] at outside
  simp only [resultLocals, copied, Array.set!_eq_setIfInBounds]
  simp [Ne.symm outside.1, Ne.symm outside.2.1, Ne.symm outside.2.2.1,
    Ne.symm outside.2.2.2.1, Ne.symm outside.2.2.2.2.1,
    Ne.symm outside.2.2.2.2.2.1, Ne.symm outside.2.2.2.2.2.2]

theorem nil_locals_preserved (q : Slots) (vs : Array (Option Value))
    (H : ReferenceHeap.Heap) (outside : k ≠ q.result) :
    (vs.set! q.result (some (.pointer H.size 0)))[k]? = vs[k]? := by
  simp [Ne.symm outside]

def nilOut (q : Slots) (fn cont : Nat) (H : ReferenceHeap.Heap)
    (vs : Array (Option Value)) (ks : List Continuation) : ReferenceCalls.State :=
  stateAt fn cont (H.push ReferenceHeap.nilObject)
    (vs.set! q.result (some (.pointer H.size 0))) ks

def nodeOut (q : Slots) (fn cont : Nat) (H : ReferenceHeap.Heap) (l r : Nat)
    (vs : Array (Option Value)) (ks : List Continuation) : ReferenceCalls.State :=
  stateAt fn cont (H.push (ReferenceHeap.node (.object l 0) (.object r 0)))
    (resultLocals q vs H l r) ks

/-- A local result contract, deliberately separate from any return ABI. -/
theorem node_result_pointer (safe : Safe f q vs left right) :
    ((nodeOut q fn cont H l r vs ks).frame.locals[q.result]?).join =
      some (.pointer H.size 0) := by
  have hd := safe.distinct
  simp [Slots.writes] at hd
  have da : q.address ≠ q.result := by omega
  have dw : q.word ≠ q.result := by omega
  have br := safe.bounds q.result (by simp [Slots.writes])
  simp [nodeOut, stateAt, resultLocals, copied, da, dw, br]

theorem nil_result_pointer (bound : q.result < vs.size) :
    ((nilOut q fn cont H vs ks).frame.locals[q.result]?).join = some (.pointer H.size 0) := by
  simp [nilOut, stateAt, Array.set!, Array.setIfInBounds, bound]

theorem stack_preserved :
    (nilOut q fn cont H vs ks).stack = ks ∧
    (nodeOut q fn cont H l r vs ks).stack = ks := ⟨rfl, rfl⟩

theorem heap_preserved (old : j < H.size) :
    (nilOut q fn cont H vs ks).frame.heap[j]? = H[j]? ∧
    (nodeOut q fn cont H l r vs ks).frame.heap[j]? = H[j]? := by
  simp [nilOut, nodeOut, stateAt, Array.getElem?_push, old, Nat.ne_of_lt old]

/-- Source Nil stutters. Its target representation still consumes one object
and one cell; these are executable allocator bounds, not success premises. -/
theorem nil_total (installed : p[fn]? = some f)
    (place : Placement f q false left right start work cont)
    (resultType : f.code.base.locals[q.result]? = some .ptr)
    (resultBound : q.result < vs.size) (capacity : Budget H 1) (s : CommonData.State) :
    Prefix p 3 (stateAt fn start H vs ks) [.alloc H.size 8] (nilOut q fn cont H vs ks) ∧
    Related s (nilOut q fn cont H vs ks).frame.heap (.nil H.size) := by
  obtain ⟨_, related, _⟩ := empty_total s capacity
  exact ⟨walk_sound (nil_prefix installed place resultType resultBound capacity), related⟩

/-- The ownership/layout bridge is intentionally stronger than raw transport.
Dangling/null/shared child values do not establish these premises. -/
theorem node_total (installed : p[fn]? = some f)
    (place : Placement f q true left right start work cont)
    (safe : Safe f q vs left right)
    (hl : (vs[left]?).join = some (.pointer l.target 0))
    (hr : (vs[right]?).join = some (.pointer r.target 0))
    (valid : Valid s.buffers.heap)
    (lf : Represents s.cells l.source) (rf : Represents s.cells r.source)
    (owned : Owns s.buffers.heap (l.source.owners ++ r.source.owners ++ frame))
    (ll : Layout H l) (rl : Layout H r) (separate : (l.ids ++ r.ids).Nodup)
    (capacity : Budget H 3) :
    let t := CommonData.allocate s (root l.source) (root r.source)
    let out := nodeOut q fn cont H l.target r.target vs ks
    Prefix p 13 (stateAt fn start H vs ks) [.alloc H.size 24] out ∧
    Related t out.frame.heap (.node s.buffers.heap.nextObject H.size l r) ∧
    Valid t.buffers.heap ∧
    Owns t.buffers.heap ((Tree.node s.buffers.heap.nextObject l.source r.source).owners ++ frame) ∧
    ReferenceHeap.loadScalar out.frame.heap (.object H.size 0) = some 1 ∧
    ReferenceHeap.loadRef out.frame.heap (.object H.size 1) = some (.object l.target 0) ∧
    ReferenceHeap.loadRef out.frame.heap (.object H.size 2) = some (.object r.target 0) := by
  obtain ⟨_, related, vt, ot, _⟩ := allocate_total valid lf rf owned ll rl separate capacity
  exact ⟨walk_sound (node_prefix installed place safe hl hr capacity), related, vt, ot,
    tag_total related.layout, (children_total related.layout).1, (children_total related.layout).2⟩

theorem nil_retained (tree : Related s H i) (buffer : BufferRelated s H x j) :
    Related s (nilOut q fn cont H vs ks).frame.heap i ∧
    BufferRelated s (nilOut q fn cont H vs ks).frame.heap x j :=
  ⟨tree.push _, buffer.push _⟩

theorem node_retained (valid : Valid s.buffers.heap)
    (tree : Related s H i) (buffer : BufferRelated s H x j) :
    Related (CommonData.allocate s left right) (nodeOut q fn cont H l r vs ks).frame.heap i ∧
    BufferRelated (CommonData.allocate s left right) (nodeOut q fn cont H l r vs ks).frame.heap x j :=
  ⟨tree.allocate valid _, buffer.allocate valid _⟩

/-- Includes all four copies, malloc, seven stores/conversions, and goto.
Continuation success remains a separate premise; pointer return is not modeled. -/
theorem node_fuel (installed : p[fn]? = some f)
    (place : Placement f q true left right start work cont)
    (safe : Safe f q vs left right)
    (hl : (vs[left]?).join = some (.pointer l 0))
    (hr : (vs[right]?).join = some (.pointer r 0)) (capacity : Budget H 3) :
    (∀ fuel ≤ 13, ReferenceCalls.execute fuel p (stateAt fn start H vs ks) = none) ∧
    (∀ fuel out, ReferenceCalls.execute fuel p (nodeOut q fn cont H l r vs ks) = some out →
      ReferenceCalls.execute (13 + fuel) p (stateAt fn start H vs ks) =
        some {out with events := [.alloc H.size 24] ++ out.events}) ∧
    ReferenceCalls.Steps p (.running (stateAt fn start H vs ks)) [.alloc H.size 24]
      (.running (nodeOut q fn cont H l r vs ks)) := by
  have h := walk_sound (node_prefix installed place safe hl hr capacity (ks := ks))
  exact ⟨fun _ bound => h.short_fuel bound, fun _ _ tail => h.execute tail, h.steps⟩

theorem nil_fuel (installed : p[fn]? = some f)
    (place : Placement f q false left right start work cont)
    (resultType : f.code.base.locals[q.result]? = some .ptr)
    (resultBound : q.result < vs.size) (capacity : Budget H 1) :
    (∀ fuel ≤ 3, ReferenceCalls.execute fuel p (stateAt fn start H vs ks) = none) ∧
    (∀ fuel out, ReferenceCalls.execute fuel p (nilOut q fn cont H vs ks) = some out →
      ReferenceCalls.execute (3 + fuel) p (stateAt fn start H vs ks) =
        some {out with events := [.alloc H.size 8] ++ out.events}) := by
  have h := walk_sound (nil_prefix installed place resultType resultBound capacity (ks := ks))
  exact ⟨fun _ bound => h.short_fuel bound, fun _ _ tail => h.execute tail⟩

end Jihoo.TreeCreateRelocation
