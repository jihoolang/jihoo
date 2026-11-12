import Jihoo.TreeCreateCfg

/-! Resource bridge for the concrete instruction prefixes. No malloc/store
success premise is used. Children may be arbitrary finite Image witnesses. -/
set_option linter.unusedSimpArgs false
namespace Jihoo.TreeCreateCfg
open ReferenceCfg ReferenceCalls CommonDataReference
open HeapLeases LinearHeapPrograms OwnedCoreContinuation RecursiveFieldOwnership RecursiveFieldRuntime

def nilResult (fn : Nat) (H : ReferenceHeap.Heap) (b c d e : Option Value)
    (vs : Array (Option Value)) (ks : List Continuation) : ReferenceCalls.State :=
  stateAt fn 2 (H.push ReferenceHeap.nilObject)
    (slots (some (.pointer H.size 0)) b c d e vs) ks

def nodeResult (fn : Nat) (H : ReferenceHeap.Heap) (l r : Nat)
    (vs : Array (Option Value)) (ks : List Continuation) : ReferenceCalls.State :=
  stateAt fn 2 (H.push (ReferenceHeap.node (.object l 0) (.object r 0)))
    (slots (some (.pointer H.size 0)) (some (.pointer H.size 2))
      (some (.referenceWord (.object r 0))) (some (.pointer l 0)) (some (.pointer r 0)) vs) ks

/-- The source stutters while the target allocates exactly one 8-byte object. -/
theorem nil_total (installed : p[fn]? = some (body false tys continuation exit))
    (capacity : Budget H 1) (s : CommonData.State) :
    Prefix p 3 (stateAt fn 0 H (slots a b c d e vs) ks) [.alloc H.size 8]
      (nilResult fn H b c d e vs ks) ∧
    Related s (nilResult fn H b c d e vs ks).frame.heap (.nil H.size) ∧
    ReferenceHeap.loadScalar (nilResult fn H b c d e vs ks).frame.heap (.object H.size 0) = some 0 ∧
    (∀ j < H.size, (nilResult fn H b c d e vs ks).frame.heap[j]? = H[j]?) := by
  obtain ⟨_, related, frame⟩ := empty_total s capacity
  exact ⟨walk_sound (nil_prefix installed capacity), related, tag_total related.layout, frame⟩

/-- Joint ownership and distinct target children are preconditions; allocator
success and all stores are conclusions of node_prefix and allocate_total. -/
theorem node_total (installed : p[fn]? = some (body true tys continuation exit))
    (valid : Valid s.buffers.heap)
    (lf : Represents s.cells l.source) (rf : Represents s.cells r.source)
    (owned : Owns s.buffers.heap (l.source.owners ++ r.source.owners ++ frame))
    (ll : Layout H l) (rl : Layout H r) (separate : (l.ids ++ r.ids).Nodup)
    (capacity : Budget H 3) :
    let t := CommonData.allocate s (root l.source) (root r.source)
    let out := nodeResult fn H l.target r.target vs ks
    Prefix p 9 (stateAt fn 0 H
      (slots a b c (some (.pointer l.target 0)) (some (.pointer r.target 0)) vs) ks)
      [.alloc H.size 24] out ∧
    Related t out.frame.heap (.node s.buffers.heap.nextObject H.size l r) ∧
    Valid t.buffers.heap ∧
    Owns t.buffers.heap ((Tree.node s.buffers.heap.nextObject l.source r.source).owners ++ frame) ∧
    ReferenceHeap.loadScalar out.frame.heap (.object H.size 0) = some 1 ∧
    ReferenceHeap.loadRef out.frame.heap (.object H.size 1) = some (.object l.target 0) ∧
    ReferenceHeap.loadRef out.frame.heap (.object H.size 2) = some (.object r.target 0) ∧
    (∀ j < H.size, out.frame.heap[j]? = H[j]?) := by
  obtain ⟨_, related, vt, ot, external⟩ :=
    allocate_total valid lf rf owned ll rl separate capacity
  exact ⟨walk_sound (node_prefix installed capacity), related, vt, ot,
    tag_total related.layout, (children_total related.layout).1,
    (children_total related.layout).2, external⟩

/-- Independently retained trees and buffers survive Nil with unchanged source. -/
theorem nil_retained (tree : Related s H i) (buffer : BufferRelated s H x j) :
    Related s (nilResult fn H b c d e vs ks).frame.heap i ∧
    BufferRelated s (nilResult fn H b c d e vs ks).frame.heap x j :=
  ⟨tree.push _, buffer.push _⟩

/-- Retained source allocation facts use validity; no disjointness from fresh
identities is assumed because freshness follows from validity and heap bounds. -/
theorem node_retained (valid : Valid s.buffers.heap)
    (tree : Related s H i) (buffer : BufferRelated s H x j) :
    Related (CommonData.allocate s left right) (nodeResult fn H l r vs ks).frame.heap i ∧
    BufferRelated (CommonData.allocate s left right) (nodeResult fn H l r vs ks).frame.heap x j :=
  ⟨tree.allocate valid _, buffer.allocate valid _⟩

theorem nil_result_pointer :
    ((nilResult fn H b c d e vs ks).frame.locals[0]?).join = some (.pointer H.size 0) := by
  simp [nilResult, stateAt, slots, Array.getElem?_append]
theorem node_result_pointer :
    ((nodeResult fn H l r vs ks).frame.locals[0]?).join = some (.pointer H.size 0) := by
  simp [nodeResult, stateAt, slots, Array.getElem?_append]

theorem nil_stack : (nilResult fn H b c d e vs ks).stack = ks := rfl
theorem node_stack : (nodeResult fn H l r vs ks).stack = ks := rfl

theorem nil_locals (nonResult : k ≠ 0) :
    (nilResult fn H b c d e vs ks).frame.locals[k]? = (slots a b c d e vs)[k]? := by
  by_cases h : k < 5
  · have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;>
      simp_all [nilResult, nodeResult, stateAt, slots, Array.getElem?_append]
  · simp [nilResult, nodeResult, stateAt, slots, Array.getElem?_append, h]

theorem node_locals (outside : 3 ≤ k) :
    (nodeResult fn H l r vs ks).frame.locals[k]? =
      (slots a b c (some (.pointer l 0)) (some (.pointer r 0)) vs)[k]? := by
  by_cases h : k < 5
  · have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;>
      simp_all [nilResult, nodeResult, stateAt, slots, Array.getElem?_append]
  · simp [nilResult, nodeResult, stateAt, slots, Array.getElem?_append, h]

/-- Scratch/operand conflicts are ruled out by the calling convention, not
silently tolerated. Integration must put children in 3/4 before entering 0. -/
theorem operand_scratch_disjoint :
    ∀ child ∈ [3, 4], ∀ destination ∈ [0, 1, 2], child ≠ destination := by decide

/-- Source Nil costs zero allocations; boxed target Nil costs one object/word.
A Node adds one source owner, one target object and three target words. -/
theorem allocation_accounting (s : CommonData.State) (H : ReferenceHeap.Heap) :
    (Image.nil H.size).source.owners.length = 0 ∧
    (H.push ReferenceHeap.nilObject).size = H.size + 1 ∧
    ((H.push ReferenceHeap.nilObject).toList.map (fun o => o.cells.size)).sum =
      (H.toList.map (fun o => o.cells.size)).sum + 1 ∧
    (CommonData.allocate s left right).buffers.heap.nextObject = s.buffers.heap.nextObject + 1 ∧
    (H.push (ReferenceHeap.node l r)).size = H.size + 1 ∧
    ((H.push (ReferenceHeap.node l r)).toList.map (fun o => o.cells.size)).sum =
      (H.toList.map (fun o => o.cells.size)).sum + 3 := by
  simp [Image.source, Tree.owners, ReferenceHeap.nilObject, ReferenceHeap.node,
    CommonData.allocate, allocatedState]

end Jihoo.TreeCreateCfg
