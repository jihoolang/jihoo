import Jihoo.SizedBufferHeap
import Jihoo.MirBufferHeap

/-! Exact representation of uniform read-only source buffers by MIR arrays.
Released objects retain their initialized contents and spare cell. Source lease
metadata has no MIR representation; this relation alone does not authorize a free
or establish validity of a source execution. -/
namespace Jihoo.SizedMir
open BoundedMir

/-- A represented object keeps its exact liveness, uniform logical contents and
one uninitialized allocator cell beyond its logical length. -/
def object (s : SizedBufferHeap.State) (j : Nat) : Object :=
  ⟨s.heap.live j, MirBuffer.cells (s.length j) (s.heap.payload j) (s.length j)⟩

structure HeapRel (s : SizedBufferHeap.State) (H : Array Object) : Prop where
  nextObject : s.heap.nextObject = H.size
  objects : ∀ j, j < H.size → H[j]? = some (object s j)

/-- The finite array represented by a source heap. This construction does not
assert that source identities beyond nextObject are valid or that leases are safe. -/
def materialize (s : SizedBufferHeap.State) : Array Object :=
  Array.ofFn (fun j : Fin s.heap.nextObject => object s j.val)

namespace HeapRel

theorem materialize_related (s : SizedBufferHeap.State) : HeapRel s (materialize s) := by
  constructor
  · simp [materialize]
  · intro j hj
    have bound : j < s.heap.nextObject := by simpa [materialize] using hj
    simp [materialize, bound]

theorem unique (left : HeapRel s H) (right : HeapRel s H') : H = H' := by
  apply Array.ext (left.nextObject.symm.trans right.nextObject)
  intro j hj hj'
  have one := left.objects j hj
  have two := right.objects j hj'
  simp only [getElem?_pos H j hj, getElem?_pos H' j hj', Option.some.injEq] at one two
  exact one.trans two.symm

theorem empty : HeapRel SizedBufferHeap.empty #[] := by
  constructor
  · rfl
  · simp

/-- Relating a completed source allocation requires the MIR initialization loop
already to have filled its logical cells. Raw malloc alone does not suffice. -/
theorem allocate (related : HeapRel s H) :
    HeapRel (SizedBufferHeap.allocate s n value)
      (H.push ⟨true, MirBuffer.cells n value n⟩) := by
  constructor
  · simpa [SizedBufferHeap.allocate] using congrArg Nat.succ related.nextObject
  · intro j hj
    have bound : j ≤ H.size := by simp only [Array.size_push] at hj; omega
    by_cases fresh : j = H.size
    · subst j
      simp [object, SizedBufferHeap.allocate, HeapLeases.put, related.nextObject]
    · have old : j < H.size := by omega
      rw [MirBuffer.heap_prefix_frame H old, related.objects j old]
      simp [object, SizedBufferHeap.allocate, HeapLeases.put, related.nextObject, fresh]

/-- Appending a new object preserves exact old objects, alive or released. -/
theorem allocation_frame (related : HeapRel s H) (old : j < H.size) :
    (H.push ⟨true, MirBuffer.cells n value n⟩)[j]? = some (object s j) := by
  rw [MirBuffer.heap_prefix_frame H old, related.objects j old]

theorem read (related : HeapRel s H) (old : j < H.size)
    (live : s.heap.live j = true) (bound : i < s.length j) :
    load H j i = some (s.heap.payload j) := by
  simp [load, related.objects j old, object, live,
    MirBuffer.cells_lookup (by omega : i < s.length j + 1), bound]

/-- The spare cell cannot be read, even for an otherwise live object. -/
theorem spare (related : HeapRel s H) (old : j < H.size) :
    load H j (s.length j) = none := by
  simp [load, related.objects j old, object, MirBuffer.cells]

theorem dead_unreadable (related : HeapRel s H) (old : j < H.size)
    (dead : s.heap.live j = false) : load H j i = none := by
  simp [load, related.objects j old, object, dead]

/-- A live represented object can be released by its base pointer. Source lease
and ownership preconditions must be established separately by its typing rules. -/
theorem free_heap (related : HeapRel s H) (old : j < H.size)
    (live : s.heap.live j = true) :
    freeHeap H j 0 = some (H.set! j { object s j with alive := false }) := by
  simp [freeHeap, related.objects j old, object, live]

/-- Source release and the corresponding MIR update retain exactly the same
contents and allocated identities, including the previously released objects. -/
theorem release (related : HeapRel s H) (old : j < H.size) :
    HeapRel (SizedBufferHeap.release s j) (H.set! j { object s j with alive := false }) := by
  constructor
  · simpa [SizedBufferHeap.release] using related.nextObject
  · intro k hk
    have bound : k < H.size := by simpa using hk
    by_cases same : k = j
    · subst k
      simp [Array.set!, Array.setIfInBounds, old, object, SizedBufferHeap.release, HeapLeases.put]
    · simp [Array.set!, Array.setIfInBounds, old,
        same, Ne.symm same, related.objects k bound, object, SizedBufferHeap.release, HeapLeases.put]

theorem release_frame {H : Array Object} (old : j < H.size)
    (other : k ≠ j) :
    (H.set! j { object s j with alive := false })[k]? = H[k]? := by
  simp [Array.set!, Array.setIfInBounds, old, Ne.symm other]

theorem double_free_rejected {H : Array Object} (old : j < H.size) :
    freeHeap (H.set! j { object s j with alive := false }) j 0 = none := by
  simp [freeHeap, Array.set!, Array.setIfInBounds, old]

theorem free_related (related : HeapRel s H) (old : j < H.size)
    (live : s.heap.live j = true) :
    ∃ H', freeHeap H j 0 = some H' ∧ HeapRel (SizedBufferHeap.release s j) H' :=
  ⟨_, related.free_heap old live, related.release old⟩

/-- Physical capacity counts every allocated identity, regardless of liveness. -/
theorem cell_sizes (related : HeapRel s H) :
    H.map (fun obj => obj.cells.size) =
      Array.ofFn (fun j : Fin s.heap.nextObject => s.length j.val + 1) := by
  apply Array.ext (by simp [related.nextObject])
  intro j hj hj'
  have bound : j < H.size := by simpa using hj
  have lookup : H[j] = object s j := by
    simpa only [getElem?_pos H j bound, Option.some.injEq] using related.objects j bound
  simp [lookup, object]

end HeapRel

/-- Includes the spare cell for every allocated object, even after release. -/
def cellCount (s : SizedBufferHeap.State) : Nat :=
  ((Array.ofFn (fun j : Fin s.heap.nextObject => s.length j.val + 1)).toList).sum

theorem HeapRel.cell_count (related : HeapRel s H) :
    (H.toList.map (fun obj => obj.cells.size)).sum = cellCount s := by
  rw [← Array.toList_map, related.cell_sizes]
  rfl

theorem cellCount_allocate (s : SizedBufferHeap.State) (n value : Nat) :
    cellCount (SizedBufferHeap.allocate s n value) = cellCount s + n + 1 := by
  have related := HeapRel.materialize_related s
  rw [← related.allocate.cell_count, MirBuffer.heap_prefix_cells_count, related.cell_count]

theorem cellCount_release (s : SizedBufferHeap.State) (j : Nat) :
    cellCount (SizedBufferHeap.release s j) = cellCount s := rfl

end Jihoo.SizedMir
