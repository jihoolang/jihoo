import Jihoo.BoundedMirRun

/-! Heap facts for allocation/fill fragments, independent of any particular CFG. -/
namespace Jihoo.MirBuffer
open BoundedMir
set_option linter.unusedSimpArgs false

/-- Exactly the first `k` cells have been initialized; allocation includes one
spare cell, which remains uninitialized when `k ≤ n`. -/
def cells (n value k : Nat) : Array (Option Nat) :=
  Array.ofFn fun j : Fin (n + 1) => if j.val < k then some value else none

@[simp] theorem cells_size : (cells n value k).size = n + 1 := by simp [cells]

@[simp] theorem cells_lookup (hj : j < n + 1) :
    (cells n value k)[j]? = some (if j < k then some value else none) := by
  simp [cells, hj]

theorem cells_zero : cells n value 0 = Array.replicate (n + 1) none := by
  ext j hj <;> simp [cells]

theorem cells_store (hk : k < n) :
    (cells n value k).set! k (some value) = cells n value (k + 1) := by
  have hk' : k < n + 1 := by omega
  apply Array.ext
  · simp
  · intro j hj hj'
    simp only [Array.set!, Array.setIfInBounds]
    simp only [cells_size, hk', dite_true]
    simp only [Array.getElem_set]
    simp only [cells, Array.getElem_ofFn]
    by_cases h : j = k
    · subst j; simp
    · have he : (j < k + 1) = (j < k) := propext (by omega)
      simp [h, Ne.symm h, he]

theorem cells_set (hk : k < n) (h : k < (cells n value k).size) :
    (cells n value k).set k (some value) h = cells n value (k + 1) := by
  simpa only [Array.set!, Array.setIfInBounds, h, dite_true] using cells_store (value := value) hk

/-- Allocation is allowed after any prior heap satisfying the cumulative limits. -/
theorem malloc_heap (H : Array Object) (hobjects : H.size < 512)
    (hcells : (H.toList.map (fun obj => obj.cells.size)).sum + n + 1 ≤ 4096) :
    mallocHeap H (n * 8 + 8) = some (H.push ⟨true, cells n value 0⟩) := by
  have positive : 0 < n * 8 + 8 := by omega
  have aligned : (n * 8 + 8) % 8 = 0 := by omega
  have bytes : n * 8 + 8 ≤ 32768 := by omega
  have div : (n * 8 + 8) / 8 = n + 1 := by omega
  simp [mallocHeap, positive, aligned, bytes, div, hobjects, cells_zero,
    Nat.add_assoc] at *
  exact hcells

@[simp] theorem heap_prefix_lookup (H : Array Object) :
    (H.push ⟨true, cells n value k⟩)[H.size]? = some ⟨true, cells n value k⟩ := by
  simp

/-- A prefix store changes only the appended allocation. -/
theorem heap_store_prefix (H : Array Object) (hk : k < n) :
    (H.push ⟨true, cells n value k⟩).set! H.size
      ⟨true, (cells n value k).set! k (some value)⟩ =
      H.push ⟨true, cells n value (k + 1)⟩ := by
  rw [cells_store hk]
  simp [Array.set!, Array.setIfInBounds, Array.set_push]

/-- A dereferencing MIR assignment fills the next cell, independently of the
code and of every unrelated local or earlier heap object. -/
theorem write_prefix (c : Code) (f : Frame) (H : Array Object)
    (htype : c.locals[slot]? = some .ptr)
    (hpointer : f.locals[slot]? = some (some (.pointer H.size k)))
    (hheap : f.heap = H.push ⟨true, cells n value k⟩)
    (hk : k < n) (hv : value < scalarBound) :
    write c f ⟨slot, true⟩ (.i64 value) =
      some { f with heap := H.push ⟨true, cells n value (k + 1)⟩ } := by
  have hk' : k < n + 1 := by omega
  simp [write, htype, hpointer, hheap, hk', hv]
  simpa only [Array.set!] using heap_store_prefix H hk

/-- Every prior object is preserved, including its liveness and all cells. -/
theorem heap_prefix_frame (H : Array Object) (hj : j < H.size) :
    (H.push ⟨alive, cells n value k⟩)[j]? = H[j]? := by
  simp [Array.getElem?_push, hj, Nat.ne_of_lt hj]

theorem heap_prefix_load_frame (H : Array Object) (hj : j < H.size) :
    load (H.push ⟨alive, cells n value k⟩) j index = load H j index := by
  simp only [load, heap_prefix_frame H hj]

theorem prefix_read (H : Array Object) (hk : k ≤ n) (hi : i < k) :
    load (H.push ⟨true, cells n value k⟩) H.size i = some value := by
  simp [load, cells_lookup (by omega : i < n + 1), hi]

theorem filled_read (H : Array Object) (hi : i < n) :
    load (H.push ⟨true, cells n value n⟩) H.size i = some value :=
  prefix_read H (Nat.le_refl n) hi

theorem suffix_uninitialized (H : Array Object) (hk : k ≤ i) (hi : i ≤ n) :
    load (H.push ⟨true, cells n value k⟩) H.size i = none := by
  simp [load, cells_lookup (by omega : i < n + 1), Nat.not_lt_of_ge hk]

theorem spare_uninitialized (H : Array Object) (hk : k ≤ n) :
    load (H.push ⟨true, cells n value k⟩) H.size n = none :=
  suffix_uninitialized H hk (Nat.le_refl n)

@[simp] theorem heap_prefix_cells_count (H : Array Object) :
    ((H.push ⟨alive, cells n value k⟩).toList.map (fun obj => obj.cells.size)).sum =
      (H.toList.map (fun obj => obj.cells.size)).sum + n + 1 := by
  simp [Nat.add_assoc]

/-- Freeing the new object keeps both the prior heap and the initialized cells. -/
theorem free_prefix (H : Array Object) :
    freeHeap (H.push ⟨true, cells n value k⟩) H.size 0 =
      some (H.push ⟨false, cells n value k⟩) := by
  simp [freeHeap, Array.set!, Array.setIfInBounds, Array.set_push]

end Jihoo.MirBuffer
