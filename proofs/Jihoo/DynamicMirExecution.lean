import Jihoo.DynamicMir
import Jihoo.BoundedMirRun

namespace Jihoo.DynamicMir
open BoundedMir
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- The first k cells hold the payload. The spare allocator cell and the
remaining logical cells are still uninitialized. -/
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

def inputs (n i value : Nat) : Frame :=
  ⟨0, 0, #[none, some (.u64 n), some (.u64 i), some (.i64 value),
      none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], #[]⟩

def loop (n i value k : Nat) (test dest : Option Value) : Frame :=
  ⟨3, 0, #[none, some (.u64 n), some (.u64 i), some (.i64 value),
      some (.u64 (n * 8)), some (.u64 (n * 8 + 8)), some (.pointer 0 0),
      some (.address 0), some (.boolean true), some (.u64 k), test, dest,
      none, none, none, none, none, none, none], #[⟨true, cells n value k⟩]⟩

/-- Symbolic instruction reduction of the fixed prefix, not enumeration of inputs. -/
theorem initialization_prefix (hn : n ≤ 4095) :
    runFor 8 code (.running (inputs n i value)) =
      some ⟨.running (loop n i value 0 none none), [.alloc 0 (n * 8 + 8)]⟩ := by
  have mulBound : n * 8 < wordBound := by unfold wordBound; omega
  have byteBound : n * 8 + 8 < wordBound := by unfold wordBound; omega
  have positive : 0 < n * 8 + 8 := by omega
  have aligned : (n * 8 + 8) % 8 = 0 := by omega
  have bytes : n * 8 + 8 ≤ 32768 := by omega
  have div : (n * 8 + 8) / 8 = n + 1 := by omega
  have total : n + 1 ≤ 4096 := by omega
  change n * 8 < 18446744073709551616 at mulBound
  change n * 8 + 8 < 18446744073709551616 at byteBound
  simp [runFor, rawTick, fetch, code, inputs, loop, rvalue, operand,
    constant, binary, write, valueType, mallocHeap, advance, jump,
    mulBound, byteBound, positive, aligned, bytes, div, total, cells_zero,
    wordBound, Array.set!, Array.setIfInBounds]


/-- Entry validation preserves argument order, including the two equal-typed
U64 slots. The formal fixture is one program for all bounded inputs. -/
theorem input_frame (hn : n ≤ 4095) (hi : i < wordBound) (hv : value < scalarBound) :
    entryFrame code entry [.u64 n, .u64 i, .i64 value] = some (inputs n i value) := by
  have hn' : n < wordBound := by unfold wordBound; omega
  have he : entryValid code entry = true := by decide +kernel
  unfold entryFrame
  rw [he]
  simp [bindArguments, entry, code, initial, inputs, argumentValueValid, valueType,
    hn', hi, hv, Array.set!, Array.replicate, Array.setIfInBounds]

/-- One actual test/store/increment/backedge iteration. -/
theorem fill_iteration (hn : n ≤ 4095) (hk : k < n) (hv : value < scalarBound) :
    runFor 6 code (.running (loop n i value k test dest)) =
      some ⟨.running (loop n i value (k + 1) (some (.boolean true))
        (some (.pointer 0 k))), []⟩ := by
  have one : 1 < wordBound := by decide
  have bound : k + 1 < wordBound := by unfold wordBound; omega
  have offset : k ≤ n + 1 := by omega
  have store : k < n + 1 := by omega
  simp [runFor, rawTick, fetch, code, loop, rvalue, operand,
    constant, binary, write, valueType, advance, jump, switchValue, select,
    hk, hv, one, bound, offset, store, Array.set!, Array.setIfInBounds, cells_set hk]

/-- Each iteration increases the initialized prefix; induction on the number
of cells remaining proves termination without enumerating input lengths. -/
theorem fill_total (hn : n ≤ 4095) (hv : value < scalarBound) (hk : k ≤ n) :
    ∃ test' dest', Steps code (.running (loop n i value k test dest)) []
      (.running (loop n i value n test' dest')) := by
  generalize he : n - k = remaining
  induction remaining generalizing k test dest with
  | zero =>
    have eq : k = n := by omega
    subst k
    exact ⟨test, dest, .nil⟩
  | succ remaining ih =>
    have lt : k < n := by omega
    have eq : n - (k + 1) = remaining := by omega
    obtain ⟨test', dest', rest⟩ := ih (by omega) eq
      (test := some (.boolean true)) (dest := some (.pointer 0 k))
    exact ⟨test', dest', by simpa using
      (steps_trans (runFor_sound (fill_iteration hn lt hv)) rest)⟩

def finalFrame (n i value : Nat) (dest : Option Value) : Frame :=
  if i < n then
    ⟨8, 1, #[some (.i64 value), some (.u64 n), some (.u64 i), some (.i64 value),
      some (.u64 (n * 8)), some (.u64 (n * 8 + 8)), some (.pointer 0 0),
      some (.address 0), some (.boolean true), some (.u64 n), some (.boolean false), dest,
      some (.boolean true), some (.pointer 0 0), some (.pointer 0 i), some (.i64 value),
      some .unit, some (.i64 value), none], #[⟨false, cells n value n⟩]⟩
  else
    ⟨8, 1, #[some (.i64 99), some (.u64 n), some (.u64 i), some (.i64 value),
      some (.u64 (n * 8)), some (.u64 (n * 8 + 8)), some (.pointer 0 0),
      some (.address 0), some (.boolean true), some (.u64 n), some (.boolean false), dest,
      some (.boolean false), none, none, none, none, some (.i64 99), some .unit],
      #[⟨false, cells n value n⟩]⟩

theorem filled_read (h : i < n) : load #[⟨true, cells n value n⟩] 0 i = some value := by
  simp [load, cells_lookup (by omega : i < n + 1), h]

theorem spare_uninitialized : load #[⟨true, cells n value n⟩] 0 n = none := by
  simp [load, cells]

/-- The successful branch reads a filled logical cell before freeing the base
pointer. The other branch frees without reading, including n=0. -/
theorem finishing_prefix :
    runFor 12 code (.running (loop n i value n test dest)) =
      some ⟨.returned (if i < n then value else 99) (finalFrame n i value dest), [.free 0]⟩ := by
  by_cases h : i < n
  · have offset : i ≤ n + 1 := by omega
    simp [runFor, rawTick, fetch, code, loop, finalFrame, rvalue, operand,
      constant, binary, write, valueType, advance, jump, switchValue, select,
      h, offset, filled_read h, freeHeap, Array.set!, Array.setIfInBounds]
  · simp [runFor, rawTick, fetch, code, loop, finalFrame, rvalue, operand,
      constant, binary, write, valueType, advance, jump, switchValue, select,
      h, freeHeap, scalarBound, Array.set!, Array.setIfInBounds]

theorem final_heap (n i value : Nat) (dest : Option Value) :
    (finalFrame n i value dest).heap = #[⟨false, cells n value n⟩] := by
  unfold finalFrame
  split <;> rfl

theorem final_no_live (n i value : Nat) (dest : Option Value) :
    heapEmpty (finalFrame n i value dest) = true := by
  simp [heapEmpty, final_heap]

/-- Every allowed length terminates after one allocation, n fill iterations,
an optional initialized load, and exactly one free. -/
theorem terminates (hn : n ≤ 4095) (hv : value < scalarBound) :
    ∃ dest, Steps code (.running (inputs n i value))
      [.alloc 0 (n * 8 + 8), .free 0]
      (.returned (if i < n then value else 99) (finalFrame n i value dest)) := by
  obtain ⟨test, dest, filled⟩ := fill_total (i := i) (k := 0)
    (test := none) (dest := none) hn hv (by omega)
  exact ⟨dest, by simpa using (steps_trans (runFor_sound (initialization_prefix hn))
    (steps_trans filled (runFor_sound finishing_prefix)))⟩

theorem every_return (hn : n ≤ 4095) (hv : value < scalarBound)
    (run : Steps code (.running (inputs n i value)) events (.returned result frame)) :
    result = (if i < n then value else 99) ∧
      events = [.alloc 0 (n * 8 + 8), .free 0] ∧
      frame.heap = #[⟨false, cells n value n⟩] ∧ heapEmpty frame = true := by
  obtain ⟨dest, expected⟩ := terminates (i := i) hn hv
  obtain ⟨rfl, rfl, rfl⟩ := run.returned_deterministic expected
  exact ⟨rfl, rfl, final_heap n i value dest, final_no_live n i value dest⟩

end Jihoo.DynamicMir
