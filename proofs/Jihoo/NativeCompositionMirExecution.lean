import Jihoo.NativeCompositionMir
import Jihoo.MirBufferHeap

/-! Symbolic execution of the retained native CFG. Two independent fill-loop
inductions cover every admitted pair of lengths, not a finite set of examples.
The allocator is the successful bounded abstract allocator; I64 payloads are
represented by nonnegative naturals. -/
namespace Jihoo.NativeCompositionMir
open BoundedMir MirBuffer
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def inputs (n m i value : Nat) : Frame :=
  ⟨0, 0, #[none, some (.u64 n), some (.u64 m), some (.u64 i), some (.i64 value), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], #[]⟩

def firstLoop (n m i value k : Nat) (test dest : Option Value) : Frame :=
  ⟨3, 0, #[none, some (.u64 n), some (.u64 m), some (.u64 i), some (.i64 value), some (.u64 (n * 8)), some (.u64 (n * 8 + 8)), some (.pointer 0 0), some (.address 0), some (.boolean true), some (.u64 k), test, dest, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none], #[⟨true, cells n value k⟩]⟩

def secondLoop (n m i value k : Nat) (firstDest test dest : Option Value) : Frame :=
  ⟨11, 0, #[none, some (.u64 n), some (.u64 m), some (.u64 i), some (.i64 value), some (.u64 (n * 8)), some (.u64 (n * 8 + 8)), some (.pointer 0 0), some (.address 0), some (.boolean true), some (.u64 n), some (.boolean false), firstDest, some (.boolean true), some (.pointer 0 0), some (.pointer 0 i), some (.i64 value), some (.u64 (m * 8)), some (.u64 (m * 8 + 8)), some (.pointer 1 0), some (.address 1), some (.boolean true), some (.u64 k), test, dest, none, none, none, none, none, none, none, none, none, none, none],
    #[⟨true, cells n value n⟩, ⟨true, cells m value k⟩]⟩

def finalFrame (n m i value : Nat) (firstDest secondDest : Option Value) : Frame :=
  if i < n then
    if 0 < m then
      ⟨8, 1, #[some (.i64 value), some (.u64 n), some (.u64 m), some (.u64 i), some (.i64 value), some (.u64 (n * 8)), some (.u64 (n * 8 + 8)), some (.pointer 0 0), some (.address 0), some (.boolean true), some (.u64 n), some (.boolean false), firstDest, some (.boolean true), some (.pointer 0 0), some (.pointer 0 i), some (.i64 value), some (.u64 (m * 8)), some (.u64 (m * 8 + 8)), some (.pointer 1 0), some (.address 1), some (.boolean true), some (.u64 m), some (.boolean false), secondDest, some (.boolean true), some (.pointer 1 0), some (.pointer 1 0), some (.i64 value), some .unit, some .unit, some (.i64 value), none, none, some (.i64 value), none],
        #[⟨false, cells n value n⟩, ⟨false, cells m value m⟩]⟩
    else
      ⟨8, 1, #[some (.i64 value), some (.u64 n), some (.u64 m), some (.u64 i), some (.i64 value), some (.u64 (n * 8)), some (.u64 (n * 8 + 8)), some (.pointer 0 0), some (.address 0), some (.boolean true), some (.u64 n), some (.boolean false), firstDest, some (.boolean true), some (.pointer 0 0), some (.pointer 0 i), some (.i64 value), some (.u64 (m * 8)), some (.u64 (m * 8 + 8)), some (.pointer 1 0), some (.address 1), some (.boolean true), some (.u64 m), some (.boolean false), secondDest, some (.boolean false), none, none, none, none, none, some (.i64 value), some .unit, some .unit, some (.i64 value), none],
        #[⟨false, cells n value n⟩, ⟨false, cells m value m⟩]⟩
  else
    ⟨8, 1, #[some (.i64 99), some (.u64 n), some (.u64 m), some (.u64 i), some (.i64 value), some (.u64 (n * 8)), some (.u64 (n * 8 + 8)), some (.pointer 0 0), some (.address 0), some (.boolean true), some (.u64 n), some (.boolean false), firstDest, some (.boolean false), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some (.i64 99), some .unit], #[⟨false, cells n value n⟩]⟩

def events (n m i : Nat) : List Event :=
  if i < n then [.alloc 0 (n * 8 + 8), .alloc 1 (m * 8 + 8), .free 0, .free 1]
  else [.alloc 0 (n * 8 + 8), .free 0]

def finalHeap (n m i value : Nat) : Array Object :=
  if i < n then #[⟨false, cells n value n⟩, ⟨false, cells m value m⟩]
  else #[⟨false, cells n value n⟩]

theorem final_heap : (finalFrame n m i value firstDest secondDest).heap = finalHeap n m i value := by
  unfold finalFrame finalHeap
  split <;> simp_all only
  split <;> rfl

theorem final_no_live : heapEmpty (finalFrame n m i value firstDest secondDest) = true := by
  rw [heapEmpty, final_heap]
  unfold finalHeap
  split <;> simp

/-- Checked binding of the exact four-argument native ABI. -/
theorem input_frame (capacity : n + m + 2 ≤ 4096) (hi : i < wordBound)
    (hv : value < scalarBound) :
    entryFrame code entry [.u64 n, .u64 m, .u64 i, .i64 value] = some (inputs n m i value) := by
  have hn : n < wordBound := by unfold wordBound; omega
  have hm : m < wordBound := by unfold wordBound; omega
  have he : entryValid code entry = true := by decide +kernel
  unfold entryFrame
  rw [he]
  simp [bindArguments, entry, code, initial, inputs, argumentValueValid, valueType,
    hn, hm, hi, hv, Array.set!, Array.replicate, Array.setIfInBounds]

/-- Initial allocation reaches its fill loop with no initialized logical cells. -/
theorem initialization_prefix (hn : n ≤ 4095) :
    runFor 8 code (.running (inputs n m i value)) =
      some ⟨.running (firstLoop n m i value 0 none none), [.alloc 0 (n * 8 + 8)]⟩ := by
  have mulBound : n * 8 < wordBound := by unfold wordBound; omega
  have byteBound : n * 8 + 8 < wordBound := by unfold wordBound; omega
  have positive : 0 < n * 8 + 8 := by omega
  have aligned : (n * 8 + 8) % 8 = 0 := by omega
  have bytes : n * 8 + 8 ≤ 32768 := by omega
  have div : (n * 8 + 8) / 8 = n + 1 := by omega
  have total : n + 1 ≤ 4096 := by omega
  change n * 8 < 18446744073709551616 at mulBound
  change n * 8 + 8 < 18446744073709551616 at byteBound
  simp [runFor, rawTick, fetch, code, inputs, firstLoop, rvalue, operand,
    constant, binary, write, valueType, mallocHeap, advance, jump,
    mulBound, byteBound, positive, aligned, bytes, div, total, cells_zero,
    wordBound, Array.set!, Array.setIfInBounds]

/-- The first loop tests, stores one cell, increments, and returns to its test. -/
theorem first_iteration (hn : n ≤ 4095) (hk : k < n) (hv : value < scalarBound) :
    runFor 6 code (.running (firstLoop n m i value k test dest)) =
      some ⟨.running (firstLoop n m i value (k + 1) (some (.boolean true))
        (some (.pointer 0 k))), []⟩ := by
  have one : 1 < wordBound := by decide
  have bound : k + 1 < wordBound := by unfold wordBound; omega
  have offset : k ≤ n + 1 := by omega
  have store : k < n + 1 := by omega
  simp [runFor, rawTick, fetch, code, firstLoop, rvalue, operand,
    constant, binary, write, valueType, advance, jump, switchValue, select,
    hk, hv, one, bound, offset, store, Array.set!, Array.setIfInBounds, cells_set hk]

theorem first_total (hn : n ≤ 4095) (hv : value < scalarBound) (hk : k ≤ n) :
    ∃ test' dest', Steps code (.running (firstLoop n m i value k test dest)) []
      (.running (firstLoop n m i value n test' dest')) := by
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
      (steps_trans (runFor_sound (first_iteration hn lt hv)) rest)⟩

theorem first_filled_read (h : i < n) : load #[⟨true, cells n value n⟩] 0 i = some value := by
  simp [load, cells_lookup (by omega : i < n + 1), h]

/-- The original read is a three-statement prefix of the second allocation
block. The actual CFG executes that prefix before sizing the new allocation. -/
theorem second_initialization (capacity : n + m + 2 ≤ 4096) (readable : i < n) :
    runFor 15 code (.running (firstLoop n m i value n test firstDest)) =
      some ⟨.running (secondLoop n m i value 0 firstDest none none),
        [.alloc 1 (m * 8 + 8)]⟩ := by
  have mulBound : m * 8 < wordBound := by unfold wordBound; omega
  have byteBound : m * 8 + 8 < wordBound := by unfold wordBound; omega
  have positive : 0 < m * 8 + 8 := by omega
  have aligned : (m * 8 + 8) % 8 = 0 := by omega
  have bytes : m * 8 + 8 ≤ 32768 := by omega
  have div : (m * 8 + 8) / 8 = m + 1 := by omega
  have total : n + 1 + (m + 1) ≤ 4096 := by omega
  have offset : i ≤ n + 1 := by omega
  change m * 8 < 18446744073709551616 at mulBound
  change m * 8 + 8 < 18446744073709551616 at byteBound
  simp [runFor, rawTick, fetch, code, firstLoop, secondLoop, rvalue, operand,
    constant, binary, write, valueType, mallocHeap, advance, jump, switchValue, select,
    readable, offset, first_filled_read readable,
    mulBound, byteBound, positive, aligned, bytes, div, total, cells_zero,
    wordBound, Array.set!, Array.setIfInBounds]

/-- Filling the copied allocation preserves the first allocation exactly. -/
theorem second_iteration (hm : m ≤ 4095) (hk : k < m) (hv : value < scalarBound) :
    runFor 6 code (.running (secondLoop n m i value k firstDest test dest)) =
      some ⟨.running (secondLoop n m i value (k + 1) firstDest (some (.boolean true))
        (some (.pointer 1 k))), []⟩ := by
  have one : 1 < wordBound := by decide
  have bound : k + 1 < wordBound := by unfold wordBound; omega
  have offset : k ≤ m + 1 := by omega
  have store : k < m + 1 := by omega
  simp [runFor, rawTick, fetch, code, secondLoop, rvalue, operand,
    constant, binary, write, valueType, advance, jump, switchValue, select,
    hk, hv, one, bound, offset, store, Array.set!, Array.setIfInBounds, cells_set hk]

theorem second_total (hm : m ≤ 4095) (hv : value < scalarBound) (hk : k ≤ m) :
    ∃ test' dest', Steps code (.running (secondLoop n m i value k firstDest test dest)) []
      (.running (secondLoop n m i value m firstDest test' dest')) := by
  generalize he : m - k = remaining
  induction remaining generalizing k test dest with
  | zero =>
    have eq : k = m := by omega
    subst k
    exact ⟨test, dest, .nil⟩
  | succ remaining ih =>
    have lt : k < m := by omega
    have eq : m - (k + 1) = remaining := by omega
    obtain ⟨test', dest', rest⟩ := ih (by omega) eq
      (test := some (.boolean true)) (dest := some (.pointer 1 k))
    exact ⟨test', dest', by simpa using
      (steps_trans (runFor_sound (second_iteration hm lt hv)) rest)⟩

theorem second_filled_read (h : 0 < m) :
    load #[⟨true, cells n value n⟩, ⟨true, cells m value m⟩] 1 0 = some value := by
  simp [load, cells, h]

/-- An out-of-range original index selects the native zero case, frees only
its original owner, writes 99 through the outer join, and returns. -/
theorem outside_finish (outside : ¬ i < n) :
    runFor 9 code (.running (firstLoop n m i value n test firstDest)) =
      some ⟨.returned 99 (finalFrame n m i value firstDest none), [.free 0]⟩ := by
  simp [runFor, rawTick, fetch, code, firstLoop, finalFrame, rvalue, operand,
    constant, binary, write, valueType, advance, jump, switchValue, select,
    outside, freeHeap, scalarBound, Array.set!, Array.setIfInBounds]

/-- Both inner arms release the original then copied owner. The positive arm
reads the copy; the zero-length arm skips that read and returns the payload. -/
theorem inside_finish (readable : i < n) :
    runFor 15 code (.running (secondLoop n m i value m firstDest test secondDest)) =
      some ⟨.returned value (finalFrame n m i value firstDest secondDest), [.free 0, .free 1]⟩ := by
  by_cases nonzero : 0 < m
  · simp [runFor, rawTick, fetch, code, secondLoop, finalFrame, rvalue, operand,
      constant, binary, write, valueType, advance, jump, switchValue, select,
      readable, nonzero, second_filled_read nonzero, freeHeap, wordBound,
      Array.set!, Array.setIfInBounds]
  · simp [runFor, rawTick, fetch, code, secondLoop, finalFrame, rvalue, operand,
      constant, binary, write, valueType, advance, jump, switchValue, select,
      readable, nonzero, freeHeap, wordBound, Array.set!, Array.setIfInBounds]

/-- Every admitted input terminates in this exact native CFG. Capacity counts
both allocations including their spare cells, even after release. -/
theorem terminates (capacity : n + m + 2 ≤ 4096) (hv : value < scalarBound) :
    ∃ firstDest secondDest, Steps code (.running (inputs n m i value)) (events n m i)
      (.returned (if i < n then value else 99) (finalFrame n m i value firstDest secondDest)) := by
  have hn : n ≤ 4095 := by omega
  have hm : m ≤ 4095 := by omega
  obtain ⟨test, firstDest, filled⟩ := first_total (m := m) (i := i) (k := 0)
    (test := none) (dest := none) hn hv (by omega)
  have first := steps_trans (runFor_sound (initialization_prefix (m := m) (i := i) (value := value) hn)) filled
  by_cases readable : i < n
  · obtain ⟨test', secondDest, copied⟩ := second_total (n := n) (i := i) (k := 0)
      (firstDest := firstDest) (test := none) (dest := none) hm hv (by omega)
    refine ⟨firstDest, secondDest, ?_⟩
    simpa [events, readable] using steps_trans first
      (steps_trans (runFor_sound (second_initialization (test := test) capacity readable))
        (steps_trans copied (runFor_sound (inside_finish (test := test') readable))))
  · refine ⟨firstDest, none, ?_⟩
    simpa [events, readable] using steps_trans first (runFor_sound (outside_finish (test := test) readable))

/-- Determinism identifies every terminating execution with the constructed
run, including exact heap contents and allocator/free observations. -/
theorem every_return (capacity : n + m + 2 ≤ 4096) (hv : value < scalarBound)
    (run : Steps code (.running (inputs n m i value)) observed (.returned result frame)) :
    result = (if i < n then value else 99) ∧ observed = events n m i ∧
      frame.heap = finalHeap n m i value ∧ heapEmpty frame = true := by
  obtain ⟨firstDest, secondDest, expected⟩ := terminates (i := i) capacity hv
  obtain ⟨rfl, rfl, rfl⟩ := run.returned_deterministic expected
  exact ⟨rfl, rfl, final_heap, final_no_live⟩

end Jihoo.NativeCompositionMir
