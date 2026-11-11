import Jihoo.SizedMirLinearSteps

/-! Generated read prefixes in arbitrary completed code. Physical representation
forgets lease counters; source borrowing authority must be proved separately. -/
namespace Jihoo.SizedMir
open BoundedMir
set_option linter.unusedSimpArgs false

/-- Restoring source lease metadata does not change its physical representation.
This is not a claim that an arbitrary source borrow or read is authorized. -/
theorem HeapRel.restore (related : HeapRel s H) :
    HeapRel (SizedBufferHeap.restore s) H := by
  constructor
  · exact related.nextObject
  · exact related.objects

namespace Linear

def readFrame (f : Frame) (slot exit objectId index value : Nat) : Frame :=
  ⟨exit, 0, (f.locals.set! slot (some (.pointer objectId index))).set!
    (slot + 1) (some (.i64 value)), f.heap⟩

@[simp] theorem readFrame_size :
    (readFrame f slot exit objectId index value).locals.size = f.locals.size := by
  simp [readFrame]

@[simp] theorem readFrame_heap :
    (readFrame f slot exit objectId index value).heap = f.heap := rfl

theorem readFrame_other (other : k < slot ∨ slot + 2 ≤ k) :
    (readFrame f slot exit objectId index value).locals[k]? = f.locals[k]? := by
  have first : slot ≠ k := by omega
  have second : slot + 1 ≠ k := by omega
  by_cases h1 : slot < f.locals.size <;> by_cases h2 : slot + 1 < f.locals.size <;>
    simp [readFrame, Array.set!, Array.setIfInBounds, first, second, h1, h2]

theorem readFrame_result (bound : slot + 2 ≤ f.locals.size) :
    operand (readFrame f slot exit objectId index value) (.copy ⟨slot + 1, false⟩) =
      some (.i64 value) := by
  have first : slot < f.locals.size := by omega
  have second : slot + 1 < f.locals.size := by omega
  simp [operand, readFrame, Array.set!, Array.setIfInBounds, first, second]

/-- Both input operands are evaluated before either scratch slot is overwritten.
No assumption about their positions or the old scratch contents is needed. -/
theorem read_run
    (block : c.blocks[f.block]? = some (readBlock slot owner indexOp exit))
    (start : f.index = 0)
    (ptrTy : c.locals[slot]? = some .ptr)
    (resultTy : c.locals[slot + 1]? = some .i64)
    (bound : slot + 2 ≤ f.locals.size) (out : exit < c.blocks.size)
    (pointer : operand f owner = some (.pointer objectId 0))
    (indexValue : operand f indexOp = some (.u64 index))
    (heaps : HeapRel s f.heap) (old : objectId < f.heap.size)
    (live : s.heap.live objectId = true) (inside : index < s.length objectId) :
    Steps c (.running f) []
      (.running (readFrame f slot exit objectId index (s.heap.payload objectId))) := by
  have firstBound : slot < f.locals.size := by omega
  have secondBound : slot + 1 < f.locals.size := by omega
  let first : Frame := { f with index := 1, locals := f.locals.set! slot (some (.pointer objectId index)) }
  let second : Frame := { first with index := 2, locals := first.locals.set! (slot + 1) (some (.i64 (s.heap.payload objectId))) }
  have offset : rvalue f (.offset owner indexOp) = some (.pointer objectId index) := by
    simp [rvalue, pointer, indexValue, heaps.objects objectId old, SizedMir.object,
      live, show index ≤ s.length objectId + 1 by omega]
  have step1 : Step c (.running f) [] (.running first) := by
    have h := Step.assign (c := c) (f := f) (place := ⟨slot, false⟩)
      (rhs := .offset owner indexOp) (v := .pointer objectId index)
      (next := { f with locals := f.locals.set! slot (some (.pointer objectId index)) })
      (by simp [fetch, block, start, readBlock]) offset
      (by simp [write, ptrTy, valueType, firstBound])
    simpa [first, advance, start] using h
  have loaded : rvalue first (.use (.copy ⟨slot, true⟩)) =
      some (.i64 (s.heap.payload objectId)) := by
    simp [rvalue, operand, first, Array.set!, Array.setIfInBounds, firstBound,
      heaps.read old live inside]
  have step2 : Step c (.running first) [] (.running second) := by
    have h := Step.assign (c := c) (f := first) (place := ⟨slot + 1, false⟩)
      (rhs := .use (.copy ⟨slot, true⟩)) (v := .i64 (s.heap.payload objectId))
      (next := { first with locals := first.locals.set! (slot + 1) (some (.i64 (s.heap.payload objectId))) })
      (by simp [fetch, first, block, readBlock]) loaded
      (by simp [write, resultTy, valueType, first, secondBound])
    simpa [second, advance, first] using h
  have step3 : Step c (.running second) []
      (.running (readFrame f slot exit objectId index (s.heap.payload objectId))) := by
    have h := Step.goto (f := second) (by simp [fetch, second, first, block, readBlock]) out
    simpa [jump, second, first, readFrame] using h
  exact .cons step1 (.cons step2 (.cons step3 .nil))


/-- The complete read-prefix interface, including the exact exit and local frame.
The only execution fact in this theorem is its conclusion. -/
theorem read_correct
    (block : c.blocks[f.block]? = some (readBlock slot owner indexOp exit))
    (start : f.index = 0)
    (ptrTy : c.locals[slot]? = some .ptr)
    (resultTy : c.locals[slot + 1]? = some .i64)
    (bound : slot + 2 ≤ f.locals.size) (out : exit < c.blocks.size)
    (pointer : operand f owner = some (.pointer objectId 0))
    (indexValue : operand f indexOp = some (.u64 index))
    (heaps : HeapRel s f.heap) (old : objectId < f.heap.size)
    (live : s.heap.live objectId = true) (inside : index < s.length objectId) :
    ∃ g, Steps c (.running f) [] (.running g) ∧
      g.block = exit ∧ g.index = 0 ∧ g.heap = f.heap ∧
      HeapRel s g.heap ∧
      operand g (.copy ⟨slot + 1, false⟩) = some (.i64 (s.heap.payload objectId)) ∧
      g.locals.size = f.locals.size ∧
      ∀ k, k < slot ∨ slot + 2 ≤ k → g.locals[k]? = f.locals[k]? := by
  refine ⟨readFrame f slot exit objectId index (s.heap.payload objectId),
    read_run block start ptrTy resultTy bound out pointer indexValue heaps old live inside,
    rfl, rfl, rfl, heaps, readFrame_result bound, readFrame_size, ?_⟩
  intro k outside
  exact readFrame_other outside

/- The owner and index deliberately occupy the two destination slots. The
unrelated local, heap and pre-existing scratch values test the generic frame. -/
private def aliasReadCode : Code :=
  ⟨#[.i64, .ptr, .i64, .unit],
    #[readBlock 1 (.copy ⟨1, false⟩) (.copy ⟨2, false⟩) 1, ⟨#[], .ret⟩]⟩

private def aliasReadStart : Frame :=
  ⟨0, 0, #[some (.i64 99), some (.pointer 0 0), some (.u64 1), some .unit],
    #[⟨true, #[some 37, some 37, none]⟩]⟩

example : runFor 3 aliasReadCode (.running aliasReadStart) =
    some ⟨.running (readFrame aliasReadStart 1 1 0 1 37), []⟩ := by decide

example : (readFrame aliasReadStart 1 1 0 1 37).locals =
    #[some (.i64 99), some (.pointer 0 1), some (.i64 37), some .unit] := by decide

end Linear
end Jihoo.SizedMir
