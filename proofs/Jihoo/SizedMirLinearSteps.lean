import Jihoo.SizedMirLinearCompiler
import Jihoo.SizedMirHeap
import Jihoo.BoundedMirRun

/-! Instruction-level release and scalar-return fragments. Their code premises
describe actual rows in the completed MIR, not successful target executions. -/
namespace Jihoo.SizedMir.Linear
open BoundedMir
set_option linter.unusedSimpArgs false

def freedFrame (f : Frame) (slot exit : Nat) (H : Array Object) : Frame :=
  ⟨exit, 0, f.locals.set! slot (some .unit), H⟩

theorem free_run
    (block : c.blocks[f.block]? = some (freeBlock slot owner exit))
    (start : f.index = 0) (ty : c.locals[slot]? = some .unit)
    (bound : slot < f.locals.size) (out : exit < c.blocks.size)
    (pointer : operand f owner = some (.pointer objectId 0))
    (heaps : HeapRel s f.heap) (old : objectId < f.heap.size)
    (live : s.heap.live objectId = true) :
    Steps c (.running f) [.free objectId]
      (.running (freedFrame f slot exit (f.heap.set! objectId { SizedMir.object s objectId with alive := false }))) := by
  have fetched : fetch c f = some (.term (.free owner ⟨slot, false⟩ exit)) := by
    simp [fetch, block, start, freeBlock]
  have written : write c { f with heap := f.heap.set! objectId { SizedMir.object s objectId with alive := false } }
      ⟨slot, false⟩ .unit = some
        { f with locals := f.locals.set! slot (some .unit), heap := f.heap.set! objectId { SizedMir.object s objectId with alive := false } } := by
    simp [write, ty, valueType, bound]
  exact .cons (.free fetched pointer (heaps.free_heap old live) written out) .nil

@[simp] theorem freedFrame_size : (freedFrame f slot exit H).locals.size = f.locals.size := by
  simp [freedFrame]

theorem freedFrame_other (other : i ≠ slot) :
    (freedFrame f slot exit H).locals[i]? = f.locals[i]? := by
  by_cases bound : slot < f.locals.size
  · simp [freedFrame, Array.set!, Array.setIfInBounds, bound, Ne.symm other]
  · simp [freedFrame, Array.set!, Array.setIfInBounds, bound]

theorem freedFrame_heap (heaps : HeapRel s f.heap) (old : objectId < f.heap.size) :
    HeapRel (SizedBufferHeap.release s objectId)
      (freedFrame f slot exit (f.heap.set! objectId { SizedMir.object s objectId with alive := false })).heap :=
  heaps.release old

def returnBlock (result : Operand) : Block :=
  ⟨#[⟨⟨0, false⟩, .use result⟩], .ret⟩

def returnedFrame (f : Frame) (value : Nat) : Frame :=
  { f with index := 1, locals := f.locals.set! 0 (some (.i64 value)) }

/-- The final scalar operand is copied to the MIR return slot and returned.
The operand may itself refer to slot zero; it is evaluated before the write. -/
theorem return_run
    (block : c.blocks[f.block]? = some (returnBlock result))
    (start : f.index = 0) (ty : c.locals[0]? = some .i64)
    (bound : 0 < f.locals.size)
    (value : operand f result = some (.i64 n)) :
    Steps c (.running f) [] (.returned n (returnedFrame f n)) := by
  have raw : Step c (.running f) [] (.running (advance { f with locals := f.locals.set! 0 (some (.i64 n)) })) := by
    apply Step.assign (place := ⟨0, false⟩) (rhs := .use result) (v := .i64 n)
      (next := { f with locals := f.locals.set! 0 (some (.i64 n)) })
    · simp [fetch, block, start, returnBlock]
    · exact value
    · simp [write, ty, valueType, bound]
  have first : Step c (.running f) [] (.running (returnedFrame f n)) := by
    simpa [advance, returnedFrame, start] using raw
  have second : Step c (.running (returnedFrame f n)) []
      (.returned n (returnedFrame f n)) := by
    apply Step.ret
    · simp [fetch, returnedFrame, block, returnBlock]
    · simp [returnedFrame, Array.set!, Array.setIfInBounds, bound]
  exact .cons first (.cons second .nil)

end Jihoo.SizedMir.Linear
