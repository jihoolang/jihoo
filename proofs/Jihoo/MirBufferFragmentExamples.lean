import Jihoo.MirBufferFragment
import Jihoo.DynamicMir

/-! Non-vacuous fragment instances: the retained compiler CFG and a shifted-local,
permuted-block program with a preexisting live object and a released object. -/
namespace Jihoo.MirBufferExamples
open BoundedMir MirBuffer
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def dynamicLayout : Layout where
  slot := fun r => #[1, 3, 4, 5, 6, 7, 8, 9, 10, 11][r.val]
  distinct := by decide +kernel

def dynamicLabels : Labels := ⟨0, 1, 2, 3, 4, 5⟩

theorem dynamic_embedded : Embedded DynamicMir.code dynamicLayout dynamicLabels := by
  constructor <;> decide +kernel

theorem dynamic_index_preserved :
    (outputFrame dynamicLayout dynamicLabels original H n value dest).locals[2]! = original[2]! :=
  output_local_frame (by decide +kernel)

def shifted : Layout where
  slot := fun r => r.val + 2
  distinct := by intro a b h; apply Fin.ext; simpa using h

def labels : Labels := ⟨4, 5, 6, 3, 1, 2⟩

def retBlock : Block := ⟨#[], .ret⟩

def code : Code :=
  ⟨#[.i64, .unit, .u64, .i64, .u64, .u64, .ptr, .u64, .bool, .u64, .bool, .ptr],
    #[retBlock, bodyBlock shifted labels,
      ⟨#[], .free (copy shifted 4) ⟨1, false⟩ 7⟩,
      testBlock shifted labels, entryBlock shifted labels,
      guardBlock shifted labels, initBlock shifted labels, retBlock]⟩

theorem embedded : Embedded code shifted labels := by
  constructor <;> decide +kernel

theorem code_valid : valid code = true := by decide +kernel

def prior : Array Object := #[⟨true, #[some 73]⟩, ⟨false, #[none, some 5]⟩]

def locals (n value : Nat) : Array (Option Value) :=
  #[some (.i64 777), some .unit, some (.u64 n), some (.i64 value),
    some (.u64 19), none, some (.pointer 0 0), none,
    some (.boolean false), some (.u64 42), none, some (.pointer 1 0)]

theorem local_bounds : ∀ r, shifted.slot r < (locals n value).size := by
  intro r
  have hr := r.isLt
  change r.val + 2 < 12
  omega

theorem shifted_terminates (hn : n ≤ 4092) (hv : value < scalarBound) :
    ∃ dest, Steps code (.running ⟨4, 0, locals n value, prior⟩)
      [.alloc 2 (n * 8 + 8)]
      (.running (outputFrame shifted labels (locals n value) prior n value dest)) := by
  apply fills_from_frame embedded local_bounds
  · rfl
  · rfl
  · decide
  · simp [prior]; omega
  · exact hv

noncomputable def returnedFrame (n value : Nat) (dest : Option Value) : Frame :=
  let f := outputFrame shifted labels (locals n value) prior n value dest
  ⟨7, 0, f.locals.set! 1 (some .unit), prior.push ⟨false, cells n value n⟩⟩

theorem free_and_return :
    runFor 2 code (.running (outputFrame shifted labels (locals n value) prior n value dest)) =
      some ⟨.returned 777 (returnedFrame n value dest), [.free 2]⟩ := by
  have size : (locals n value).size = 12 := rfl
  have look : (MirLocal.overlay shifted.slot (locals n value)
      (loopValues n value prior.size n (some (.boolean false)) dest))[shifted.slot 4]? =
      some (some (.pointer prior.size 0)) :=
    MirLocal.overlay_lookup_opt shifted.slot (locals n value) _ shifted.distinct 4 (local_bounds 4)
  have other : ∀ r, shifted.slot r ≠ 0 := by intro r; simp [shifted]
  have look0 : (MirLocal.overlay shifted.slot (locals n value)
      (loopValues n value prior.size n (some (.boolean false)) dest))[0]! = some (.i64 777) :=
    MirLocal.overlay_other shifted.slot (locals n value) _ 0 other
  have look0' (hb) : (MirLocal.overlay shifted.slot (locals n value)
      (loopValues n value prior.size n (some (.boolean false)) dest))[0]'hb = some (.i64 777) := by
    rw [← getElem!_pos (MirLocal.overlay shifted.slot (locals n value) _) 0 hb]
    exact look0
  have priorSize : prior.size = 2 := rfl
  simp [runFor, rawTick, fetch, code, labels, retBlock, outputFrame, frame,
    slotPlace, copy, operand, write, valueType, jump, returnedFrame,
    look, free_prefix, size, Array.setIfInBounds, look0']
  exact priorSize

/-- The same proof covers zero length and the cumulative-capacity boundary. It
returns after freeing only the fresh object; the prior live object stays live. -/
theorem complete_run (hn : n ≤ 4092) (hv : value < scalarBound) :
    ∃ dest, Steps code (.running ⟨4, 0, locals n value, prior⟩)
      [.alloc 2 (n * 8 + 8), .free 2]
      (.returned 777 (returnedFrame n value dest)) := by
  apply continue_after_fill embedded local_bounds (by rfl) (by rfl) (by decide)
    (by simp [prior]; omega) hv (fun dest => .returned 777 (returnedFrame n value dest))
  intro dest
  exact runFor_sound free_and_return

theorem zero_run :
    ∃ dest, Steps code (.running ⟨4, 0, locals 0 0, prior⟩)
      [.alloc 2 8, .free 2] (.returned 777 (returnedFrame 0 0 dest)) :=
  complete_run (by decide) (by decide)

theorem capacity_run :
    ∃ dest, Steps code (.running ⟨4, 0, locals 4092 (2^63-1), prior⟩)
      [.alloc 2 (4092 * 8 + 8), .free 2]
      (.returned 777 (returnedFrame 4092 (2^63-1) dest)) :=
  complete_run (by decide) (by decide)

theorem prior_read_preserved :
    load (returnedFrame n value dest).heap 0 0 = some 73 := by
  simp [returnedFrame, load, prior]

theorem fresh_released :
    load (returnedFrame n value dest).heap 2 index = none := by
  simp [returnedFrame, load, prior]

theorem prior_still_live : heapEmpty (returnedFrame n value dest) = false := by
  simp [heapEmpty, returnedFrame, prior]

def observe (fuel n value : Nat) : Option (Nat × Array Object × List Event) := do
  let out ← runFor fuel code (.running ⟨4, 0, locals n value, prior⟩)
  let .returned result f := out.machine | none
  return (result, f.heap, out.events)

theorem executable_two_cells :
    observe 24 2 19 = some (777, prior.push ⟨false, cells 2 19 2⟩,
      [.alloc 2 24, .free 2]) := by decide +kernel

theorem executable_zero_cells :
    observe 12 0 0 = some (777, prior.push ⟨false, cells 0 0 0⟩,
      [.alloc 2 8, .free 2]) := by decide +kernel

theorem too_many_cells : mallocHeap prior (4093 * 8 + 8) = none := by decide +kernel

theorem missing_store_not_embedded :
    ¬ Embedded { code with blocks := code.blocks.set! 1 ⟨#[], .goto 3⟩ } shifted labels := by
  intro h
  have bad := h.body
  contradiction

end Jihoo.MirBufferExamples
