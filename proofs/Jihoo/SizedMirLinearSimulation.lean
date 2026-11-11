import Jihoo.SizedMirAllocationEmbedded
import Jihoo.SizedMirLinearSteps
import Jihoo.SizedMirTraceBounds
import Jihoo.SizedMirTranslation

/-! Compositional forward execution of generated straight-line MIR. Source safe
traces justify release; final cumulative bounds justify every allocation. -/
namespace Jihoo.SizedMir.Linear
open BoundedMir
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def start (f : Frame) (block : Nat) : Frame := { f with block := block, index := 0 }

@[simp] theorem operand_start : operand (start f block) op = operand f op := by
  cases op <;> rfl

theorem start_eq (block : f.block = target) (index : f.index = 0) : start f target = f := by
  cases f
  simp_all [start]

theorem Compiles.covered (compiled : Compiles inputs l b exit term fragment) : Trace.LinearTerm term := by
  induction compiled with
  | scalar => exact .scalar
  | natural => exact .natural
  | var => exact .var
  | allocate => exact .allocate
  | app _ _ first last => exact .app first last
  | free _ _ ih => exact .free ih

theorem Embedded.allocation
    (placed : Embedded c l b (allocationFragment l b exit length fill))
    (out : exit < c.blocks.size) : Allocation.Embedded c l b exit length fill := by
  constructor
  · constructor
    · intro r
      have h := placed.locals r.val (by simp [allocationFragment, Allocation.roleTypes])
      simpa [allocationFragment, Allocation.roleTypes, Allocation.layout] using h
    · simpa [allocationFragment, Allocation.fragmentBlocks, Allocation.labels] using placed.blocks 1 (by simp [allocationFragment, Allocation.fragmentBlocks])
    · simpa [allocationFragment, Allocation.fragmentBlocks, Allocation.labels] using placed.blocks 2 (by simp [allocationFragment, Allocation.fragmentBlocks])
    · simpa [allocationFragment, Allocation.fragmentBlocks, Allocation.labels] using placed.blocks 3 (by simp [allocationFragment, Allocation.fragmentBlocks])
    · simpa [allocationFragment, Allocation.fragmentBlocks, Allocation.labels] using placed.blocks 4 (by simp [allocationFragment, Allocation.fragmentBlocks])
    · simpa [allocationFragment, Allocation.fragmentBlocks, Allocation.labels] using placed.blocks 5 (by simp [allocationFragment, Allocation.fragmentBlocks])
    · exact out
  · simpa [allocationFragment, Allocation.fragmentBlocks] using placed.blocks 0 (by simp [allocationFragment, Allocation.fragmentBlocks])

theorem lifecycle_append (first last : List SizedBufferHeap.Event) :
    lifecycle (first ++ last) = lifecycle first ++ lifecycle last := by
  induction first with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [lifecycle, ih]

/-- Every covered compact execution constructs an instruction execution in the
completed code, retaining the lexical environment and exact heap representation.
No successful MIR run is a premise. -/
theorem Compiles.simulate
    (compiled : Compiles inputs l b exit term fragment)
    (placed : Embedded c l b fragment) (out : exit < c.blocks.size)
    (size : c.locals.size = f.locals.size) (before : InputsBefore l inputs)
    (related : EnvRel env inputs f) (heaps : HeapRel s f.heap)
    (valid : SizedBufferHeap.Valid s)
    (run : SizedErasure.Eval env term s value events t)
    (safe : SizedBufferHeap.Steps s events t) (bounded : Trace.Bounds t) :
    ∃ final, Steps c (.running (start f (entry b exit term))) (lifecycle events) (.running final) ∧
      final.block = exit ∧ final.index = 0 ∧ HeapRel t final.heap ∧
      operand final fragment.result = some (toMir value) ∧
      final.locals.size = f.locals.size ∧
      (∀ i, i < l → final.locals[i]? = f.locals[i]?) := by
  induction compiled generalizing env f s value events t c with
  | @scalar v inputs l b exit bound =>
    cases run
    refine ⟨start f exit, ?_, rfl, rfl, heaps, ?_, rfl, ?_⟩
    · simpa [entry, blockCost, lifecycle] using (Steps.nil (c := c) (m := .running (start f exit)))
    · simp [pureFragment, operand, constant, toMir, bound]
    · intro i hi; rfl
  | @natural n inputs l b exit bound =>
    cases run
    refine ⟨start f exit, ?_, rfl, rfl, heaps, ?_, rfl, ?_⟩
    · simpa [entry, blockCost, lifecycle] using (Steps.nil (c := c) (m := .running (start f exit)))
    · simp [pureFragment, operand, constant, toMir, bound]
    · intro i hi; rfl
  | @var inputs k op l b exit lookup =>
    cases run with
    | var source =>
      refine ⟨start f exit, ?_, rfl, rfl, heaps, ?_, rfl, ?_⟩
      · simpa [entry, blockCost, lifecycle] using (Steps.nil (c := c) (m := .running (start f exit)))
      · simpa [pureFragment] using related.lookup source lookup
      · intro i hi; rfl
  | @allocate inputs length lengthOp fill fillOp l b exit hn hf =>
    cases run with
    | allocate lengthRun fillRun =>
      rename_i n value
      obtain ⟨objects, cells, payload⟩ := bounded.allocation
      have locals : l + 10 ≤ f.locals.size := by simpa [allocationFragment, Allocation.roleTypes, size] using placed.localBound
      have hobjects : f.heap.size < 512 := by rw [← heaps.nextObject]; exact objects
      have hcells : (f.heap.toList.map (fun obj => obj.cells.size)).sum + n + 1 ≤ 4096 := by
        rw [heaps.cell_count]; exact cells
      obtain ⟨final, target, control, index, heap, result, length, frame⟩ :=
        Allocation.embedded_run (placed.allocation out) locals
          (lowerNat_before before hn) (lowerScalar_before before hf)
          (lowerNat_correct lengthRun related hn) (lowerScalar_correct fillRun related hf)
          hobjects hcells payload
      refine ⟨final, ?_, control, index, ?_, ?_, length, fun i hi => frame i (Or.inl hi)⟩
      · simpa [start, lifecycle, heaps.nextObject] using target
      · rw [heap]; exact heaps.allocate
      · simpa [allocationFragment, toMir, heaps.nextObject] using result
  | @app inputs l b argument exit body first last firstCompiled lastCompiled firstIH lastIH =>
    cases run with
    | app firstRun lastRun =>
      obtain ⟨firstSafe, lastSafe⟩ := Trace.trace_suffix firstCompiled.covered firstRun safe
      have firstPlaced := placed.append_left
      have lastPlaced : Embedded c (l + localCost argument) (b + blockCost argument) last := by
        simpa only [firstCompiled.sizes.1, firstCompiled.sizes.2] using placed.append_right
      have middleExit := lastPlaced.entry_bound lastCompiled out
      obtain ⟨middle, firstSteps, middleBlock, middleIndex, middleHeap, middleValue, middleSize, middleFrame⟩ :=
        firstIH firstPlaced middleExit size before related heaps valid firstRun firstSafe (bounded.backward lastSafe)
      have kept : EnvRel env inputs middle := related.frame before (fun i hi => (middleFrame i hi).symm)
      have newBefore : InputsBefore (l + localCost argument) (first.result :: inputs) := by
        intro op member
        rcases List.mem_cons.mp member with rfl | old
        · exact firstCompiled.result_before before
        · exact (before op old).mono (by omega)
      obtain ⟨final, lastSteps, control, index, heap, result, length, frame⟩ :=
        lastIH lastPlaced out (size.trans middleSize.symm) newBefore (kept.cons middleValue)
          middleHeap (SizedBufferHeap.steps_valid valid firstSafe) lastRun lastSafe bounded
      rw [start_eq middleBlock middleIndex] at lastSteps
      refine ⟨final, ?_, control, index, heap, result, length.trans middleSize, ?_⟩
      · simpa only [entry_app, lifecycle_append] using steps_trans firstSteps lastSteps
      · intro i hi
        exact (frame i (by omega)).trans (middleFrame i hi)
  | @free inputs k owner l b exit body last lookup bodyCompiled ih =>
    cases run with
    | free source bodyRun =>
      cases safe with
      | cons released rest =>
        cases released with
        | free live unborrowed =>
          rename_i objectId suffix
          have old : objectId < f.heap.size := by rw [← heaps.nextObject]; exact valid.allocated _ live
          have tailPlaced := placed.free_tail
          have tailExit := tailPlaced.entry_bound bodyCompiled out
          have localBound : l < f.locals.size := by
            have h := placed.localBound
            simp only [freeFragment, Array.size_append, Array.size_singleton] at h
            omega
          let initial := start f b
          have firstSteps := free_run (f := initial) placed.free_block rfl placed.free_type localBound tailExit
            (by simpa [initial, toMir] using related.lookup source lookup) heaps old live
          let middle := freedFrame initial l (entry (b + 1) exit body)
            (f.heap.set! objectId { SizedMir.object s objectId with alive := false })
          have middleHeap : HeapRel (SizedBufferHeap.release s objectId) middle.heap := heaps.release old
          have middleSize : middle.locals.size = f.locals.size := by simp [middle, initial, start]
          have middleFrame : ∀ i, i < l → middle.locals[i]? = f.locals[i]? := by
            intro i hi
            exact freedFrame_other (by omega)
          have kept : EnvRel env inputs middle := related.frame before (fun i hi => (middleFrame i hi).symm)
          obtain ⟨final, lastSteps, control, index, heap, result, length, frame⟩ :=
            ih tailPlaced out (size.trans middleSize.symm) (before.mono (by omega)) kept middleHeap
              (SizedBufferHeap.step_valid valid (.free live unborrowed)) bodyRun rest bounded
          have middleStart : start middle (entry (b + 1) exit body) = middle := rfl
          rw [middleStart] at lastSteps
          refine ⟨final, ?_, control, index, heap, result, length.trans middleSize, ?_⟩
          · simpa [initial, middle, lifecycle] using steps_trans firstSteps lastSteps
          · intro i hi
            exact (frame i (by omega)).trans (middleFrame i hi)

end Jihoo.SizedMir.Linear
