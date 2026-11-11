import Jihoo.SizedMirAllocation
import Jihoo.SizedMirHeap
import Jihoo.SizedErasureCompiler
import Jihoo.SizedErasureForward

/-! Forward lowering of compact/source allocation constructors to generated MIR.
Code is constructed from operand syntax and an existing continuation. Runtime
numeric/capacity bounds remain explicit; arbitrary continuations and the native
compiler's implementation are outside this translation theorem. -/
namespace Jihoo.SizedMir
open BoundedMir
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def operandValid (bound : Nat) : Operand → Bool
  | .constant _ => true
  | .copy p => !p.deref && p.slot < bound

theorem operandValid_iff : operandValid bound op = true ↔ Before bound op := by
  cases op <;> simp [operandValid, Before]

def inputsValid (bound : Nat) (inputs : List Operand) : Bool :=
  inputs.all (operandValid bound)

theorem inputsValid_iff : inputsValid bound inputs = true ↔ InputsBefore bound inputs := by
  simp [inputsValid, List.all_eq_true, operandValid_iff, InputsBefore]

/-- Lower only the allocation constructor. Natural operands include nested
lexical lets; all other compact program constructors are rejected here. -/
def lower (before : Code) (exit : Nat) (inputs : List Operand) : SizedErasure.Term → Option Code
  | .allocate length fill =>
    if exit < before.blocks.size ∧ before.locals.size + 10 ≤ 512 ∧
        before.blocks.size + 6 ≤ 512 ∧ inputsValid before.locals.size inputs = true then do
      let lengthOp ← lowerNat inputs length
      let fillOp ← lowerScalar inputs fill
      let code := Allocation.build before exit lengthOp fillOp
      if valid code then return code else none
    else none
  | _ => none

theorem lower_shape (success : lower before exit inputs (.allocate length fill) = some code) :
    ∃ lengthOp fillOp,
      lowerNat inputs length = some lengthOp ∧ lowerScalar inputs fill = some fillOp ∧
      code = Allocation.build before exit lengthOp fillOp ∧
      exit < before.blocks.size ∧ before.locals.size + 10 ≤ 512 ∧
      before.blocks.size + 6 ≤ 512 ∧ InputsBefore before.locals.size inputs ∧ valid code = true := by
  simp only [lower] at success
  split at success
  next guard =>
    cases hn : lowerNat inputs length with
    | none => simp [hn] at success
    | some lengthOp =>
      cases hv : lowerScalar inputs fill with
      | none => simp [hn, hv] at success
      | some fillOp =>
        simp [hn, hv] at success
        obtain ⟨validated, same⟩ := success
        subst code
        exact ⟨lengthOp, fillOp, rfl, rfl, rfl, guard.1, guard.2.1,
          guard.2.2.1, inputsValid_iff.mp guard.2.2.2, validated⟩
  next => contradiction

theorem lower_bounds (success : lower before exit inputs (.allocate length fill) = some code) :
    code.locals.size ≤ 512 ∧ code.blocks.size ≤ 512 ∧
      before.blocks.size < code.blocks.size := by
  obtain ⟨_, _, _, _, rfl, _, locals, blocks, _⟩ := lower_shape success
  simp only [Allocation.local_count, Allocation.block_count]
  exact ⟨locals, blocks, by omega⟩

theorem lower_valid (success : lower before exit inputs (.allocate length fill) = some code) :
    valid code = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, validated⟩ := lower_shape success
  exact validated

theorem lower_local_prefix (success : lower before exit inputs (.allocate length fill) = some code)
    (old : slot < before.locals.size) : code.locals[slot]? = before.locals[slot]? := by
  obtain ⟨_, _, _, _, rfl, _⟩ := lower_shape success
  exact Allocation.local_prefix old

theorem lower_block_prefix (success : lower before exit inputs (.allocate length fill) = some code)
    (old : block < before.blocks.size) : code.blocks[block]? = before.blocks[block]? := by
  obtain ⟨_, _, _, _, rfl, _⟩ := lower_shape success
  exact Allocation.block_prefix old

/-- The result pointer and retained input aliases fit the next lowering context. -/
theorem lower_result_inputs (success : lower before exit inputs (.allocate length fill) = some code) :
    InputsBefore code.locals.size (.copy ⟨before.locals.size + 4, false⟩ :: inputs) := by
  obtain ⟨_, _, _, _, rfl, _, _, _, old, _⟩ := lower_shape success
  intro op member
  rcases List.mem_cons.mp member with rfl | rest
  · simp [Before]
  · apply (old op rest).mono
    simp

/-- Observe logical allocation/free at the physical byte-request interface.
Lease and read events have no allocation-lifecycle observation. -/
def lifecycle : List SizedBufferHeap.Event → List Event
  | [] => []
  | .alloc object n _ :: rest => .alloc object (n * 8 + 8) :: lifecycle rest
  | .free object :: rest => .free object :: lifecycle rest
  | _ :: rest => lifecycle rest

/-- Forward execution is constructed from a successful lowering and the compact
operand evaluations. The final owner extends the represented runtime context. -/
theorem allocation_forward
    (success : lower before exit inputs (.allocate length fill) = some code)
    (hsize : before.locals.size = f.locals.size)
    (related : EnvRel env inputs f) (heaps : HeapRel s f.heap)
    (lengthRun : SizedErasure.NatEval env length n)
    (fillRun : SizedErasure.ScalarEval env fill value)
    (hobjects : s.heap.nextObject < 512) (hcells : cellCount s + n + 1 ≤ 4096)
    (hv : value < scalarBound) :
    ∃ dest,
      Steps code (.running (Allocation.startFrame before f.locals f.heap))
        [.alloc s.heap.nextObject (n * 8 + 8)]
        (.running (Allocation.outputFrame before exit f.locals f.heap n value dest)) ∧
      HeapRel (SizedBufferHeap.allocate s n value)
        (Allocation.outputFrame before exit f.locals f.heap n value dest).heap ∧
      EnvRel (.owner s.heap.nextObject :: env)
        (.copy ⟨before.locals.size + 4, false⟩ :: inputs)
        (Allocation.outputFrame before exit f.locals f.heap n value dest) := by
  obtain ⟨lengthOp, fillOp, hn, hf, rfl, hexit, _, _, beforeInputs, _⟩ := lower_shape success
  have old : InputsBefore f.locals.size inputs := by simpa only [hsize] using beforeInputs
  have cells : (f.heap.toList.map (fun obj => obj.cells.size)).sum + n + 1 ≤ 4096 := by
    rw [heaps.cell_count]
    exact hcells
  have objects : f.heap.size < 512 := by rw [← heaps.nextObject]; exact hobjects
  obtain ⟨dest, run⟩ := Allocation.run hsize hexit
    (lowerNat_before old hn) (lowerScalar_before old hf)
    (lowerNat_correct lengthRun related hn) (lowerScalar_correct fillRun related hf)
    objects cells hv
  refine ⟨dest, ?_, heaps.allocate, ?_⟩
  · simpa only [heaps.nextObject] using run
  · apply EnvRel.keep
    · simpa only [hsize, toMir, heaps.nextObject] using
        (Allocation.output_owner_operand (before := before) (exit := exit)
          (original := f.locals) (H := f.heap) (n := n) (value := value) (dest := dest))
    · apply related.frame old
      intro slot bound
      exact (Allocation.output_local_prefix bound).symm

/-- Every compact allocation execution has a generated MIR prefix with related
result, heap and retained environment. Source final-state resource bounds are
sufficient; no successful MIR execution is supplied as a premise. -/
theorem compact_to_mir
    (success : lower before exit inputs (.allocate length fill) = some code)
    (hsize : before.locals.size = f.locals.size)
    (related : EnvRel env inputs f) (heaps : HeapRel s f.heap)
    (compact : SizedErasure.Eval env (.allocate length fill) s (.owner owner) events t)
    (hobjects : t.heap.nextObject ≤ 512) (hcells : cellCount t ≤ 4096)
    (hv : t.heap.payload owner < scalarBound) :
    ∃ final,
      Steps code (.running (Allocation.startFrame before f.locals f.heap))
        (lifecycle events) (.running final) ∧
      HeapRel t final.heap ∧
      EnvRel (.owner owner :: env) (.copy ⟨before.locals.size + 4, false⟩ :: inputs) final ∧
      (∀ slot, slot < f.locals.size → final.locals[slot]? = f.locals[slot]?) ∧
      final.block = exit ∧ final.index = 0 := by
  cases compact with
  | allocate lengthRun fillRun =>
    have objects : s.heap.nextObject < 512 := by
      simp only [SizedBufferHeap.allocate] at hobjects
      omega
    have cells := hcells
    rw [cellCount_allocate] at cells
    have valueBound := hv
    simp only [SizedBufferHeap.allocate, HeapLeases.put, ite_true] at valueBound
    obtain ⟨dest, run, heap, env⟩ := allocation_forward success hsize related heaps
      lengthRun fillRun objects cells valueBound
    exact ⟨_, run, heap, env, fun _ bound => Allocation.output_local_prefix bound,
      Allocation.output_control⟩

/-- Composition with the proved graph compactor connects any covered source
allocation root to the generated MIR. This does not assert association with the
native compiler's emitted CFG or cover other runtime constructors. -/
theorem source_to_mir
    (compacted : SizedErasure.compileTarget graph fuel mask root = some (.allocate length fill))
    (success : lower before exit inputs (.allocate length fill) = some code)
    (hsize : before.locals.size = f.locals.size)
    (erasedEnv : SizedErasure.EnvRel mask sourceEnv env)
    (related : EnvRel env inputs f) (heaps : HeapRel s f.heap)
    (source : SizedCoreExecution.Eval graph sourceEnv root s (.owner owner) events t)
    (hobjects : t.heap.nextObject ≤ 512) (hcells : cellCount t ≤ 4096)
    (hv : t.heap.payload owner < scalarBound) :
    ∃ final,
      Steps code (.running (Allocation.startFrame before f.locals f.heap))
        (lifecycle events) (.running final) ∧
      HeapRel t final.heap ∧
      EnvRel (.owner owner :: env) (.copy ⟨before.locals.size + 4, false⟩ :: inputs) final ∧
      (∀ slot, slot < f.locals.size → final.locals[slot]? = f.locals[slot]?) ∧
      final.block = exit ∧ final.index = 0 := by
  obtain ⟨value, same, compact⟩ := (SizedErasure.compileTarget_correct compacted).forward erasedEnv source
  have equal : value = .owner owner := SizedErasure.Value.embed_inj.mp same.symm
  subst value
  exact compact_to_mir success hsize related heaps compact hobjects hcells hv

end Jihoo.SizedMir
