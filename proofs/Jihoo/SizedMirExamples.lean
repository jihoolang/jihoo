import Jihoo.SizedMirTranslation
import Jihoo.SizedCoreExamples

/-! Kernel-checked generated code, source composition and rejection examples.
Execution stops at the existing continuation while the fresh owner remains live. -/
namespace Jihoo.SizedMirExamples
open BoundedMir SizedMir
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def retBlock : Block := ⟨#[], .ret⟩
def before : Code := ⟨#[.i64, .unit, .u64, .i64], #[retBlock, retBlock]⟩
def inputs : List Operand := [.copy ⟨3, false⟩, .copy ⟨2, false⟩]
def length : SizedErasure.NatTerm := .letE (.var 1) (.letE (.var 0) (.var 0))
def term : SizedErasure.Term := .allocate length (.var 0)
def code : Code := Allocation.build before 0 (.copy ⟨2, false⟩) (.copy ⟨3, false⟩)

theorem compiled : lower before 0 inputs term = some code := by decide +kernel
theorem generated_valid : valid code = true := lower_valid compiled

def prior : SizedBufferHeap.State :=
  SizedBufferHeap.release
    (SizedBufferHeap.allocate (SizedBufferHeap.allocate SizedBufferHeap.empty 1 73) 0 5) 1

def heap : Array Object := materialize prior
def env (n value : Nat) : SizedErasure.Env := [.scalar value, .nat n]
def frame (n value : Nat) : Frame :=
  ⟨0, 0, #[some (.i64 777), some .unit, some (.u64 n), some (.i64 value)], heap⟩

theorem prior_related : HeapRel prior heap := HeapRel.materialize_related prior
theorem prior_cells : cellCount prior = 3 := by decide +kernel
theorem prior_objects : prior.heap.nextObject = 2 := rfl

theorem inputs_related : EnvRel (env n value) inputs (frame n value) :=
  .keep rfl (.keep rfl .nil)

theorem length_eval : SizedErasure.NatEval (env n value) length n :=
  .letE (.var rfl) (.letE (.var rfl) (.var rfl))

theorem compact_run : SizedErasure.Eval (env n value) term prior (.owner 2)
    [.alloc 2 n value] (SizedBufferHeap.allocate prior n value) :=
  .allocate length_eval (.var rfl)

/-- All supported lengths share one generated CFG and one old heap containing
both a live buffer and a released buffer. -/
theorem generated_run (hn : n ≤ 4092) (hv : value < scalarBound) :
    ∃ final,
      Steps code (.running (Allocation.startFrame before (frame n value).locals heap))
        [.alloc 2 (n * 8 + 8)] (.running final) ∧
      HeapRel (SizedBufferHeap.allocate prior n value) final.heap ∧
      EnvRel (.owner 2 :: env n value) (.copy ⟨8, false⟩ :: inputs) final ∧
      (∀ slot, slot < (frame n value).locals.size → final.locals[slot]? = (frame n value).locals[slot]?) ∧
      final.block = 0 ∧ final.index = 0 := by
  apply compact_to_mir compiled (by rfl) inputs_related prior_related compact_run
  · change 3 ≤ 512; decide
  · rw [cellCount_allocate, prior_cells]; omega
  · simpa [SizedBufferHeap.allocate, HeapLeases.put, prior_objects] using hv

theorem zero_run :
    ∃ final, Steps code (.running (Allocation.startFrame before (frame 0 0).locals heap))
      [.alloc 2 8] (.running final) ∧ HeapRel (SizedBufferHeap.allocate prior 0 0) final.heap := by
  obtain ⟨final, run, related, _⟩ := generated_run (n := 0) (value := 0) (by decide) (by decide)
  exact ⟨final, run, related⟩

theorem capacity_run :
    ∃ final, Steps code (.running (Allocation.startFrame before (frame 4092 (2^63-1)).locals heap))
      [.alloc 2 (4092 * 8 + 8)] (.running final) ∧
      HeapRel (SizedBufferHeap.allocate prior 4092 (2^63-1)) final.heap := by
  obtain ⟨final, run, related, _⟩ := generated_run (n := 4092) (value := 2^63-1) (by decide) (by decide)
  exact ⟨final, run, related⟩

structure Observation where
  block : Nat
  index : Nat
  heap : Array Object
  events : List Event
  preserved : Option Value
  owner : Option Value
  deriving DecidableEq, Repr

def observe (fuel n value : Nat) : Option Observation := do
  let out ← runFor fuel code (.running (Allocation.startFrame before (frame n value).locals heap))
  let .running f := out.machine | none
  return ⟨f.block, f.index, f.heap, out.events, f.locals[0]!, f.locals[8]!⟩

theorem executable_zero :
    observe 13 0 0 = some ⟨0, 0, heap.push ⟨true, MirBuffer.cells 0 0 0⟩,
      [.alloc 2 8], some (.i64 777), some (.pointer 2 0)⟩ := by decide +kernel

theorem executable_two :
    observe 25 2 19 = some ⟨0, 0, heap.push ⟨true, MirBuffer.cells 2 19 2⟩,
      [.alloc 2 24], some (.i64 777), some (.pointer 2 0)⟩ := by decide +kernel

/-- A preexisting original Core allocation root is compacted and then lowered,
with no supplied MIR snapshot association. -/
def sourceBefore : Code := ⟨#[.i64, .u64, .u64, .i64], #[retBlock]⟩
def sourceInputs : List Operand := [.copy ⟨3, false⟩, .copy ⟨2, false⟩, .copy ⟨1, false⟩]
def sourceTerm : SizedErasure.Term := .allocate (.var 2) (.var 0)
def sourceCode : Code := Allocation.build sourceBefore 0 (.copy ⟨1, false⟩) (.copy ⟨3, false⟩)
def sourceFrame (n i value : Nat) : Frame :=
  ⟨0, 0, #[some (.i64 777), some (.u64 n), some (.u64 i), some (.i64 value)], #[]⟩
def sourceEnv (n i value : Nat) : SizedErasure.Env := [.scalar value, .nat i, .nat n]

theorem source_compacted :
    SizedErasure.compileTarget SizedCoreExamples.graph 128 [true, true, true] 39 = some sourceTerm := rfl

theorem source_lowered : lower sourceBefore 0 sourceInputs sourceTerm = some sourceCode := by decide +kernel

theorem source_inputs_related : EnvRel (sourceEnv n i value) sourceInputs (sourceFrame n i value) :=
  .keep rfl (.keep rfl (.keep rfl .nil))

theorem source_env_erased : SizedErasure.EnvRel [true, true, true]
    (SizedCoreExamples.inputEnv n i value) (sourceEnv n i value) :=
  .consKeep (.scalar value) (.consKeep (.nat i) (.consKeep (.nat n) .nil))

theorem original_core_to_generated (hn : n ≤ 4095) (hv : value < scalarBound) :
    ∃ final,
      Steps sourceCode (.running (Allocation.startFrame sourceBefore (sourceFrame n i value).locals #[]))
        [.alloc 0 (n * 8 + 8)] (.running final) ∧
      HeapRel (SizedCoreExamples.allocated n value) final.heap ∧
      EnvRel (.owner 0 :: sourceEnv n i value) (.copy ⟨8, false⟩ :: sourceInputs) final ∧
      (∀ slot, slot < (sourceFrame n i value).locals.size → final.locals[slot]? = (sourceFrame n i value).locals[slot]?) ∧
      final.block = 0 ∧ final.index = 0 := by
  apply source_to_mir source_compacted source_lowered (by rfl) source_env_erased
    source_inputs_related HeapRel.empty (SizedCoreExamples.allocation_run n i value)
  · change 1 ≤ 512; decide
  · change cellCount (SizedBufferHeap.allocate SizedBufferHeap.empty n value) ≤ 4096
    rw [cellCount_allocate]
    have emptyCount : cellCount SizedBufferHeap.empty = 0 := rfl
    rw [emptyCount]
    omega
  · simpa [SizedCoreExamples.allocated, SizedBufferHeap.allocate, SizedBufferHeap.empty,
      HeapLeases.empty, HeapLeases.put] using hv

theorem bad_exit_rejected : lower before 2 inputs term = none := by decide +kernel

theorem local_budget_rejected :
    lower { before with locals := Array.replicate 503 .i64 } 0 inputs term = none := by decide +kernel

theorem block_budget_rejected :
    lower { before with blocks := Array.replicate 507 retBlock } 0 inputs term = none := by decide +kernel

theorem dereference_rejected :
    lower before 0 [.copy ⟨3, true⟩, .copy ⟨2, false⟩] term = none := by decide +kernel

theorem natural_overflow_rejected :
    lower before 0 inputs (.allocate (.literal (2^64)) (.literal 0)) = none := by decide +kernel

theorem payload_overflow_rejected :
    lower before 0 inputs (.allocate (.literal 0) (.literal (2^63))) = none := by decide +kernel

theorem mistyped_input_rejected :
    lower { before with locals := #[.i64, .unit, .i64, .i64] } 0 inputs term = none := by decide +kernel

theorem malformed_old_block_rejected :
    lower { before with blocks := #[retBlock, ⟨#[], .goto 99⟩] } 0 inputs term = none := by decide +kernel

theorem unsupported_free_rejected : lower before 0 inputs (.free 0 (.scalar 0)) = none := rfl

/-- Alias substitution alone does not reflect strict evaluation of an unused,
ill-typed argument. The translation theorem deliberately requires a source run. -/
theorem unused_bad_argument_lowered :
    lowerNat [.constant (.i64 1)] (.letE (.var 0) (.literal 2)) = some (.constant (.u64 2)) := by decide +kernel

theorem unused_bad_argument_not_evaluated :
    ¬ SizedErasure.NatEval [.scalar 1] (.letE (.var 0) (.literal 2)) n := by
  intro h
  cases h with
  | letE first _ =>
    cases first with
    | var lookup => simp at lookup

end Jihoo.SizedMirExamples
