import Jihoo.SizedMirLinearValueBounds
import Jihoo.SizedMirExamples

/-! One generated program handles arbitrary two-buffer lengths, lexical owner
aliases, prior live/dead objects and release order. Safety is not inferred from
MIR validation alone: a deliberate double-free distinguishes those premises. -/
namespace Jihoo.SizedMirLinearExamples
open BoundedMir SizedMir SizedMir.Linear
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def inputTypes : Array Ty := #[.i64, .u64, .u64, .i64, .i64]
def inputs : List Operand := [.copy ⟨1,false⟩, .copy ⟨2,false⟩, .copy ⟨3,false⟩, .copy ⟨4,false⟩]
def term : SizedErasure.Term :=
  .app (.allocate (.var 0) (.var 2))
    (.app (.allocate (.var 2) (.var 3))
      (.app (.var 1) (.free 0 (.free 1 (.var 6)))))
def fragment : Fragment := (compile inputs ((inputKinds inputTypes inputs).getD []) 5 1 0 term).getD (pureFragment (.constant (.i64 0)))
def code : Code := program inputTypes fragment

theorem compiled : lowerProgram inputTypes inputs term = some fragment := by decide +kernel
theorem sizes : fragment.locals.size = 22 ∧ fragment.blocks.size = 14 := by decide +kernel

def prior : SizedBufferHeap.State := SizedMirExamples.prior
def first (n fill : Nat) : SizedBufferHeap.State := SizedBufferHeap.allocate prior n fill
def second (n m fill : Nat) : SizedBufferHeap.State := SizedBufferHeap.allocate (first n fill) m fill
def finalState (n m fill : Nat) : SizedBufferHeap.State :=
  SizedBufferHeap.release (SizedBufferHeap.release (second n m fill) 2) 3

def env (n m fill result : Nat) : SizedErasure.Env := [.nat n,.nat m,.scalar fill,.scalar result]
def frame (n m fill result : Nat) : Frame :=
  ⟨77, 9, #[some (.i64 777),some (.u64 n),some (.u64 m),some (.i64 fill),some (.i64 result)], materialize prior⟩
def events (n m fill : Nat) : List SizedBufferHeap.Event :=
  [.alloc 2 n fill,.alloc 3 m fill,.free 2,.free 3]

theorem prior_valid : SizedBufferHeap.Valid prior := by
  apply SizedBufferHeap.step_valid
    (SizedBufferHeap.step_valid (SizedBufferHeap.step_valid SizedBufferHeap.empty_valid
      (SizedBufferHeap.Step.alloc (n := 1) (v := 73))) (SizedBufferHeap.Step.alloc (n := 0) (v := 5)))
  exact .free (by decide) (by intro token; simp [SizedBufferHeap.allocate, SizedBufferHeap.empty, HeapLeases.empty])

theorem compact_run : SizedErasure.Eval (env n m fill result) term prior (.scalar result)
    (events n m fill) (finalState n m fill) := by
  apply SizedErasure.Eval.app (.allocate (.var rfl) (.var rfl))
  apply SizedErasure.Eval.app (.allocate (.var rfl) (.var rfl))
  apply SizedErasure.Eval.app (.var rfl)
  exact .free rfl (.free rfl (.var rfl))

theorem safe_run : SizedBufferHeap.Steps prior (events n m fill) (finalState n m fill) := by
  apply SizedBufferHeap.Steps.cons .alloc
  apply SizedBufferHeap.Steps.cons .alloc
  apply SizedBufferHeap.Steps.cons (.free (by simp [second, first, prior, SizedMirExamples.prior,
    SizedBufferHeap.allocate, SizedBufferHeap.release, SizedBufferHeap.empty, HeapLeases.empty, HeapLeases.put]) (by intro token; simp [second, first, prior,
    SizedMirExamples.prior, SizedBufferHeap.allocate, SizedBufferHeap.release, SizedBufferHeap.empty, HeapLeases.empty]))
  apply SizedBufferHeap.Steps.cons (.free (by simp [second, first, prior, SizedMirExamples.prior,
    SizedBufferHeap.allocate, SizedBufferHeap.release, SizedBufferHeap.empty, HeapLeases.empty, HeapLeases.put]) (by intro token; simp [second, first, prior,
    SizedMirExamples.prior, SizedBufferHeap.allocate, SizedBufferHeap.release, SizedBufferHeap.empty, HeapLeases.empty]))
  exact .nil

theorem final_cells : cellCount (finalState n m fill) = 3 + n + 1 + m + 1 := by
  simp only [finalState, cellCount_release, second, first, cellCount_allocate]
  rfl

theorem final_bounds (capacity : n + m ≤ 4091) (payload : fill < scalarBound) :
    Trace.Bounds (finalState n m fill) := by
  constructor
  · change 4 ≤ 512; decide
  · rw [final_cells]; omega
  · intro objectId old
    change objectId < 4 at old
    have alternatives : objectId = 0 ∨ objectId = 1 ∨ objectId = 2 ∨ objectId = 3 := by omega
    rcases alternatives with rfl | rfl | rfl | rfl <;>
      simp_all [finalState, second, first, prior, SizedMirExamples.prior, SizedBufferHeap.release,
        SizedBufferHeap.allocate, SizedBufferHeap.empty, HeapLeases.put, HeapLeases.empty,
        payload, scalarBound]

theorem related_inputs : EnvRel (env n m fill result) inputs (frame n m fill result) :=
  .keep rfl (.keep rfl (.keep rfl (.keep rfl .nil)))

theorem generated_run (capacity : n + m ≤ 4091) (payload : fill < scalarBound) :
    ∃ final, Steps code
      (.running (start (programFrame fragment (frame n m fill result)) 1))
      [.alloc 2 (n*8+8), .alloc 3 (m*8+8), .free 2, .free 3] (.returned result final) ∧
      HeapRel (finalState n m fill) final.heap ∧
      final.locals.size = 27 ∧
      (∀ i, i < 5 → i ≠ 0 → final.locals[i]? = (frame n m fill result).locals[i]?) := by
  simpa [code, term, entry, blockCost, events, lifecycle, frame, program, inputTypes, sizes] using
    program_run compiled (f := frame n m fill result) rfl related_inputs rfl
      (HeapRel.materialize_related prior) prior_valid compact_run safe_run (final_bounds capacity payload)

theorem inputs_bounded (hn : n < wordBound) (hm : m < wordBound)
    (hf : fill < scalarBound) (hr : result < scalarBound) : EnvBounded (env n m fill result) := by
  simp [EnvBounded, env, ValueBounded, hn, hm, hf, hr]

theorem generated_scalar_width (hn : n < wordBound) (hm : m < wordBound)
    (hf : fill < scalarBound) (hr : result < scalarBound) :
    ValueBounded (.scalar result) := by
  apply (lowerProgram_shape compiled).1.value_bounded
    (inputs_bounded hn hm hf hr) prior_valid compact_run safe_run
  intro objectId old
  change objectId < 4 at old
  have alternatives : objectId = 0 ∨ objectId = 1 ∨ objectId = 2 ∨ objectId = 3 := by omega
  rcases alternatives with rfl | rfl | rfl | rfl <;>
    simp_all [finalState, second, first, prior, SizedMirExamples.prior, SizedBufferHeap.release,
      SizedBufferHeap.allocate, SizedBufferHeap.empty, HeapLeases.put, HeapLeases.empty,
      scalarBound]

structure Observation where
  result : Nat
  heap : Array Object
  events : List Event
  retained : Option Value
  deriving DecidableEq, Repr

def observe (fuel n m fill result : Nat) : Option Observation := do
  let out ← runFor fuel code (.running (start (programFrame fragment (frame n m fill result)) 1))
  let .returned value final := out.machine | none
  return ⟨value, final.heap, out.events, final.locals[4]!⟩

theorem executable_zero : observe 30 0 0 19 42 =
    some ⟨42, materialize (finalState 0 0 19), [.alloc 2 8,.alloc 3 8,.free 2,.free 3], some (.i64 42)⟩ := by
  decide +kernel

theorem executable_nonzero : observe 48 2 1 19 42 =
    some ⟨42, materialize (finalState 2 1 19), [.alloc 2 24,.alloc 3 16,.free 2,.free 3], some (.i64 42)⟩ := by
  decide +kernel

theorem capacity_run : ∃ final, Steps code
    (.running (start (programFrame fragment (frame 4091 0 (2^63-1) 42)) 1))
    [.alloc 2 (4091*8+8), .alloc 3 8,.free 2,.free 3] (.returned 42 final) ∧
    HeapRel (finalState 4091 0 (2^63-1)) final.heap := by
  obtain ⟨final, run, heap, _⟩ := generated_run (n := 4091) (m := 0) (fill := 2^63-1) (result := 42)
    (by decide) (by decide)
  exact ⟨final, run, heap⟩

theorem branch_kind_mismatch_rejected : lowerProgram inputTypes inputs (.ifLt (.literal 0) (.literal 1) (.scalar 1) (.natural 2)) = none := by decide +kernel
theorem lend_wrong_owner_type_rejected : lowerProgram inputTypes inputs (.lend 0 (.literal 0) (.scalar 1)) = none := by decide +kernel
theorem owned_lend_wrong_owner_type_rejected : lowerProgram inputTypes inputs (.ownedLend 0 (.literal 0) (.literal 0) (.scalar 1)) = none := by decide +kernel
theorem missing_slot_rejected : lowerProgram inputTypes inputs (.var 4) = none := by decide +kernel
theorem wrong_input_type_rejected : lowerProgram #[.i64,.i64,.u64,.i64,.i64] inputs term = none := by decide +kernel
theorem wrong_return_type_rejected : lowerProgram inputTypes inputs (.allocate (.literal 0) (.literal 1)) = none := by decide +kernel
theorem local_budget_rejected : lowerProgram (Array.replicate 491 .i64) []
    (.app (.allocate (.literal 0) (.literal 1)) (.app (.allocate (.literal 0) (.literal 1)) (.free 1 (.free 0 (.scalar 0))))) = none := by decide +kernel

theorem dereference_input_rejected : lowerProgram inputTypes
    [.copy ⟨1,true⟩,.copy ⟨2,false⟩,.copy ⟨3,false⟩,.copy ⟨4,false⟩] term = none := by decide +kernel

theorem scalar_literal_overflow_rejected : lowerProgram inputTypes inputs (.scalar scalarBound) = none := by decide +kernel

theorem natural_return_rejected : lowerProgram inputTypes inputs (.natural 7) = none := by decide +kernel

def pureCode : Code := program #[.i64] (pureFragment (.constant (.i64 99)))

theorem zero_fragment_compiled : lowerProgram #[.i64] [] (.scalar 99) =
    some (pureFragment (.constant (.i64 99))) := by decide +kernel

theorem zero_fragment_return : runFor 2 pureCode (.running ⟨0,0,#[none],#[]⟩) =
    some ⟨.returned 99 ⟨0,1,#[some (.i64 99)],#[]⟩,[]⟩ := by decide +kernel

def doubleFree : SizedErasure.Term := .free 0 (.free 0 (.scalar 7))
def doubleFreeFragment : Fragment := (compile [.copy ⟨1,false⟩] [.pointer] 2 1 0 doubleFree).getD (pureFragment (.constant (.i64 0)))

theorem double_free_static_valid : lowerProgram #[.i64,.ptr] [.copy ⟨1,false⟩] doubleFree = some doubleFreeFragment := by decide +kernel

theorem double_free_no_safe_trace : ¬ SizedBufferHeap.Steps prior [.free 0,.free 0] t := by
  intro run
  cases run with
  | cons first rest =>
    cases first with
    | free live unborrowed =>
      cases rest with
      | cons second tail =>
        cases second with
        | free liveAgain unborrowedAgain =>
          simp [SizedBufferHeap.release, HeapLeases.put] at liveAgain

/-- An original Core graph with an allocation/application/free body. The change
selects the fixture's existing release branch directly; no native-exporter
association for this derived graph is asserted. -/
def sourceGraph : ScopedLend.Graph.Graph :=
  DependentBufferGraph.graph.set! 36 (.lam false 11 34)
def sourceTerm : SizedErasure.Term :=
  .app (.allocate (.var 2) (.var 0)) (.free 0 (.scalar 99))
def sourceTypes : Array Ty := #[.i64,.u64,.u64,.i64]
def sourceInputs : List Operand := [.copy ⟨3,false⟩,.copy ⟨2,false⟩,.copy ⟨1,false⟩]
def sourceFragment : Fragment := (compile sourceInputs ((inputKinds sourceTypes sourceInputs).getD []) 4 1 0 sourceTerm).getD (pureFragment (.constant (.i64 0)))
def sourceFrame (n i value : Nat) : Frame :=
  ⟨0,0,#[some (.i64 777),some (.u64 n),some (.u64 i),some (.i64 value)],#[]⟩
def sourceEnv (n i value : Nat) : SizedErasure.Env := [.scalar value,.nat i,.nat n]

theorem source_compacted : SizedErasure.compileTarget sourceGraph 128 [true,true,true] 40 = some sourceTerm := by
  decide +kernel

theorem source_lowered : lowerProgram sourceTypes sourceInputs sourceTerm = some sourceFragment := by decide +kernel

theorem source_typed (n i : Nat) :
    SizedCoreTyping.Typing sourceGraph (SizedCoreExamples.inputContext n i) [] 40 .scalar := by
  apply SizedCoreTyping.Typing.allocate (function := 36) (argument := 39) (domain := 11)
    (length := 37) (init := 38) (n := n) rfl rfl
  · exact ⟨10,rfl,DependentBufferIndices.Eval.var rfl rfl⟩
  · rfl
  · exact DependentBufferIndices.Eval.var rfl rfl
  · exact .var rfl rfl
  · exact .free (slot := 0) rfl rfl rfl (by simp) (.literal rfl (by decide))

theorem source_run (n i value : Nat) :
    SizedCoreExecution.Eval sourceGraph (SizedCoreExamples.inputEnv n i value) 40 SizedBufferHeap.empty
      (.scalar 99) [.alloc 0 n value,.free 0] (SizedCoreExamples.noReadFinal n value) := by
  apply SizedCoreExecution.Eval.app rfl rfl
    (.allocate rfl (DependentBufferIndices.Eval.var rfl rfl) (.var rfl rfl))
  exact .free rfl rfl rfl (.scalar rfl)

theorem source_inputs_related : EnvRel (sourceEnv n i value) sourceInputs (sourceFrame n i value) :=
  .keep rfl (.keep rfl (.keep rfl .nil))

theorem source_env_erased : SizedErasure.EnvRel [true,true,true]
    (SizedCoreExamples.inputEnv n i value) (sourceEnv n i value) :=
  .consKeep (.scalar value) (.consKeep (.nat i) (.consKeep (.nat n) .nil))

theorem source_bounds (capacity : n ≤ 4095) (payload : value < scalarBound) :
    Trace.Bounds (SizedCoreExamples.noReadFinal n value) := by
  constructor
  · change 1 ≤ 512; decide
  · simp only [SizedCoreExamples.noReadFinal, cellCount_release, SizedCoreExamples.allocated, cellCount_allocate]
    have empty : cellCount SizedBufferHeap.empty = 0 := rfl
    rw [empty]; omega
  · intro objectId old
    change objectId < 1 at old
    have zero : objectId = 0 := by omega
    subst objectId
    simpa [SizedCoreExamples.noReadFinal, SizedCoreExamples.allocated,
      SizedBufferHeap.release, SizedBufferHeap.allocate, SizedBufferHeap.empty,
      HeapLeases.empty, HeapLeases.put] using payload

/-- Safety of the release is obtained from the actual source typing derivation,
not supplied as a separate event-trace premise. -/
theorem original_core_to_generated (capacity : n ≤ 4095) (payload : value < scalarBound) :
    ∃ final, Steps (program sourceTypes sourceFragment)
      (.running (start (programFrame sourceFragment (sourceFrame n i value)) 1))
      [.alloc 0 (n*8+8),.free 0] (.returned 99 final) ∧
      HeapRel (SizedCoreExamples.noReadFinal n value) final.heap := by
  obtain ⟨final, target, heap, _⟩ := typed_source_run source_compacted source_lowered
    (source_typed n i) source_env_erased (SizedCoreExamples.input_agrees n i value)
    SizedCoreExamples.empty_layout SizedBufferHeap.empty_valid LinearHeapPrograms.empty_owns
    (f := sourceFrame n i value) rfl source_inputs_related rfl HeapRel.empty (source_run n i value)
    (source_bounds capacity payload)
  exact ⟨final, target, heap⟩

/-- Source typing also supplies an execution; resource adequacy is discharged
using determinism against the explicit source execution. -/
theorem typed_source_totality (capacity : n ≤ 4095) (payload : value < scalarBound) :
    ∃ result events t final,
      SizedCoreExecution.Eval sourceGraph (SizedCoreExamples.inputEnv n i value) 40 SizedBufferHeap.empty
        (.scalar result) events t ∧
      Steps (program sourceTypes sourceFragment)
        (.running (start (programFrame sourceFragment (sourceFrame n i value)) 1))
        (lifecycle events) (.returned result final) ∧ HeapRel t final.heap ∧
      SizedCoreTyping.Account [] (.scalar result) events := by
  apply typed_source_total source_compacted source_lowered (source_typed n i) source_env_erased
    (SizedCoreExamples.input_agrees n i value) SizedCoreExamples.empty_layout SizedBufferHeap.empty_valid
    LinearHeapPrograms.empty_owns rfl source_inputs_related rfl HeapRel.empty
  intro result events t run
  obtain ⟨_,_,same⟩ := run.deterministic (source_run n i value)
  rw [same]
  exact source_bounds capacity payload

end Jihoo.SizedMirLinearExamples
