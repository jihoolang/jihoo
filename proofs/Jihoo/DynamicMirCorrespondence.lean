import Jihoo.SizedCoreExamples
import Jihoo.SizedErasureCompiler
import Jihoo.SizedErasureForward
import Jihoo.DynamicMirExecution

/-! Result and allocation/free correspondence for the fixed dependent-buffer
fixture. Compaction is proved for the original source body (node 40). The
association of that source snapshot with the actual emitted MIR snapshot is
checked externally, not proved as a general lowering theorem. Lease/read events
are erased by an explicit observation function; no store/read trace equality
is asserted. MIR uses successful abstract allocation and nonnegative I64s. -/
namespace Jihoo.DynamicMirCorrespondence
open SizedErasure

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

abbrev graph := SizedCoreExamples.graph

def inputMask : Mask := [true, true, true]
def runtimeEnv (n i value : Nat) : Env := [.scalar value, .nat i, .nat n]

/-- Both branches of the unchanged graph are compiled. The true branch drops
its ghost comparison proof, retaining only the owner and scalar payload. -/
def target : Term :=
  .app (.allocate (.var 2) (.var 0))
    (.ifLt (.var 2) (.var 3)
      (.lend 0 (.var 3) (.free 0 (.var 1)))
      (.free 0 (.scalar 99)))

theorem compiled : compileTarget graph 128 inputMask 40 = some target := by rfl

theorem erased : Erases graph inputMask 40 target := compileTarget_correct compiled

theorem inputs_related (n i value : Nat) :
    EnvRel inputMask (SizedCoreExamples.inputEnv n i value) (runtimeEnv n i value) :=
  .consKeep (.scalar value) (.consKeep (.nat i) (.consKeep (.nat n) .nil))

theorem target_run (n i value : Nat) :
    Eval (runtimeEnv n i value) target SizedBufferHeap.empty
      (.scalar (if i < n then value else 99))
      (SizedCoreExamples.bodyEvents n i value) (SizedCoreExamples.bodyFinal n i value) := by
  obtain ⟨result, eq, run⟩ := erased.forward (inputs_related n i value)
    (SizedCoreExamples.body_run n i value)
  have same : result = .scalar (if i < n then value else 99) := Value.embed_inj.mp eq.symm
  simpa [same] using run

theorem every_target_exact
    (run : Eval (runtimeEnv n i value) target SizedBufferHeap.empty result events t) :
    result = .scalar (if i < n then value else 99) ∧
      events = SizedCoreExamples.bodyEvents n i value ∧ t = SizedCoreExamples.bodyFinal n i value := by
  obtain ⟨resultEq, eventEq, stateEq⟩ := SizedCoreExamples.every_run_exact
    (erased.backward (inputs_related n i value) run)
  exact ⟨Value.embed_inj.mp resultEq, eventEq, stateEq⟩

theorem every_target_no_live
    (run : Eval (runtimeEnv n i value) target SizedBufferHeap.empty result events t) :
    ∀ x, t.heap.live x = false :=
  SizedCoreExamples.every_run_releases_all (erased.backward (inputs_related n i value) run)

theorem every_target_safe
    (run : Eval (runtimeEnv n i value) target SizedBufferHeap.empty result events t) :
    SizedBufferHeap.Steps SizedBufferHeap.empty events t ∧ SizedBufferHeap.Valid t ∧
      SizedCoreTyping.Post .scalar t result.embed :=
  erased.every_run_safe (inputs_related n i value) (SizedCoreExamples.body_typed n i)
    (SizedCoreExamples.input_agrees n i value) SizedCoreExamples.empty_layout
    SizedBufferHeap.empty_valid LinearHeapPrograms.empty_owns run

/-- Logical length n becomes n I64 cells and the allocator's one spare cell.
Only allocation and release are compared across the two heap models. -/
def lifecycle : List SizedBufferHeap.Event → List BoundedMir.Event
  | [] => []
  | .alloc object n _ :: rest => .alloc object (8 * (n + 1)) :: lifecycle rest
  | .free object :: rest => .free object :: lifecycle rest
  | _ :: rest => lifecycle rest

theorem body_lifecycle (n i value : Nat) :
    lifecycle (SizedCoreExamples.bodyEvents n i value) =
      [.alloc 0 (n * 8 + 8), .free 0] := by
  by_cases h : i < n <;>
    simp [SizedCoreExamples.bodyEvents, SizedCoreExamples.readEvents, lifecycle, h,
      Nat.add_mul, Nat.mul_comm]

/-- Existence in all three semantics for the same parameters. The MIR entry
is validated at its real U64/U64/I64 ABI; length is restricted by the abstract
allocator bound and payload by the nonnegative I64 representation. -/
theorem three_way_termination (hn : n ≤ 4095) (hi : i < BoundedMir.wordBound)
    (hv : value < BoundedMir.scalarBound) :
    BoundedMir.entryFrame DynamicMir.code DynamicMir.entry
        [.u64 n, .u64 i, .i64 value] = some (DynamicMir.inputs n i value) ∧
    SizedCoreExecution.Eval graph (SizedCoreExamples.inputEnv n i value) 40
      SizedBufferHeap.empty (.scalar (if i < n then value else 99))
      (SizedCoreExamples.bodyEvents n i value) (SizedCoreExamples.bodyFinal n i value) ∧
    Eval (runtimeEnv n i value) target SizedBufferHeap.empty
      (.scalar (if i < n then value else 99))
      (SizedCoreExamples.bodyEvents n i value) (SizedCoreExamples.bodyFinal n i value) ∧
    ∃ dest, BoundedMir.Steps DynamicMir.code (.running (DynamicMir.inputs n i value))
      (lifecycle (SizedCoreExamples.bodyEvents n i value))
      (.returned (if i < n then value else 99) (DynamicMir.finalFrame n i value dest)) := by
  refine ⟨DynamicMir.input_frame hn hi hv, SizedCoreExamples.body_run n i value,
    target_run n i value, ?_⟩
  rw [body_lifecycle]
  exact DynamicMir.terminates hn hv

/-- Arbitrary terminating executions agree in result and allocator lifecycle.
The source/compact event lists coincide exactly; only their explicit lifecycle
projection is identified with MIR, whose initialization stores have no source
event counterpart. Both abstract heaps are released on return. -/
theorem every_execution_agrees (hn : n ≤ 4095) (hv : value < BoundedMir.scalarBound)
    (source : SizedCoreExecution.Eval graph (SizedCoreExamples.inputEnv n i value) 40
      SizedBufferHeap.empty sourceResult sourceEvents sourceFinal)
    (compact : Eval (runtimeEnv n i value) target SizedBufferHeap.empty
      compactResult compactEvents compactFinal)
    (mir : BoundedMir.Steps DynamicMir.code (.running (DynamicMir.inputs n i value))
      mirEvents (.returned mirResult mirFinal)) :
    sourceResult = compactResult.embed ∧ compactResult = .scalar mirResult ∧
    sourceEvents = compactEvents ∧ lifecycle sourceEvents = mirEvents ∧
    (∀ x, sourceFinal.heap.live x = false) ∧
    (∀ x, compactFinal.heap.live x = false) ∧ BoundedMir.heapEmpty mirFinal = true := by
  obtain ⟨sr, se, _⟩ := SizedCoreExamples.every_run_exact source
  obtain ⟨cr, ce, _⟩ := every_target_exact compact
  obtain ⟨mr, me, _, empty⟩ := DynamicMir.every_return hn hv mir
  refine ⟨?_, ?_, se.trans ce.symm, ?_, SizedCoreExamples.every_run_releases_all source,
    every_target_no_live compact, empty⟩
  · rw [sr, cr]; rfl
  · rw [cr, mr]
  · rw [se, me, body_lifecycle]

/-- Every compact execution has a corresponding terminating MIR execution;
this conclusion is constructed, not conditional on the existence of a MIR run. -/
theorem compact_to_mir (hn : n ≤ 4095) (hv : value < BoundedMir.scalarBound)
    (compact : Eval (runtimeEnv n i value) target SizedBufferHeap.empty result events t) :
    ∃ mirResult frame,
      BoundedMir.Steps DynamicMir.code (.running (DynamicMir.inputs n i value))
        (lifecycle events) (.returned mirResult frame) ∧
      result = .scalar mirResult ∧ BoundedMir.heapEmpty frame = true := by
  obtain ⟨cr, ce, _⟩ := every_target_exact compact
  obtain ⟨dest, run⟩ := DynamicMir.terminates (i := i) hn hv
  refine ⟨_, _, ?_, cr, DynamicMir.final_no_live n i value dest⟩
  simpa [ce, body_lifecycle] using run

/-- Every returned MIR execution has source and compact executions with the
same result and projected allocator observations. Existence of either source
execution is proved here, rather than assumed as a premise. -/
theorem mir_to_compact (hn : n ≤ 4095) (hv : value < BoundedMir.scalarBound)
    (mir : BoundedMir.Steps DynamicMir.code (.running (DynamicMir.inputs n i value))
      mirEvents (.returned mirResult mirFinal)) :
    ∃ events t,
      SizedCoreExecution.Eval graph (SizedCoreExamples.inputEnv n i value) 40
        SizedBufferHeap.empty (.scalar mirResult) events t ∧
      Eval (runtimeEnv n i value) target SizedBufferHeap.empty (.scalar mirResult) events t ∧
      lifecycle events = mirEvents ∧ (∀ x, t.heap.live x = false) := by
  obtain ⟨resultEq, eventEq, _, _⟩ := DynamicMir.every_return hn hv mir
  refine ⟨SizedCoreExamples.bodyEvents n i value, SizedCoreExamples.bodyFinal n i value,
    ?_, ?_, ?_, SizedCoreExamples.body_final_no_live n i value⟩
  · rw [resultEq]
    exact SizedCoreExamples.body_run n i value
  · rw [resultEq]
    exact target_run n i value
  · rw [eventEq, body_lifecycle]

end Jihoo.DynamicMirCorrespondence
