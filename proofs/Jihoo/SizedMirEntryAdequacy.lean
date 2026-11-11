import Jihoo.SizedMirEntryProgram
import Jihoo.BoundedMirExecutionAdequacy

/-! Checked-entry adequacy is obtained from source totality, not a target run
hypothesis. Heap correspondence is asserted at the completed return only. -/
namespace Jihoo.SizedMir.Entry
open BoundedMir Linear SizedBufferContext SizedCoreTyping LinearHeapPrograms

/-- Every finite running prefix can continue, every fuel budget gives a partial
result, and sufficiently large fuel gives the exact source lifecycle and scalar. -/
theorem typed_source_adequacy
    (compacted : SizedErasure.compileTarget graph fuel (SizedErasure.compactEnv sourceEnv).1 root = some term)
    (success : lowerProgram inputTypes abi term = some fragment)
    (typed : Typing graph ctx sizes root .scalar)
    (agree : Agrees ctx owners sourceEnv) (layout : Layout SizedBufferHeap.empty owners sizes)
    (owned : Owns SizedBufferHeap.empty.heap owners)
    (admission : entryFrame (program inputTypes term fragment) abi
      ((SizedErasure.compactEnv sourceEnv).2.map toMir) = some f)
    (resources : ∀ value events t,
      SizedCoreExecution.Eval graph sourceEnv root SizedBufferHeap.empty value events t → Trace.Bounds t) :
    ∃ value events t final,
      SizedCoreExecution.Eval graph sourceEnv root SizedBufferHeap.empty (.scalar value) events t ∧
      SizedBufferHeap.Steps SizedBufferHeap.empty events t ∧ SizedBufferHeap.Valid t ∧
      HeapRel t final.heap ∧ Account owners (.scalar value) events ∧ value < scalarBound ∧
      (∀ preEvents middle, Steps (program inputTypes term fragment) (.running f) preEvents (.running middle) →
        (∃ suffix, lifecycle events = preEvents ++ suffix ∧
          Steps (program inputTypes term fragment) (.running middle) suffix (.returned value final)) ∧
        (∃ next, rawTick (program inputTypes term fragment) middle = some next)) ∧
      (∀ fuel, ∃ out, runFor fuel (program inputTypes term fragment) (.running f) = some out) ∧
      (∃ bound, ∀ fuel, bound ≤ fuel →
        runFor fuel (program inputTypes term fragment) (.running f) =
          some ⟨.returned value final, lifecycle events⟩) ∧
      (∃ bound, ∀ fuel, bound ≤ fuel →
        execute fuel (program inputTypes term fragment) f = some ⟨value, final, lifecycle events⟩) ∧
      (∀ actual actualEvents actualFinal,
        Steps (program inputTypes term fragment) (.running f) actualEvents (.returned actual actualFinal) →
        actual = value ∧ actualFinal = final ∧ actualEvents = lifecycle events) := by
  obtain ⟨value, events, t, final, source, target, heap, account, bound, _, _⟩ :=
    typed_source_total compacted success typed agree layout owned admission resources
  have safe := (typed.every_run_safe agree layout SizedBufferHeap.empty_valid owned source).1
  refine ⟨value, events, t, final, source, safe, SizedBufferHeap.steps_valid SizedBufferHeap.empty_valid safe,
    heap, account, bound, ?_, target.runFor_total, target.runFor_complete, target.execute_complete, ?_⟩
  · intro preEvents middle pre
    exact ⟨target.prefix_completion pre, target.running_rawTick pre⟩
  · intro actual actualEvents actualFinal actualRun
    exact actualRun.returned_deterministic target


/-- Any observed MIR return agrees with a safe, accounted source execution.
Source totality supplies the comparison run; the observed return is not a
premise of termination or progress. -/
theorem typed_source_return
    (compacted : SizedErasure.compileTarget graph fuel (SizedErasure.compactEnv sourceEnv).1 root = some term)
    (success : lowerProgram inputTypes abi term = some fragment)
    (typed : Typing graph ctx sizes root .scalar)
    (agree : Agrees ctx owners sourceEnv) (layout : Layout SizedBufferHeap.empty owners sizes)
    (owned : Owns SizedBufferHeap.empty.heap owners)
    (admission : entryFrame (program inputTypes term fragment) abi
      ((SizedErasure.compactEnv sourceEnv).2.map toMir) = some f)
    (resources : ∀ value events t,
      SizedCoreExecution.Eval graph sourceEnv root SizedBufferHeap.empty value events t → Trace.Bounds t)
    (observed : Steps (program inputTypes term fragment) (.running f)
      actualEvents (.returned actual actualFinal)) :
    ∃ events t,
      SizedCoreExecution.Eval graph sourceEnv root SizedBufferHeap.empty (.scalar actual) events t ∧
      SizedBufferHeap.Steps SizedBufferHeap.empty events t ∧ SizedBufferHeap.Valid t ∧
      actualEvents = lifecycle events ∧ HeapRel t actualFinal.heap ∧
      Account owners (.scalar actual) events ∧ actual < scalarBound := by
  obtain ⟨value, events, t, final, source, target, heap, account, bound, _, _⟩ :=
    typed_source_total compacted success typed agree layout owned admission resources
  obtain ⟨rfl, rfl, rfl⟩ := observed.returned_deterministic target
  have safe := (typed.every_run_safe agree layout SizedBufferHeap.empty_valid owned source).1
  exact ⟨events, t, source, safe, SizedBufferHeap.steps_valid SizedBufferHeap.empty_valid safe,
    rfl, heap, account, bound⟩

end Jihoo.SizedMir.Entry
