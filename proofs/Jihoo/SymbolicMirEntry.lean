import Jihoo.SymbolicCoreClosing
import Jihoo.SizedMirEntryAdequacy

/-! Constructor-driven symbolic typing reaches computed ghost compaction and
checked MIR entry. Closing, inventory, resource and ABI premises remain explicit;
no native compiler correctness or full Core soundness is asserted. -/
namespace Jihoo.SymbolicMirEntry
open BoundedMir SizedMir SizedMir.Entry SizedBufferContext SizedCoreTyping LinearHeapPrograms

theorem typed_source_run
    (compacted : SizedErasure.compileTarget graph fuel (SizedErasure.compactEnv sourceEnv).1 root = some term)
    (success : lowerProgram inputTypes abi term = some fragment)
    (typed : SymbolicCoreTyping.Typing graph symbolic symbolicSizes root .scalar)
    (closing : SymbolicCoreContext.Closes symbolic ctx)
    (inventory : SymbolicCoreContext.SizesEval (naturalEnv ctx) symbolicSizes sizes)
    (agree : Agrees ctx owners sourceEnv) (layout : Layout SizedBufferHeap.empty owners sizes)
    (owned : Owns SizedBufferHeap.empty.heap owners)
    (admission : entryFrame (program inputTypes term fragment) abi
      ((SizedErasure.compactEnv sourceEnv).2.map toMir) = some f)
    (source : SizedCoreExecution.Eval graph sourceEnv root SizedBufferHeap.empty (.scalar value) events t)
    (bounded : Trace.Bounds t) :
    ∃ final, Steps (program inputTypes term fragment) (.running f)
      (lifecycle events) (.returned value final) ∧ HeapRel t final.heap ∧
      final.locals.size = (program inputTypes term fragment).locals.size ∧
      (∀ i, i < inputTypes.size → i ≠ 0 → final.locals[i]? = f.locals[i]?) ∧ value < scalarBound := by
  exact SizedMir.Entry.typed_source_run compacted success (typed.instantiate closing inventory trivial) agree layout owned admission source bounded

theorem typed_source_total
    (compacted : SizedErasure.compileTarget graph fuel (SizedErasure.compactEnv sourceEnv).1 root = some term)
    (success : lowerProgram inputTypes abi term = some fragment)
    (typed : SymbolicCoreTyping.Typing graph symbolic symbolicSizes root .scalar)
    (closing : SymbolicCoreContext.Closes symbolic ctx)
    (inventory : SymbolicCoreContext.SizesEval (naturalEnv ctx) symbolicSizes sizes)
    (agree : Agrees ctx owners sourceEnv) (layout : Layout SizedBufferHeap.empty owners sizes)
    (owned : Owns SizedBufferHeap.empty.heap owners)
    (admission : entryFrame (program inputTypes term fragment) abi
      ((SizedErasure.compactEnv sourceEnv).2.map toMir) = some f)
    (resources : ∀ value events t,
      SizedCoreExecution.Eval graph sourceEnv root SizedBufferHeap.empty value events t → Trace.Bounds t) :
    ∃ value events t final,
      SizedCoreExecution.Eval graph sourceEnv root SizedBufferHeap.empty (.scalar value) events t ∧
      Steps (program inputTypes term fragment) (.running f) (lifecycle events) (.returned value final) ∧
      HeapRel t final.heap ∧ Account owners (.scalar value) events ∧ value < scalarBound ∧
      final.locals.size = (program inputTypes term fragment).locals.size ∧
      (∀ i, i < inputTypes.size → i ≠ 0 → final.locals[i]? = f.locals[i]?) := by
  exact SizedMir.Entry.typed_source_total compacted success (typed.instantiate closing inventory trivial) agree layout owned admission resources

theorem typed_source_adequacy
    (compacted : SizedErasure.compileTarget graph fuel (SizedErasure.compactEnv sourceEnv).1 root = some term)
    (success : lowerProgram inputTypes abi term = some fragment)
    (typed : SymbolicCoreTyping.Typing graph symbolic symbolicSizes root .scalar)
    (closing : SymbolicCoreContext.Closes symbolic ctx)
    (inventory : SymbolicCoreContext.SizesEval (naturalEnv ctx) symbolicSizes sizes)
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
  exact SizedMir.Entry.typed_source_adequacy compacted success (typed.instantiate closing inventory trivial) agree layout owned admission resources

theorem typed_source_return
    (compacted : SizedErasure.compileTarget graph fuel (SizedErasure.compactEnv sourceEnv).1 root = some term)
    (success : lowerProgram inputTypes abi term = some fragment)
    (typed : SymbolicCoreTyping.Typing graph symbolic symbolicSizes root .scalar)
    (closing : SymbolicCoreContext.Closes symbolic ctx)
    (inventory : SymbolicCoreContext.SizesEval (naturalEnv ctx) symbolicSizes sizes)
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
  exact SizedMir.Entry.typed_source_return compacted success (typed.instantiate closing inventory trivial) agree layout owned admission resources observed

end Jihoo.SymbolicMirEntry
