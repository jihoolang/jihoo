import Jihoo.SizedMirLinearSimulation

/-! Completed scalar-returning programs generated from straight-line compact
syntax. The final validator checks the whole constructed MIR. Resource bounds
remain explicit, and source typing supplies release safety in the typed bridge. -/
namespace Jihoo.SizedMir.Linear
open BoundedMir
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def program (inputTypes : Array Ty) (fragment : Fragment) : Code :=
  ⟨inputTypes ++ fragment.locals, #[returnBlock fragment.result] ++ fragment.blocks⟩

def lowerProgram (inputTypes : Array Ty) (inputs : List Operand)
    (term : SizedErasure.Term) : Option Fragment := do
  let fragment ← compile inputs inputTypes.size 1 0 term
  let code := program inputTypes fragment
  if inputTypes[0]? = some .i64 ∧ inputsValid inputTypes.size inputs = true ∧
      code.locals.size ≤ 512 ∧ code.blocks.size ≤ 512 ∧ valid code = true then
    return fragment
  else none

theorem lowerProgram_shape (success : lowerProgram inputTypes inputs term = some fragment) :
    Compiles inputs inputTypes.size 1 0 term fragment ∧ inputTypes[0]? = some .i64 ∧
      InputsBefore inputTypes.size inputs ∧ (program inputTypes fragment).locals.size ≤ 512 ∧
      (program inputTypes fragment).blocks.size ≤ 512 ∧ valid (program inputTypes fragment) = true := by
  unfold lowerProgram at success
  cases hc : compile inputs inputTypes.size 1 0 term with
  | none => simp [hc] at success
  | some result =>
    simp [hc] at success
    obtain ⟨guard, same⟩ := success
    subst result
    exact ⟨compile_sound hc, guard.1, inputsValid_iff.mp guard.2.1,
      guard.2.2.1, guard.2.2.2.1, guard.2.2.2.2⟩

theorem lowerProgram_valid (success : lowerProgram inputTypes inputs term = some fragment) :
    valid (program inputTypes fragment) = true := (lowerProgram_shape success).2.2.2.2.2

theorem lowerProgram_bounds (success : lowerProgram inputTypes inputs term = some fragment) :
    (program inputTypes fragment).locals.size ≤ 512 ∧ (program inputTypes fragment).blocks.size ≤ 512 :=
  ⟨(lowerProgram_shape success).2.2.2.1, (lowerProgram_shape success).2.2.2.2.1⟩

theorem program_embedded : Embedded (program inputTypes fragment) inputTypes.size 1 fragment := by
  constructor
  · intro i hi
    simp [program, Array.getElem?_append_right (by omega : inputTypes.size ≤ inputTypes.size + i)]
  · intro i hi
    simp [program, Array.getElem?_append]
  · simp [program]
  · simp [program]

theorem program_return : (program inputTypes fragment).blocks[0]? = some (returnBlock fragment.result) := by
  simp [program, Array.getElem?_append]

def programFrame (fragment : Fragment) (f : Frame) : Frame :=
  { f with locals := f.locals ++ Array.replicate fragment.locals.size none }

@[simp] theorem programFrame_size :
    (programFrame fragment f).locals.size = f.locals.size + fragment.locals.size := by simp [programFrame]

theorem programFrame_prefix (bound : i < f.locals.size) :
    (programFrame fragment f).locals[i]? = f.locals[i]? := Array.getElem?_append_left bound

theorem programFrame_related (related : EnvRel env inputs f) (before : InputsBefore f.locals.size inputs) :
    EnvRel env inputs (programFrame fragment f) :=
  related.frame before (fun _ bound => (programFrame_prefix bound).symm)

/-- The generated fragment and return block construct a terminating MIR run.
Only the original input array is supplied; fresh locals are initialized here. -/
theorem program_run (success : lowerProgram inputTypes inputs term = some fragment)
    (size : inputTypes.size = f.locals.size) (related : EnvRel env inputs f)
    (heaps : HeapRel s f.heap) (initial : SizedBufferHeap.Valid s)
    (run : SizedErasure.Eval env term s (.scalar value) events t)
    (safe : SizedBufferHeap.Steps s events t) (bounded : Trace.Bounds t) :
    ∃ final, Steps (program inputTypes fragment)
      (.running (start (programFrame fragment f) (entry 1 0 term)))
      (lifecycle events) (.returned value final) ∧ HeapRel t final.heap ∧
      final.locals.size = (program inputTypes fragment).locals.size ∧
      (∀ i, i < f.locals.size → i ≠ 0 → final.locals[i]? = f.locals[i]?) := by
  obtain ⟨compiled, zero, before, _, _, _⟩ := lowerProgram_shape success
  have positive : 0 < inputTypes.size := (Array.getElem?_eq_some_iff.mp zero).1
  have inputSize : (program inputTypes fragment).locals.size = (programFrame fragment f).locals.size := by
    simp [program, size]
  have represented := programFrame_related related (by simpa [size] using before) (fragment := fragment)
  obtain ⟨middle, first, block, index, heap, result, middleSize, frame⟩ :=
    compiled.simulate program_embedded (by simp [program]; omega) inputSize before represented heaps initial run safe bounded
  have ret : (program inputTypes fragment).blocks[middle.block]? = some (returnBlock fragment.result) := by
    rw [block]; exact program_return
  have ty : (program inputTypes fragment).locals[0]? = some .i64 := by
    simpa [program, Array.getElem?_append_left positive] using zero
  have length : 0 < middle.locals.size := by rw [middleSize]; simp [programFrame]; omega
  have last := return_run ret index ty length (by simpa [toMir] using result)
  refine ⟨returnedFrame middle value, ?_, heap, ?_, ?_⟩
  · simpa using steps_trans first last
  · simpa [returnedFrame] using middleSize.trans inputSize.symm
  · intro i old nonzero
    have preserved := frame i (by omega)
    have update : (returnedFrame middle value).locals[i]? = middle.locals[i]? := by
      simp [returnedFrame, Array.set!, Array.setIfInBounds, length, Ne.symm nonzero]
    exact update.trans (preserved.trans (programFrame_prefix old))

open SizedBufferContext SizedCoreTyping LinearHeapPrograms

/-- Every scalar execution of the covered typed source graph has a generated
MIR execution. Source typing supplies the safe trace; it is not an extra premise. -/
theorem typed_source_run
    (compacted : SizedErasure.compileTarget graph fuel mask root = some term)
    (success : lowerProgram inputTypes inputs term = some fragment)
    (typed : Typing graph ctx sizes root .scalar)
    (erasedEnv : SizedErasure.EnvRel mask sourceEnv env)
    (agree : Agrees ctx owners sourceEnv) (layout : Layout s owners sizes)
    (initial : SizedBufferHeap.Valid s) (owned : Owns s.heap owners)
    (size : inputTypes.size = f.locals.size) (related : EnvRel env inputs f)
    (heaps : HeapRel s f.heap)
    (source : SizedCoreExecution.Eval graph sourceEnv root s (.scalar value) events t)
    (bounded : Trace.Bounds t) :
    ∃ final, Steps (program inputTypes fragment)
      (.running (start (programFrame fragment f) (entry 1 0 term)))
      (lifecycle events) (.returned value final) ∧ HeapRel t final.heap ∧
      final.locals.size = (program inputTypes fragment).locals.size ∧
      (∀ i, i < f.locals.size → i ≠ 0 → final.locals[i]? = f.locals[i]?) := by
  have erased := SizedErasure.compileTarget_correct compacted
  have compact : SizedErasure.Eval env term s (.scalar value) events t :=
    (erased.eval_iff erasedEnv).mp source
  exact program_run success size related heaps initial compact
    (typed.every_run_safe agree layout initial owned source).1 bounded

/-- Typing and source resource adequacy construct the terminating execution.
The adequacy premise bounds source heaps only; it assumes no target execution. -/
theorem typed_source_total
    (compacted : SizedErasure.compileTarget graph fuel mask root = some term)
    (success : lowerProgram inputTypes inputs term = some fragment)
    (typed : Typing graph ctx sizes root .scalar)
    (erasedEnv : SizedErasure.EnvRel mask sourceEnv env)
    (agree : Agrees ctx owners sourceEnv) (layout : Layout s owners sizes)
    (initial : SizedBufferHeap.Valid s) (owned : Owns s.heap owners)
    (size : inputTypes.size = f.locals.size) (related : EnvRel env inputs f)
    (heaps : HeapRel s f.heap)
    (resources : ∀ value events t, SizedCoreExecution.Eval graph sourceEnv root s value events t → Trace.Bounds t) :
    ∃ value events t final, SizedCoreExecution.Eval graph sourceEnv root s (.scalar value) events t ∧
      Steps (program inputTypes fragment)
        (.running (start (programFrame fragment f) (entry 1 0 term)))
        (lifecycle events) (.returned value final) ∧ HeapRel t final.heap ∧
      Account owners (.scalar value) events := by
  obtain ⟨value, events, t, source, safe, vt, post, account⟩ := typed.total_accounted agree layout initial owned
  cases value <;> simp only [Post] at post
  case scalar value =>
    obtain ⟨final, target, heap, _⟩ := typed_source_run compacted success typed erasedEnv agree layout initial owned
      size related heaps source (resources _ _ _ source)
    exact ⟨value, events, t, final, source, target, heap, account⟩

end Jihoo.SizedMir.Linear
