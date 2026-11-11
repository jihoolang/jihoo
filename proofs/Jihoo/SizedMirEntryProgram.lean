import Jihoo.SizedMirEntryArguments

/-! Completed programs whose real checked ABI entry starts at block zero. -/
namespace Jihoo.SizedMir.Entry
open BoundedMir Linear
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def entryBlock (term : SizedErasure.Term) : Block := ⟨#[], .goto (Linear.entry 2 1 term)⟩

def program (inputTypes : Array Ty) (term : SizedErasure.Term) (fragment : Fragment) : Code :=
  ⟨inputTypes ++ fragment.locals, #[entryBlock term, returnBlock fragment.result] ++ fragment.blocks⟩

def lowerProgram (inputTypes : Array Ty) (abi : BoundedMir.Entry)
    (term : SizedErasure.Term) : Option Fragment := do
  let inputs := operands abi.argumentSlots.toList
  let kinds ← inputKinds inputTypes inputs
  let fragment ← compile inputs kinds inputTypes.size 2 1 term
  let code := program inputTypes term fragment
  if inputTypes[0]? = some .i64 ∧ inputsValid inputTypes.size inputs = true ∧
      code.locals.size ≤ 512 ∧ code.blocks.size ≤ 512 ∧ valid code = true ∧ entryValid code abi = true then
    return fragment
  else none

theorem lowerProgram_shape (success : lowerProgram inputTypes abi term = some fragment) :
    Compiles (operands abi.argumentSlots.toList)
      ((inputKinds inputTypes (operands abi.argumentSlots.toList)).getD []) inputTypes.size 2 1 term fragment ∧
    inputTypes[0]? = some .i64 ∧ InputsBefore inputTypes.size (operands abi.argumentSlots.toList) ∧
    (program inputTypes term fragment).locals.size ≤ 512 ∧
    (program inputTypes term fragment).blocks.size ≤ 512 ∧
    valid (program inputTypes term fragment) = true ∧ entryValid (program inputTypes term fragment) abi = true := by
  unfold lowerProgram at success
  cases hk : inputKinds inputTypes (operands abi.argumentSlots.toList) with
  | none => simp [hk] at success
  | some kinds =>
    simp only [hk, Option.bind_some] at success
    cases hc : compile (operands abi.argumentSlots.toList) kinds inputTypes.size 2 1 term with
    | none => simp [hc] at success
    | some result =>
      simp [hc] at success
      obtain ⟨guard, same⟩ := success
      subst result
      simpa [hk] using And.intro (compile_sound hc)
        ⟨guard.1, inputsValid_iff.mp guard.2.1, guard.2.2⟩

theorem lowerProgram_valid (success : lowerProgram inputTypes abi term = some fragment) :
    valid (program inputTypes term fragment) = true := (lowerProgram_shape success).2.2.2.2.2.1

theorem lowerProgram_bounds (success : lowerProgram inputTypes abi term = some fragment) :
    (program inputTypes term fragment).locals.size ≤ 512 ∧
      (program inputTypes term fragment).blocks.size ≤ 512 :=
  ⟨(lowerProgram_shape success).2.2.2.1, (lowerProgram_shape success).2.2.2.2.1⟩

theorem lowerProgram_entryValid (success : lowerProgram inputTypes abi term = some fragment) :
    entryValid (program inputTypes term fragment) abi = true :=
  (lowerProgram_shape success).2.2.2.2.2.2

theorem program_embedded : Embedded (program inputTypes term fragment) inputTypes.size 2 fragment := by
  constructor
  · intro i hi
    simp [program, Array.getElem?_append_right (by omega : inputTypes.size ≤ inputTypes.size + i)]
  · intro i hi
    simp [program, Array.getElem?_append]
    omega
  · simp [program]
  · simp [program]

theorem program_return : (program inputTypes term fragment).blocks[1]? = some (returnBlock fragment.result) := by
  simp [program, Array.getElem?_append]

theorem program_entry : (program inputTypes term fragment).blocks[0]? = some (entryBlock term) := by
  simp [program, Array.getElem?_append]

theorem inputKinds_prefix (before : InputsBefore types.size inputs) :
    inputKinds (types ++ extra) inputs = inputKinds types inputs := by
  induction inputs with
  | nil => rfl
  | cons op rest ih =>
    have head := before op (by simp)
    have tail : InputsBefore types.size rest := fun x hx => before x (by simp [hx])
    have same : operandType ⟨types ++ extra, #[]⟩ op = operandType ⟨types, #[]⟩ op := by
      cases op with
      | constant v => cases v <;> rfl
      | copy p => simp [operandType, head.1, Array.getElem?_append_left head.2]
    simpa only [inputKinds, List.mapM_cons, same] using congrArg
      (fun xs : Option (List Kind) => (do
        let k ← (do let ty ← operandType ⟨types, #[]⟩ op; toKind ty)
        let ks ← xs
        pure (k :: ks))) (ih tail)


/-- The admitted frame itself executes the wrapper, compiled fragment and return.
No reset, scratch extension, or target-execution premise is needed. -/
theorem program_run
    (success : lowerProgram inputTypes abi term = some fragment)
    (admission : entryFrame (program inputTypes term fragment) abi (env.map toMir) = some f)
    (run : SizedErasure.Eval env term SizedBufferHeap.empty (.scalar value) events t)
    (safe : SizedBufferHeap.Steps SizedBufferHeap.empty events t) (bounded : Trace.Bounds t) :
    ∃ final, Steps (program inputTypes term fragment) (.running f)
      (lifecycle events) (.returned value final) ∧ HeapRel t final.heap ∧
      final.locals.size = (program inputTypes term fragment).locals.size ∧
      (∀ i, i < inputTypes.size → i ≠ 0 → final.locals[i]? = f.locals[i]?) ∧ value < scalarBound := by
  obtain ⟨compiled, zero, before, _, _, _, _⟩ := lowerProgram_shape success
  obtain ⟨related, fullKinds, widths⟩ := checked_arguments admission
  have kinds : InputKindsAgree inputTypes (operands abi.argumentSlots.toList) env := by
    simpa only [InputKindsAgree, program, inputKinds_prefix before] using fullKinds
  have envKinds : EnvKinds env ((inputKinds inputTypes (operands abi.argumentSlots.toList)).getD []) := by
    rw [kinds]; rfl
  obtain ⟨control, index, empty⟩ := entryFrame_control admission
  have size := entryFrame_size admission
  have positive : 0 < inputTypes.size := (Array.getElem?_eq_some_iff.mp zero).1
  have heaps : HeapRel SizedBufferHeap.empty f.heap := by rw [empty]; exact HeapRel.empty
  obtain ⟨middle, first, block, midIndex, heap, result, middleSize, frame⟩ :=
    compiled.simulate program_embedded (by simp [program]; omega) size.symm before related envKinds heaps
      SizedBufferHeap.empty_valid run safe bounded
  have target : Linear.entry 2 1 term < (program inputTypes term fragment).blocks.size := by
    have costs := compiled.sizes
    simp only [program, Array.size_append, Array.size_push, Array.size_empty]
    change Linear.entry 2 1 term < 2 + fragment.blocks.size
    unfold Linear.entry
    split <;> omega
  have enter : Step (program inputTypes term fragment) (.running f) []
      (.running (start f (Linear.entry 2 1 term))) := by
    apply Step.goto
    · simp [fetch, control, index, program_entry, entryBlock]
    · exact target
  have ret : (program inputTypes term fragment).blocks[middle.block]? = some (returnBlock fragment.result) := by
    rw [block]; exact program_return
  have ty : (program inputTypes term fragment).locals[0]? = some .i64 := by
    simpa [program, Array.getElem?_append_left positive] using zero
  have length : 0 < middle.locals.size := by rw [middleSize, size]; simp [program]; omega
  have last := return_run ret midIndex ty length (by simpa [toMir] using result)
  refine ⟨returnedFrame middle value, ?_, heap, ?_, ?_, ?_⟩
  · simpa using Steps.cons enter (steps_trans first last)
  · simpa [returnedFrame] using middleSize.trans size
  · intro i old nonzero
    have update : (returnedFrame middle value).locals[i]? = middle.locals[i]? := by
      simp [returnedFrame, Array.set!, Array.setIfInBounds, length, Ne.symm nonzero]
    exact update.trans (frame i old)
  · exact compiled.value_bounded widths SizedBufferHeap.empty_valid run safe bounded.payloads

open SizedBufferContext SizedCoreTyping LinearHeapPrograms

/-- A source execution is compiled from automatic environment compaction and
actual ABI admission. Typing supplies the safe lifecycle trace. -/
theorem typed_source_run
    (compacted : SizedErasure.compileTarget graph fuel (SizedErasure.compactEnv sourceEnv).1 root = some term)
    (success : lowerProgram inputTypes abi term = some fragment)
    (typed : Typing graph ctx sizes root .scalar)
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
  have erased := SizedErasure.compileTarget_correct compacted
  have compact : SizedErasure.Eval (SizedErasure.compactEnv sourceEnv).2 term
      SizedBufferHeap.empty (.scalar value) events t :=
    (erased.eval_iff (SizedErasure.compactEnv_related sourceEnv)).mp source
  exact program_run success admission compact
    (typed.every_run_safe agree layout SizedBufferHeap.empty_valid owned source).1 bounded

/-- Source-only resource adequacy constructs both source and checked-entry MIR
termination, including a bounded scalar return and the exact final heap relation. -/
theorem typed_source_total
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
      Steps (program inputTypes term fragment) (.running f) (lifecycle events) (.returned value final) ∧
      HeapRel t final.heap ∧ Account owners (.scalar value) events ∧ value < scalarBound ∧
      final.locals.size = (program inputTypes term fragment).locals.size ∧
      (∀ i, i < inputTypes.size → i ≠ 0 → final.locals[i]? = f.locals[i]?) := by
  obtain ⟨value, events, t, source, safe, vt, post, account⟩ :=
    typed.total_accounted agree layout SizedBufferHeap.empty_valid owned
  cases value <;> simp only [Post] at post
  case scalar value =>
    obtain ⟨final, target, heap, size, preserved, bound⟩ :=
      typed_source_run compacted success typed agree layout owned admission source (resources _ _ _ source)
    exact ⟨value, events, t, final, source, target, heap, account, bound, size, preserved⟩

end Jihoo.SizedMir.Entry
