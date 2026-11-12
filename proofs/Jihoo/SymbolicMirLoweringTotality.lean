import Jihoo.SymbolicMirStructuralBridge
import Jihoo.SizedMirStructuralValidity
import Jihoo.SymbolicMirEntry

/-! End-to-end structural lowering from the existing symbolic judgment.
Machine resource and ABI conditions are explicit; no successful lowerer call
or generated-code validity is a premise. -/
namespace Jihoo.SymbolicMirLoweringTotality
open BoundedMir SymbolicCoreContext SymbolicCoreTyping SizedErasure SizedMir
open SizedMir.Structural SymbolicMirStructuralBridge

/-- A fixed compact term and compactor fuel bound are constructed from source
symbolic typing. Scalar ABI and finite code-size conditions then imply checked
MIR lowering. Both conditional arms are covered, independently of execution. -/
theorem typed_lowering (typed : Typing g ctx sizes root .scalar)
    (closing : Closes ctx closed) (agrees : SizedBufferContext.Agrees closed owners env)
    (inputTypesOK : InputsTyped ⟨types, #[]⟩ (Entry.operands abi.argumentSlots.toList)
      ((compactEnv env).2.map kindOf))
    (before : InputsBefore types.size (Entry.operands abi.argumentSlots.toList))
    (zero : types[0]? = some .i64)
    (distinct : abi.argumentSlots.toList.Nodup)
    (slots : ∀ slot ∈ abi.argumentSlots.toList, slot ≠ 0 ∧
      ∃ ty, types[slot]? = some ty ∧ argumentTypeSupported ty = true) :
    ∃ term bound,
      (∀ fuel, bound ≤ fuel → compileTarget g fuel (compactEnv env).1 root = some term) ∧
      (types.size + Linear.localCost term ≤ 512 → 2 + Linear.blockCost term ≤ 512 →
        ∃ fragment, Entry.lowerProgram types abi term = some fragment ∧
          valid (Entry.program types term fragment) = true ∧
          entryValid (Entry.program types term fragment) abi = true) := by
  obtain ⟨term, erased, represented⟩ := typing_erases_typed typed
    (SymbolicCoreCompaction.MaskSupports.of_closing_agrees closing agrees)
    (KindsSupport.of_closing_agrees closing agrees)
  obtain ⟨bound, complete⟩ := erased.compileTarget_complete
  refine ⟨term, bound, complete, ?_⟩
  intro locals blocks
  obtain ⟨fragment, lowered⟩ := represented.entry_total inputTypesOK before zero locals blocks distinct slots
  exact ⟨fragment, lowered, Entry.lowerProgram_valid lowered, Entry.lowerProgram_entryValid lowered⟩

/-- Two structural erasures of the same graph/mask coincide because the
existing deterministic compactor is complete for each. -/
theorem erasure_unique (a : Erases g mask root ta) (b : Erases g mask root tb) : ta = tb := by
  obtain ⟨na, ha⟩ := a.compileTarget_complete
  obtain ⟨nb, hb⟩ := b.compileTarget_complete
  exact Option.some.inj ((ha (max na nb) (Nat.le_max_left _ _)).symm.trans
    (hb (max na nb) (Nat.le_max_right _ _)))

theorem typed_erasure (typed : Typing g ctx sizes root kind)
    (maskOK : SymbolicCoreCompaction.MaskSupports ctx mask)
    (kinds : KindsSupport ctx mask ks) (erased : Erases g mask root term) :
    Typed ks term (resultKind kind) := by
  obtain ⟨other, ho, ht⟩ := typing_erases_typed typed maskOK kinds
  exact erasure_unique ho erased ▸ ht

/-- Source execution and generated execution are constructed with computed
compaction, checked lowering and actual checked argument binding. The code-size
bound is solely on erased syntax; runtime heap-resource bounds remain explicit. -/
theorem typed_source_total
    (typed : Typing g ctx sizes root .scalar)
    (closing : Closes ctx closed)
    (inventory : SizesEval (SizedBufferContext.naturalEnv closed) sizes concreteSizes)
    (agrees : SizedBufferContext.Agrees closed owners env)
    (layout : SizedBufferContext.Layout SizedBufferHeap.empty owners concreteSizes)
    (owned : LinearHeapPrograms.Owns SizedBufferHeap.empty.heap owners)
    (inputTypesOK : InputsTyped ⟨types, #[]⟩ (Entry.operands abi.argumentSlots.toList)
      ((compactEnv env).2.map kindOf))
    (before : InputsBefore types.size (Entry.operands abi.argumentSlots.toList))
    (zero : types[0]? = some .i64)
    (distinct : abi.argumentSlots.toList.Nodup)
    (slots : ∀ slot ∈ abi.argumentSlots.toList, slot ≠ 0 ∧
      ∃ ty, types[slot]? = some ty ∧ argumentTypeSupported ty = true)
    (args : ArgumentsRel (fun slot value => types[slot]? = some (valueType value) ∧
      argumentValueValid value = true) abi.argumentSlots.toList ((compactEnv env).2.map toMir))
    (storage : ∀ term, Erases g (compactEnv env).1 root term →
      types.size + Linear.localCost term ≤ 512 ∧ 2 + Linear.blockCost term ≤ 512)
    (resources : ∀ value events t,
      SizedCoreExecution.Eval g env root SizedBufferHeap.empty value events t → Trace.Bounds t) :
    ∃ term fuel fragment f value events t final,
      compileTarget g fuel (compactEnv env).1 root = some term ∧
      Entry.lowerProgram types abi term = some fragment ∧
      entryFrame (Entry.program types term fragment) abi ((compactEnv env).2.map toMir) = some f ∧
      SizedCoreExecution.Eval g env root SizedBufferHeap.empty (.scalar value) events t ∧
      Steps (Entry.program types term fragment) (.running f) (lifecycle events) (.returned value final) ∧
      HeapRel t final.heap ∧ SizedCoreTyping.Account owners (.scalar value) events ∧
      value < scalarBound ∧ final.locals.size = (Entry.program types term fragment).locals.size ∧
      (∀ i, i < types.size → i ≠ 0 → final.locals[i]? = f.locals[i]?) := by
  obtain ⟨term, erased, represented⟩ := typing_erases_typed typed
    (SymbolicCoreCompaction.MaskSupports.of_closing_agrees closing agrees)
    (KindsSupport.of_closing_agrees closing agrees)
  obtain ⟨bound, complete⟩ := erased.compileTarget_complete
  have compacted := complete bound (Nat.le_refl bound)
  obtain ⟨localBound, blockBound⟩ := storage term erased
  obtain ⟨fragment, f, lowered, admitted⟩ := represented.entry_admission_total
    inputTypesOK before zero localBound blockBound distinct slots args
  obtain ⟨value, events, t, final, result⟩ := SymbolicMirEntry.typed_source_total
    compacted lowered typed closing inventory agrees layout owned admitted resources
  exact ⟨term, bound, fragment, f, value, events, t, final, compacted, lowered, admitted, result⟩

end Jihoo.SymbolicMirLoweringTotality
