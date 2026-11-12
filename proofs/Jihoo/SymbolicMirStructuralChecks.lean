import Jihoo.SymbolicMirLoweringTotality
import Jihoo.DynamicMirCorrespondence
import Jihoo.SizedMirStructuralChecks
import Jihoo.SizedMirStructuralBudgets
import Jihoo.SymbolicCoreExamples

namespace Jihoo.SymbolicMirStructuralChecks
open SymbolicCoreContext SymbolicCoreTyping SymbolicCoreExamples
open SymbolicMirStructuralBridge SizedErasure SizedMir SizedMir.Structural

/-- The original branch/lend graph has a fixed structurally typed compact term,
for every input length and index admitted by its symbolic context. No source
execution or MIR lowering equality is supplied. -/
theorem branch_lend_total (hn : n < 2^64) (hi : i < 2^64)
    (same : operands.length = 3) :
    ∃ term bound, Typed [.scalar, .natural, .natural] term .scalar ∧
      (∀ fuel, bound ≤ fuel → compileTarget graph fuel [true, true, true] 40 = some term) ∧
      ∀ l b exit, ∃ fragment,
        Linear.compile operands [.scalar, .natural, .natural] l b exit term = some fragment ∧
        fragment.locals.size = Linear.localCost term ∧
        fragment.blocks.size = Linear.blockCost term := by
  exact typing_compiles_closed body_typed (inputs_close hn hi)
    (SizedCoreExamples.input_agrees n i 0) (by simpa [SizedCoreExamples.inputEnv, compactEnv] using same)

/-- Natural binding preserves an owned dependent result representation. -/
theorem dependent_result_total (hn : n < 2^64) (same : operands.length = 2) :
    ∃ term bound, Typed [.scalar, .natural] term .pointer ∧
      (∀ fuel, bound ≤ fuel → compileTarget dependentGraph fuel [true, true] 6 = some term) ∧
      ∀ l b exit, ∃ fragment,
        Linear.compile operands [.scalar, .natural] l b exit term = some fragment ∧
        fragment.locals.size = Linear.localCost term ∧
        fragment.blocks.size = Linear.blockCost term := by
  exact typing_compiles_closed dependent_result_typed (dependent_inputs_close hn)
    (dependent_input_agrees (value := 0)) (by simpa [compactEnv] using same)

/-- A missing dead slot needs neither a fabricated operand nor a kind. -/
theorem absent_dead_kinds : KindsSupport [.dead] [] [] := by
  intro k e kind lookup typed
  cases k with
  | zero => cases lookup; contradiction
  | succ k => simp at lookup

/-- Erasing a proof before a live natural changes its lexical rank. -/
theorem erased_proof_rank :
    KindsSupport [.bound (.literal 0) (.literal 1), .nat] [false, true] [.natural] := by
  intro k e kind lookup typed
  match k with
  | 0 => cases lookup; contradiction
  | 1 => cases lookup; cases typed; rfl
  | k+2 => simp at lookup

/-- Source typing and structural success still cannot establish a scalar ABI
for an owned result. This is intentionally not a checked-entry theorem. -/
theorem pointer_result_not_scalar : resultKind (.owner (.literal 0)) ≠ .scalar := by decide

/-- Existing source typing, not a concrete lowerProgram reduction, supplies
representation typing for the retained exporter-tested target. -/
theorem source_target_typed :
    Typed [.scalar, .natural, .natural] DynamicMirCorrespondence.target .scalar := by
  exact SymbolicMirLoweringTotality.typed_erasure body_typed
    (SymbolicCoreCompaction.MaskSupports.of_closing_agrees
      (inputs_close (n := 0) (i := 0) (by decide) (by decide))
      (SizedCoreExamples.input_agrees 0 0 0))
    (KindsSupport.of_closing_agrees
      (inputs_close (n := 0) (i := 0) (by decide) (by decide))
      (SizedCoreExamples.input_agrees 0 0 0)) DynamicMirCorrespondence.erased

def entryTypes : Array BoundedMir.Ty := #[.i64,.u64,.u64,.i64]
def entryABI : BoundedMir.Entry := ⟨#[3,2,1]⟩

theorem generic_checked_lowering :
    ∃ fragment, Entry.lowerProgram entryTypes entryABI DynamicMirCorrespondence.target = some fragment := by
  apply source_target_typed.entry_total
  · exact .cons (OperandTyped.copy rfl) (.cons (OperandTyped.copy rfl) (.cons (OperandTyped.copy rfl) .nil))
  · simp [InputsBefore, Before, Entry.operands, entryABI, entryTypes]
  · rfl
  · decide +kernel
  · decide +kernel
  · decide
  · intro slot h
    simp [entryABI] at h
    rcases h with rfl | rfl | rfl <;> simp [entryTypes, BoundedMir.argumentTypeSupported]

theorem generic_checked_admission (hn : n < BoundedMir.wordBound)
    (hi : i < BoundedMir.wordBound) (hv : v < BoundedMir.scalarBound) :
    ∃ fragment f, Entry.lowerProgram entryTypes entryABI DynamicMirCorrespondence.target = some fragment ∧
      BoundedMir.entryFrame (Entry.program entryTypes DynamicMirCorrespondence.target fragment)
        entryABI [.i64 v, .u64 i, .u64 n] = some f := by
  apply source_target_typed.entry_admission_total
  · exact .cons (OperandTyped.copy rfl) (.cons (OperandTyped.copy rfl) (.cons (OperandTyped.copy rfl) .nil))
  · simp [InputsBefore, Before, Entry.operands, entryABI, entryTypes]
  · rfl
  · decide +kernel
  · decide +kernel
  · decide
  · intro slot h
    simp [entryABI] at h
    rcases h with rfl | rfl | rfl <;> simp [entryTypes, BoundedMir.argumentTypeSupported]
  · exact .cons ⟨rfl, by simpa [BoundedMir.argumentValueValid] using hv⟩
      (.cons ⟨rfl, by simpa [BoundedMir.argumentValueValid] using hi⟩
        (.cons ⟨rfl, by simpa [BoundedMir.argumentValueValid] using hn⟩ .nil))

/-- All compact constructors, including owned lends, use the generic validity
proof rather than reducing the entire concrete lowerer. -/
theorem all_forms_generic :
    ∃ fragment, Entry.lowerProgram #[.i64] ⟨#[]⟩ Checks.allForms = some fragment := by
  apply Checks.allForms_typed.entry_total
  · exact .nil
  · simp [InputsBefore, Entry.operands]
  · rfl
  · decide +kernel
  · decide +kernel
  · decide
  · simp

#print axioms generic_checked_admission
#print axioms all_forms_generic
#print axioms generic_checked_lowering
#print axioms Typed.entry_total
#print axioms Typed.entry_admission_total
#print axioms typed_fragment_valid
#print axioms SymbolicMirLoweringTotality.typed_lowering
#print axioms SymbolicMirLoweringTotality.typed_source_total
#print axioms typing_erases_typed
#print axioms typing_compiles_closed
#print axioms compiled_statement_cost
#print axioms entry_statement_bound
#print axioms entry_signature_valid
#print axioms branch_lend_total
#print axioms dependent_result_total
end Jihoo.SymbolicMirStructuralChecks
