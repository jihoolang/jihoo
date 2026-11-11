import Jihoo.SizedMirStructuralTotality
import Jihoo.SizedMirEntryProgram

/-! Exact statement costs and static entry-signature checks. These discharge
individual gates, not whole-program MIR validity. -/
namespace Jihoo.SizedMir.Structural
open BoundedMir Linear

def statementCost : SizedErasure.Term → Nat
  | .allocate _ _ => 11
  | .app a b => statementCost a + statementCost b
  | .free _ b => statementCost b
  | .lend _ _ b => 2 + statementCost b
  | .ownedLend _ _ _ b => 13 + statementCost b
  | .ifLt _ _ y n => 3 + statementCost y + statementCost n
  | _ => 0

def statements (blocks : Array Block) : Nat :=
  (blocks.toList.map (fun b => b.statements.size)).sum

@[simp] theorem statements_append : statements (a ++ b) = statements a + statements b := by
  simp [statements]

theorem compiled_statement_cost (compiled : Compiles inputs ks l b exit term fragment) :
    statements fragment.blocks = statementCost term := by
  induction compiled <;>
    simp_all [statementCost, statements, pureFragment, allocationFragment, appendFragment,
      freeFragment, freeBlock, lendFragment, readFragment, readBlock, ownedLendFragment,
      branchFragment, Branch.decisionBlock, Branch.joinBlock, Allocation.fragmentBlocks,
      Allocation.inputBlock, MirBuffer.entryBlock, MirBuffer.guardBlock,
      MirBuffer.initBlock, MirBuffer.testBlock, MirBuffer.bodyBlock, Nat.add_assoc] <;> omega

/-- Local budgets already imply the statement budget with substantial slack. -/
theorem statementCost_le_twice_locals (term : SizedErasure.Term) :
    statementCost term ≤ 2 * localCost term := by
  induction term <;> simp_all [statementCost, localCost] <;> omega

theorem entry_statement_bound (compiled : Compiles inputs ks l b exit term fragment)
    (locals : inputTypes.size + localCost term ≤ 512) :
    statements (Entry.program inputTypes term fragment).blocks ≤ 4096 := by
  have cost := compiled_statement_cost compiled
  have bound := statementCost_le_twice_locals term
  simp only [Entry.program, statements_append]
  have wrapper : statements #[Entry.entryBlock term, returnBlock fragment.result] = 1 := rfl
  rw [wrapper, cost]
  omega

/-- Distinct nonzero scalar argument slots remain ABI-valid after scratch locals
are appended. Pointer arguments are explicitly excluded by this hypothesis. -/
theorem entry_signature_valid (distinct : abi.argumentSlots.toList.Nodup)
    (slots : ∀ slot ∈ abi.argumentSlots.toList, slot ≠ 0 ∧
      ∃ ty, inputTypes[slot]? = some ty ∧ argumentTypeSupported ty = true) :
    entryValid (Entry.program inputTypes term fragment) abi = true := by
  simp only [entryValid, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨distinct, ?_⟩
  rw [Array.all_eq_true]
  intro i hi
  obtain ⟨nonzero, ty, lookup, supported⟩ := slots abi.argumentSlots[i] (by simp)
  have bound := (Array.getElem?_eq_some_iff.mp lookup).1
  simp [Entry.program, Array.getElem?_append_left bound, lookup, supported, nonzero]

end Jihoo.SizedMir.Structural
