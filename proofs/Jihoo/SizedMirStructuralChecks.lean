import Jihoo.SizedMirStructuralTotality
import Jihoo.SizedMirEntryProgram
namespace Jihoo.SizedMir.Structural.Checks
open BoundedMir Linear

def allForms : SizedErasure.Term :=
  .app (.allocate (.literal 1) (.literal 7))
    (.lend 0 (.literal 0)
      (.ownedLend 0 (.literal 1) (.literal 0)
        (.ifLt (.literal 0) (.literal 1)
          (.free 0 (.free 1 (.scalar 7)))
          (.free 1 (.free 0 (.scalar 9))))))
theorem allForms_typed : Typed [] allForms .scalar := by
  apply Typed.app
  · exact .allocate (.literal (by decide)) (.literal (by decide))
  · apply Typed.lend (by rfl) (.literal (by decide))
    apply Typed.ownedLend (by rfl) (.literal (by decide)) (.literal (by decide))
    apply Typed.ifLt (.literal (by decide)) (.literal (by decide))
    · exact .free (by rfl) (.free (by rfl) (.scalar (by decide)))
    · exact .free (by rfl) (.free (by rfl) (.scalar (by decide)))
theorem allForms_total : ∃ f, compile [] [] 1 2 1 allForms = some f :=
  allForms_typed.total rfl 1 2 1
theorem allForms_entry : (Entry.lowerProgram #[.i64] ⟨#[]⟩ allForms).isSome = true := by
  decide +kernel

def badUnselected : SizedErasure.Term :=
  .ifLt (.literal 0) (.literal 1) (.scalar 7) (.scalar scalarBound)
theorem selected_runs : SizedErasure.Eval [] badUnselected SizedBufferHeap.empty
    (.scalar 7) [] SizedBufferHeap.empty :=
  .yes .literal .literal (by decide) .scalar
theorem unselected_rejected : compile [] [] 1 2 1 badUnselected = none := by decide +kernel
theorem natural_return_rejected : Entry.lowerProgram #[.i64] ⟨#[]⟩ (.natural 0) = none := by
  decide +kernel
theorem wrong_operand_compiles :
    (compile [.constant (.i64 0)] [.pointer] 1 2 1 (.free 0 (.scalar 0))).isSome = true := by
  decide +kernel
theorem wrong_operand_invalid :
    valid (Entry.program #[.i64] (.free 0 (.scalar 0))
      (freeFragment 1 (.constant (.i64 0)) 1 (pureFragment (.constant (.i64 0))))) = false := by
  decide +kernel
theorem natural_let_typed : NatTyped [.natural]
    (.letE (.var 0) (.var 0)) :=
  .letE (.var rfl) (.var rfl)

theorem natural_branch_typed : Typed [.natural]
    (.ifLt (.var 0) (.literal 1) (.natural 2) (.var 0)) .natural :=
  .ifLt (.var rfl) (.literal (by decide)) (.natural (by decide)) (.var rfl)

theorem pointer_branch_typed : Typed [.pointer]
    (.ifLt (.literal 0) (.literal 1) (.var 0) (.allocate (.literal 1) (.literal 0))) .pointer :=
  .ifLt (.literal (by decide)) (.literal (by decide)) (.var rfl)
    (.allocate (.literal (by decide)) (.literal (by decide)))

theorem mismatched_branches_rejected :
    compile [] [] 1 2 1 (.ifLt (.literal 0) (.literal 1) (.scalar 0) (.natural 0)) = none := by
  decide +kernel

theorem missing_slot_untypable : ¬ Typed [] (.var 0) kind := by
  intro h
  cases h with
  | var lookup => simp at lookup

#print axioms Typed.total
#print axioms Typed.total_cost
#print axioms allForms_entry
#print axioms unselected_rejected
#print axioms wrong_operand_invalid
end Jihoo.SizedMir.Structural.Checks
