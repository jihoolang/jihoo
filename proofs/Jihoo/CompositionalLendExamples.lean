import Jihoo.OwnedLendExamples

namespace Jihoo.OwnedLendTyping.CompositionalExamples
open HeapLeases ScopedLend LinearHeapPrograms LinearCoreCallers
open OwnedLendContext

/-- After the first result is allocated, lend the non-newest original again.
The nested continuation owns three identities and has three aliases for the
original; consume both results and the original exactly once. -/
def graph : ScopedLend.Graph.Graph := Examples.graph ++ #[
  .var 3, .var 4, .free 21 12, .free 20 22, .free 10 23,
  .lam false 1 24, .lam false 1 25, .lend 4 9 26,
  .lam false 1 27, .lam false 1 28, .lend 4 9 29,
  .lam false 1 30]

theorem nested_shape : Shape graph 27 4 7 24 :=
  .intro 9 26 3 8 0 1 25 1 rfl rfl (by decide) rfl rfl rfl (by decide) rfl (by decide)

theorem nested_tail_typed :
    OwnedCoreContinuation.Typed graph (returnedContext context 1) 3 24 := by
  apply OwnedCoreContinuation.Typed.free (slot := 0) rfl (by decide) (by decide)
  apply OwnedCoreContinuation.Typed.free (slot := 0) rfl (by decide) (by decide)
  apply OwnedCoreContinuation.Typed.free (slot := 0) rfl (by decide) (by decide)
  exact .finish rfl (by decide)

/-- Only the original's aliases are reader-authorized; the first result stays
owned but cannot be borrowed through this reader's active token. -/
theorem nonselected_result_not_reader :
    (readerRoles context 1)[2]? = some .ghost := rfl

theorem selected_aliases_are_readable :
    (readerRoles context 1)[1]? = some .owner ∧
      (readerRoles context 1)[3]? = some .owner := ⟨rfl, rfl⟩

theorem nested_context_identity :
    bindings (returnedContext context 1) [2, 1, 0] =
      [some 0, some 2, some 0, some 1, some 0] := rfl

theorem clearing_original_does_not_clear_results :
    consumed 2 (returnedContext context 1) = [none, some 0, none, some 1, none] := rfl

theorem nested_continuation_typed : OwnedCoreContinuation.Typed graph context 2 27 :=
  .lend nested_shape (by decide) (by decide)
    (.read rfl (by decide) (by decide)) nested_tail_typed

def typed : Typed graph 31 19 :=
  ⟨7, 27, .read 0, by decide, by decide,
    .read rfl (by decide) (by decide), nested_continuation_typed⟩

theorem nested_execution_exists :
    ∃ value es t, Runs graph 31 19 Examples.initial 0 value es t :=
  total typed Examples.initial_valid (Examples.initial_owned.live 0 (by simp))
    (Examples.initial_owned.leaseFree 0 (by simp))

theorem every_nested_run_empty
    (run : Runs graph 31 19 Examples.initial 0 value es t) : ∀ x, t.live x = false := by
  apply heap_empty typed Examples.initial_valid (Examples.initial_owned.live 0 (by simp))
    (Examples.initial_owned.leaseFree 0 (by simp)) run
  intro y live
  simpa [Examples.initial, allocatedState, empty, put] using live

def freshResult : ScopedLend.Graph.Graph := graph.set! 27 (.lend 10 9 26)

theorem fresh_result_tail_typed :
    OwnedCoreContinuation.Typed freshResult (returnedContext context 0) 3 24 := by
  apply OwnedCoreContinuation.Typed.free (slot := 0) rfl (by decide) (by decide)
  apply OwnedCoreContinuation.Typed.free (slot := 0) rfl (by decide) (by decide)
  apply OwnedCoreContinuation.Typed.free (slot := 0) rfl (by decide) (by decide)
  exact .finish rfl (by decide)

theorem fresh_result_continuation_typed : OwnedCoreContinuation.Typed freshResult context 2 27 :=
  .lend (.intro 9 26 3 8 0 1 25 1 rfl rfl (by decide) rfl rfl rfl (by decide) rfl (by decide))
    (by decide) (by decide) (.read rfl (by decide) (by decide)) fresh_result_tail_typed

def freshTyped : Typed freshResult 31 19 :=
  ⟨7, 27, .read 0, by decide, by decide,
    .read rfl (by decide) (by decide), fresh_result_continuation_typed⟩

theorem fresh_result_execution_exists :
    ∃ value es t, Runs freshResult 31 19 Examples.initial 0 value es t :=
  total freshTyped Examples.initial_valid (Examples.initial_owned.live 0 (by simp))
    (Examples.initial_owned.leaseFree 0 (by simp))

def unrelatedBorrow : ScopedLend.Graph.Graph := graph ++ #[.borrow 11, .index 32 5 6]

theorem unrelated_borrow_operand_rejected :
    ScopedLend.Graph.borrowOperand unrelatedBorrow (readerRoles context 1) 32 = false := by decide

/-- An initializer cannot redirect the active lease to a different live owner. -/
theorem unrelated_reader_rejected :
    ¬ ScopedLend.Graph.Represents unrelatedBorrow (readerRoles context 1) 33 r := by
  intro h
  cases h with
  | scalar shape => cases shape
  | read shape allowed bound =>
      change ScopedLend.Graph.Node.index 32 5 6 = .index _ _ _ at shape
      cases shape
      rw [unrelated_borrow_operand_rejected] at allowed
      contradiction
  | strict shape _ _ => cases shape
  | app shape _ _ _ _ => cases shape
  | branch _ shape _ _ _ _ _ => cases shape

end Jihoo.OwnedLendTyping.CompositionalExamples
