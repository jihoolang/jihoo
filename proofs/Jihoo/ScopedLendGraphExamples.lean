import Jihoo.ScopedLendGraph
import Jihoo.ScopedLendExamples

namespace Jihoo.ScopedLend.Graph.Examples
open HeapLeases

/-- Original node positions of a one-owner scalar-read Lend function. -/
def graph : Graph := #[
  .natural 1, .buffer 0, .i64, .pi false 1 2, .var 0, .ref 1,
  .natural 0, .decide 6 0, .index 4 6 7, .lam false 5 8,
  .var 1, .free 4 10, .lam false 1 11, .lam false 2 12,
  .lend 4 9 13, .lam false 1 14]

def accepted : Accepted graph 15 3 :=
  (admit graph 15 3).get (by decide)

theorem correct_reader : accepted.reader = .read 0 := rfl

theorem original_constructor_execution :
    CoreRuns graph 15 3 ScopedLend.Examples.initial 1 42
      [.beginLease 1 1, .read 1 42, .close 1, .free 1]
      (finalState ScopedLend.Examples.initial 1 42 .free) :=
  .lend (readRoot := 8) (rest := 11) (k := .free) rfl rfl
    (.read (a := 4) (i := 6) (p := 7) rfl rfl rfl rfl)

theorem all_runs_safe (run : CoreRuns graph 15 3 ScopedLend.Examples.initial 1 v events t) :
    Steps ScopedLend.Examples.initial events t ∧ Valid t ∧
      (released events).count 1 = 1 ∧ t.live 1 = false :=
  accepted_all_runs accepted ScopedLend.Examples.initial_valid (by decide)
    ScopedLend.Examples.owner_available run

theorem constructs_execution :
    ∃ v events t, CoreRuns graph 15 3 ScopedLend.Examples.initial 1 v events t ∧
      Steps ScopedLend.Examples.initial events t ∧ Valid t ∧
      (released events).count 1 = 1 ∧ t.live 1 = false :=
  accepted_execution accepted ScopedLend.Examples.initial_valid (by decide)
    ScopedLend.Examples.owner_available

theorem erased_reader_rejected : (admit (graph.set! 9 (.lam true 5 8)) 15 3).isSome = false := by decide

theorem wrong_borrow_domain_rejected :
    (admit (graph.set! 9 (.lam false 2 8)) 15 3).isSome = false := by decide

theorem wrong_owner_slot_rejected :
    (admit (graph.set! 4 (.var 1)) 15 3).isSome = false := by decide

theorem false_index_evidence_rejected :
    (admit (graph.set! 7 (.decide 6 6)) 15 3).isSome = false := by decide

theorem return_owner_as_scalar_rejected :
    (admit (graph.set! 11 (.free 4 4)) 15 3).isSome = false := by decide

theorem cyclic_child_rejected :
    (admit (graph.set! 8 (.index 8 6 7)) 15 3).isSome = false := by decide

theorem requested_type_rejected : (admit graph 15 2).isSome = false := by decide

theorem role_shift_reader :
    borrowOperand #[.var 2] [.ghost, .scalar, .borrow, .owner] 0 = true := by decide

theorem role_shift_owner :
    borrowOperand #[.var 3, .borrow 0] [.ghost, .scalar, .borrow, .owner] 1 = true := by decide

theorem ghost_is_not_reader :
    borrowOperand #[.var 0] [.ghost, .borrow, .owner] 0 = false := by decide

theorem scalar_is_not_owner :
    borrowOperand #[.var 0, .borrow 0] [.scalar, .borrow, .owner] 1 = false := by decide

end Jihoo.ScopedLend.Graph.Examples
