import Jihoo.OwnedLendExamples
import Jihoo.OwnedCoreValues

/-! Original constructor graphs with scalar/owned/scalar Lends in the same
judgment. Distinct reader results make older/newer scalar-slot mistakes visible. -/
namespace Jihoo.OwnedCoreContinuation.MixedExamples
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext

-- Scalar read (11), owned result allocation (37), scalar read of new owner (37),
-- then free the original and result, returning the older scalar (11).
def graph : Graph.Graph := #[
  .natural 1, .buffer 0, .i64, .ref 1, .var 0,
  .natural 0, .decide 5 0, .index 4 5 6, .lam false 3 7,
  .integer 37, .alloc 0 9, .lam false 3 10,
  .var 1, .var 2, .var 5,
  .free 4 14, .free 13 15,
  .lam false 1 16, .lam false 2 17, .lend 12 8 18,
  .lam false 1 19, .lam false 1 20, .lend 4 11 21,
  .lam false 1 22, .lam false 2 23, .lend 4 8 24]

def ctx : Context := [.owner 0]
def afterScalar : Context := scalarReturned ctx 0
def afterOwned : Context := ownedReturned afterScalar 0
def afterSecondScalar : Context := scalarReturned afterOwned 0

theorem valid_graph : Graph.valid graph = true := by decide

theorem scalar_shape : ScalarShape graph 25 4 7 22 :=
  .intro 8 24 3 2 23 1 rfl rfl (by decide) rfl rfl rfl (by decide)

theorem owned_shape : OwnedLendContext.Shape graph 22 4 9 19 :=
  .intro 11 21 3 10 0 1 20 1 rfl rfl (by decide) rfl rfl rfl (by decide) rfl (by decide)

theorem second_scalar_shape : ScalarShape graph 19 12 7 16 :=
  .intro 8 18 3 2 17 1 rfl rfl (by decide) rfl rfl rfl (by decide)

theorem tail_typed : Typed graph afterSecondScalar 2 2 16 := by
  apply Typed.free (slot := 1) rfl (by decide) (by decide)
  apply Typed.free (slot := 0) rfl (by decide) (by decide)
  exact .finish rfl (by decide) (by trivial)

theorem mixed_typed : Typed graph ctx 1 0 25 := by
  apply Typed.scalarLend (slot := 0) scalar_shape (by decide) (by decide)
    (.read rfl (by decide) (by decide))
  apply Typed.lend (slot := 0) owned_shape (by decide) (by decide) (.scalar rfl)
  exact Typed.scalarLend (slot := 0) second_scalar_shape (by decide) (by decide)
    (.read rfl (by decide) (by decide)) tail_typed

theorem lexical_values_remain_distinct :
    scalarBindings afterSecondScalar [37, 11] =
      [none, some 37, none, none, none, some 11, none] := rfl

theorem freeing_owners_preserves_both_scalars :
    scalarBindings (consumed 0 (consumed 1 afterSecondScalar)) [37, 11] =
      [none, some 37, none, none, none, some 11, none] := rfl

theorem original_aliases_share_identity :
    LinearCoreCallers.bindings (ownerView afterSecondScalar) [1, 0] =
      [some 1, none, some 0, some 1, some 0, none, some 0] := rfl

def initial : State := allocatedState empty 11

theorem initial_valid : Valid initial := step_valid empty_valid .alloc

theorem initial_owned : Owns initial [0] := allocate_owns empty_valid empty_owns

theorem execution_exists : ∃ v es t, Runs graph ctx 25 [0] [] initial v es t :=
  total mixed_typed rfl rfl initial_valid initial_owned

def events : List Event := [.beginLease 0 0, .read 0 11, .close 0,
  .beginLease 1 0, .alloc 1 37, .close 1,
  .beginLease 2 1, .read 2 37, .close 2, .free 0, .free 1]

def finalState : State := freedState
  (freedState (restored (OwnedLendTransfer.final (restored initial) 37)) 0) 1

theorem older_scalar_execution : Runs graph ctx 25 [0] [] initial 11 events finalState := by
  refine Runs.scalarLend (copied := 11) (reads := [.read 0 11])
    (suffix := [.beginLease 1 0, .alloc 1 37, .close 1,
      .beginLease 2 1, .read 2 37, .close 2, .free 0, .free 1])
    scalar_shape (by decide) .here ?_ ?_
  · exact .read rfl (by decide) (by decide) (by simp [opened, put])
  · refine Runs.lend (copied := 37) (reads := []) owned_shape (by decide) .here (.scalar rfl) ?_
    refine Runs.scalarLend (copied := 37) (reads := [.read 2 37]) second_scalar_shape (by decide) .here ?_ ?_
    · exact .read rfl (by decide) (by decide) (by simp [opened, put])
    · refine Runs.free rfl (by decide) (.there .here) ?_
      refine Runs.free rfl (by decide) .here ?_
      exact .finish rfl rfl

theorem every_run_safe (run : Runs graph ctx 25 [0] [] initial v es t) :
    Steps initial es t ∧ Valid t ∧ Owns t [] :=
  execution_safe mixed_typed rfl rfl initial_valid initial_owned run

theorem every_run_empty (run : Runs graph ctx 25 [0] [] initial v es t) :
    ∀ x, t.live x = false := by
  apply heap_empty mixed_typed rfl rfl initial_valid initial_owned run
  intro x live
  simpa [initial, allocatedState, empty, put] using live

theorem every_run_returns_older (run : Runs graph ctx 25 [0] [] initial v es t) :
    v = 11 ∧ es = events ∧ t = finalState :=
  Runs.deterministic run older_scalar_execution

def newest : Graph.Graph := graph.set! 15 (.free 4 12)

theorem newest_typed : Typed newest ctx 1 0 25 := by
  apply Typed.scalarLend (slot := 0)
    (.intro 8 24 3 2 23 1 rfl rfl (by decide) rfl rfl rfl (by decide))
    (by decide) (by decide) (.read rfl (by decide) (by decide))
  apply Typed.lend (slot := 0)
    (.intro 11 21 3 10 0 1 20 1 rfl rfl (by decide) rfl rfl rfl (by decide) rfl (by decide))
    (by decide) (by decide) (.scalar rfl)
  apply Typed.scalarLend (slot := 0)
    (.intro 8 18 3 2 17 1 rfl rfl (by decide) rfl rfl rfl (by decide))
    (by decide) (by decide) (.read rfl (by decide) (by decide))
  apply Typed.free (slot := 1) rfl (by decide) (by decide)
  apply Typed.free (slot := 0) rfl (by decide) (by decide)
  exact .finish rfl (by decide) (by trivial)

theorem newest_execution : Runs newest ctx 25 [0] [] initial 37 events finalState := by
  refine Runs.scalarLend (copied := 11) (reads := [.read 0 11])
    (suffix := [.beginLease 1 0, .alloc 1 37, .close 1,
      .beginLease 2 1, .read 2 37, .close 2, .free 0, .free 1])
    (.intro 8 24 3 2 23 1 rfl rfl (by decide) rfl rfl rfl (by decide))
    (by decide) .here ?_ ?_
  · exact .read rfl (by decide) (by decide) (by simp [opened, put])
  · refine Runs.lend (copied := 37) (reads := [])
      (.intro 11 21 3 10 0 1 20 1 rfl rfl (by decide) rfl rfl rfl (by decide) rfl (by decide))
      (by decide) .here (.scalar rfl) ?_
    refine Runs.scalarLend (copied := 37) (reads := [.read 2 37])
      (.intro 8 18 3 2 17 1 rfl rfl (by decide) rfl rfl rfl (by decide))
      (by decide) .here ?_ ?_
    · exact .read rfl (by decide) (by decide) (by simp [opened, put])
    · refine Runs.free rfl (by decide) (.there .here) ?_
      refine Runs.free rfl (by decide) .here ?_
      exact .finish rfl rfl

theorem every_run_returns_newest (run : Runs newest ctx 25 [0] [] initial v es t) :
    v = 37 ∧ es = events ∧ t = finalState :=
  Runs.deterministic run newest_execution

theorem initial_payloads_bounded : OwnedScalarReader.PayloadsBounded initial := by
  apply OwnedScalarReader.allocated_payloads
  · intro x live; cases live
  · decide

theorem every_run_safe_and_bounded (run : Runs graph ctx 25 [0] [] initial v es t) :
    Steps initial es t ∧ Valid t ∧ Owns t [] ∧ v < 2^63 ∧
      OwnedScalarReader.PayloadsBounded t :=
  OwnedCoreValues.execution_safe_bounded valid_graph mixed_typed rfl rfl
    initial_valid initial_owned initial_payloads_bounded (by simp [OwnedCoreValues.ValuesBounded]) run

-- The range endpoint cannot be instantiated for an oversized reader literal.
theorem oversized_reader_literal_rejected :
    Graph.valid (graph.set! 9 (.integer (2^63))) = false := by decide

-- A scalar result cannot be reinterpreted as an owner by the Free rule.
def scalarAsOwner : Graph.Graph := graph.set! 16 (.free 12 15)

theorem scalar_cannot_be_freed : ¬ Typed scalarAsOwner afterSecondScalar 2 2 16 := by
  intro h
  exact dead_owner_rejected rfl (by decide) h

-- Owner/dead lexical entries are not scalar results, even if Nat payloads agree.
theorem owner_is_not_scalar : resultAt graph afterSecondScalar 4 = none := rfl

theorem consumed_owner_is_not_scalar :
    resultAt graph (consumed 1 afterSecondScalar) 13 = none := rfl

end Jihoo.OwnedCoreContinuation.MixedExamples
