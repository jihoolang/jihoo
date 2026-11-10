import Jihoo.CoreLexicalSimulation
import Jihoo.ComposedCoreExamples
import Jihoo.FramedCoreEmbedding

/-! The same complete native-exported graph now has a plan-free execution.
These statements reuse its exact node IDs, captured lexical structure and event
identities. The exporter association remains tested, not formally refined. -/
namespace Jihoo.CoreLexicalExamples
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext OwnedCoreContinuation
open CoreLexicalContext CoreLexicalExecution CoreLexicalSimulation

theorem program_run : Eval ComposedCoreExamples.graph [] ComposedCoreExamples.root empty (.scalar 99) ComposedCoreExamples.events ComposedCoreExamples.finalState :=
  framed_simulation ComposedCoreExamples.program_run materialize_agrees

theorem every_run_same (run : Eval ComposedCoreExamples.graph [] ComposedCoreExamples.root empty value events t) :
    value = .scalar 99 ∧ events = ComposedCoreExamples.events ∧ t = ComposedCoreExamples.finalState :=
  run.deterministic program_run

theorem every_run_safe (run : Eval ComposedCoreExamples.graph [] ComposedCoreExamples.root empty value events t) :
    Steps empty events t ∧ Valid t ∧ Owns t [] := by
  obtain ⟨_, rfl, rfl⟩ := every_run_same run
  exact ComposedCoreExamples.every_run_safe ComposedCoreExamples.program_run

theorem every_run_no_live_heap (run : Eval ComposedCoreExamples.graph [] ComposedCoreExamples.root empty value events t) :
    ∀ x, t.live x = false := by
  obtain ⟨_, _, rfl⟩ := every_run_same run
  exact ComposedCoreExamples.every_run_no_live_heap ComposedCoreExamples.program_run

theorem every_run_exact_identity_trace (run : Eval ComposedCoreExamples.graph [] ComposedCoreExamples.root empty value events t) :
    allocations events = [0,1] ∧ released events = [0,1] := by
  rw [(every_run_same run).2.1]
  exact ⟨ComposedCoreExamples.exactly_two_allocations, ComposedCoreExamples.exactly_two_releases⟩

theorem every_run_lease_expired (run : Eval ComposedCoreExamples.graph [] ComposedCoreExamples.root empty value events t) :
    ∀ token, t.lease token = none := by
  obtain ⟨_, _, rfl⟩ := every_run_same run
  exact ComposedCoreExamples.no_borrow_after_completion

theorem owned_reader_run :
    Eval ComposedCoreExamples.ownedGraph [] 19 empty (.scalar 99) ComposedCoreExamples.ownedEvents ComposedCoreExamples.ownedFinal :=
  framed_simulation ComposedCoreExamples.owned_program_run materialize_agrees

theorem owned_reader_every_run_same (run : Eval ComposedCoreExamples.ownedGraph [] 19 empty value events t) :
    value = .scalar 99 ∧ events = ComposedCoreExamples.ownedEvents ∧ t = ComposedCoreExamples.ownedFinal :=
  run.deterministic owned_reader_run

theorem owned_reader_every_run_safe (run : Eval ComposedCoreExamples.ownedGraph [] 19 empty value events t) :
    Steps empty events t ∧ Valid t ∧ Owns t [] := by
  obtain ⟨_, rfl, rfl⟩ := owned_reader_every_run_same run
  exact ComposedCoreExamples.owned_all_runs_safe ComposedCoreExamples.owned_program_run

/-- A consumed slot can still physically hold an old owner identity. -/
theorem stale_capture_agrees (identity : Nat) :
    Agrees [.dead] [] [] [.owner identity] := by
  constructor <;> intro i k x lookup value <;> simp at value

/-- One old continuation can be hidden by core or exposed structurally. -/
def overlapGraph : Graph.Graph := #[.integer 7, .var 0, .free 1 0]
def overlapContext : Context := [.owner 0]
def overlapState : State := allocatedState empty 7

theorem overlap_old_typed : Types overlapGraph .scalar overlapContext 1 0 2 := by
  exact .free (slot := 0) rfl (by decide) (by decide)
    (.finish (result := .literal 7) (by decide) (by decide) (by change 7 < 2^63; decide))

theorem overlap_expanded_typed : FramedOwnedApplications.Typing overlapGraph
    (.free .core) .scalar overlapContext 1 0 2 := by
  exact .free (slot := 0) rfl (by decide) (by decide)
    (.core (.finish (result := .literal 7) (by decide) (by decide) (by change 7 < 2^63; decide)))

theorem overlap_old_run : Exec overlapGraph .scalar overlapContext 2 [0] []
    overlapState 7 [.free 0] (freedState overlapState 0) := by
  exact .free rfl (by decide) .here (.finish (result := .literal 7) (by decide) (by decide))

theorem overlap_expanded_run : FramedOwnedApplications.Evaluation overlapGraph
    (.free .core) .scalar overlapContext 2 [0] [] overlapState 7 [.free 0]
    (freedState overlapState 0) := by
  exact .free rfl (by decide) .here (.core (.finish (result := .literal 7) (by decide) (by decide)))

theorem overlap_distinct_plans :
    FramedOwnedApplications.Plan.core ≠ .free .core := by decide

theorem overlap_coherent
    (run : FramedOwnedApplications.Evaluation overlapGraph .core .scalar
      overlapContext 2 [0] [] overlapState v events t) :
    v = 7 ∧ events = [.free 0] ∧ t = freedState overlapState 0 :=
  cross_plan_coherence run overlap_expanded_run

end Jihoo.CoreLexicalExamples
