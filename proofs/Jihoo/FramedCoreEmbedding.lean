import Jihoo.FramedOwnedApplications

/-! Structural embedding of the existing common Core judgment.
Every old continuation constructor is exposed in a plan; only integer/variable
terminals use `core`. This is not the trivial opaque `.core` embedding. -/
namespace Jihoo.FramedCoreEmbedding
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext OwnedCoreContinuation
open FramedOwnedApplications

/-- A plan with no new application boundary. -/
inductive AppFree : Plan → Prop where
  | core : AppFree .core
  | free : AppFree rest → AppFree (.free rest)
  | allocate : AppFree rest → AppFree (.allocate rest)
  | lend : AppFree rest → AppFree (.lend rest)
  | scalarLend : AppFree rest → AppFree (.scalarLend rest)
  | scalarLet : AppFree rest → AppFree (.scalarLet rest)
  | ownedLet : AppFree rest → AppFree (.ownedLet rest)

def Terminal (g : Graph.Graph) (root : Nat) : Prop :=
  (∃ v, Graph.nodeAt g root = .integer v) ∨ (∃ k, Graph.nodeAt g root = .var k)

/-- Exposing a source tree does not hide a nonterminal behind `Plan.core`. -/
inductive Expanded (g : Graph.Graph) : Plan → Nat → Prop where
  | core : Terminal g root → Expanded g .core root
  | free : Graph.nodeAt g root = .free owner body → Expanded g rest body →
      Expanded g (.free rest) root
  | allocate : Allocation g root payload body → Expanded g rest body →
      Expanded g (.allocate rest) root
  | lend : OwnedLendContext.Shape g root owner init body → Expanded g rest body →
      Expanded g (.lend rest) root
  | scalarLend : ScalarShape g root owner init body → Expanded g rest body →
      Expanded g (.scalarLend rest) root
  | scalarLet : PureOwnedScalar.Shape g root arg body → Expanded g rest body →
      Expanded g (.scalarLet rest) root
  | ownedLet : OwnedArgumentBinding.Shape g root arg body → Expanded g rest body →
      Expanded g (.ownedLet rest) root

theorem Expanded.app_free (expanded : Expanded g plan root) : AppFree plan := by
  induction expanded with
  | core _ => exact .core
  | free _ _ ih => exact .free ih
  | allocate _ _ ih => exact .allocate ih
  | lend _ _ ih => exact .lend ih
  | scalarLend _ _ ih => exact .scalarLend ih
  | scalarLet _ _ ih => exact .scalarLet ih
  | ownedLet _ _ ih => exact .ownedLet ih

theorem Expanded.core_terminal (expanded : Expanded g .core root) : Terminal g root := by
  cases expanded with | core terminal => exact terminal

/-- Every old typing derivation has a genuinely exposed recursive plan. -/
theorem expand_types (typed : Types g kind ctx n m root) :
    ∃ plan, Expanded g plan root ∧ Typing g plan kind ctx n m root := by
  induction typed with
  | finish result checked bounded =>
      exact ⟨.core, .core (finish_head result), .core (.finish result checked bounded)⟩
  | returnOwner resolved =>
      exact ⟨.core, .core (Or.inr (OwnedCoreResults.return_head resolved)), .core (.returnOwner resolved)⟩
  | free shape resolved bound next ih =>
      obtain ⟨plan, exposed, typed⟩ := ih
      exact ⟨.free plan, .free shape exposed, .free shape resolved bound typed⟩
  | allocate shape bounded next ih =>
      obtain ⟨plan, exposed, typed⟩ := ih
      exact ⟨.allocate plan, .allocate shape exposed, .allocate shape bounded typed⟩
  | lend shape resolved bound reader next ih =>
      obtain ⟨plan, exposed, typed⟩ := ih
      exact ⟨.lend plan, .lend shape exposed, .lend shape resolved bound reader typed⟩
  | scalarLend shape resolved bound reader next ih =>
      obtain ⟨plan, exposed, typed⟩ := ih
      exact ⟨.scalarLend plan, .scalarLend shape exposed, .scalarLend shape resolved bound reader typed⟩
  | scalarLet shape represents next ih =>
      obtain ⟨plan, exposed, typed⟩ := ih
      exact ⟨.scalarLet plan, .scalarLet shape exposed, .scalarLet shape represents typed⟩
  | ownedLet shape resolved bound next ih =>
      obtain ⟨plan, exposed, typed⟩ := ih
      exact ⟨.ownedLet plan, .ownedLet shape exposed, .ownedLet shape resolved bound typed⟩

/-- Removing an application-free plan preserves the exact execution, including
its event order, final state and actual returned value or allocation identity. -/
theorem erase_execution (run : Evaluation g plan kind ctx root owners values s v es t)
    (plain : AppFree plan) : Exec g kind ctx root owners values s v es t := by
  induction run with
  | core run => exact run
  | apply _ _ _ _ _ => cases plain
  | free shape resolved selected next ih =>
      cases plain with | free plain => exact .free shape resolved selected (ih plain)
  | allocate shape next ih =>
      cases plain with | allocate plain => exact .allocate shape (ih plain)
  | lend shape resolved selected reads next ih =>
      cases plain with | lend plain => exact .lend shape resolved selected reads (ih plain)
  | scalarLend shape resolved selected reads next ih =>
      cases plain with | scalarLend plain => exact .scalarLend shape resolved selected reads (ih plain)
  | scalarLet shape eval next ih =>
      cases plain with | scalarLet plain => exact .scalarLet shape eval (ih plain)
  | ownedLet shape resolved selected next ih =>
      cases plain with | ownedLet plain => exact .ownedLet shape resolved selected (ih plain)

/-- Application-free plans do not accept any extra programs relative to the
old common typing relation. -/
theorem erase_typing (typed : Typing g plan kind ctx n m root)
    (plain : AppFree plan) : Types g kind ctx n m root := by
  induction typed with
  | core typed => exact typed
  | apply _ _ _ _ _ _ => cases plain
  | free shape resolved bound next ih =>
      cases plain with | free plain => exact .free shape resolved bound (ih plain)
  | allocate shape bounded next ih =>
      cases plain with | allocate plain => exact .allocate shape bounded (ih plain)
  | lend shape resolved bound reader next ih =>
      cases plain with | lend plain => exact .lend shape resolved bound reader (ih plain)
  | scalarLend shape resolved bound reader next ih =>
      cases plain with | scalarLend plain => exact .scalarLend shape resolved bound reader (ih plain)
  | scalarLet shape represents next ih =>
      cases plain with | scalarLet plain => exact .scalarLet shape represents (ih plain)
  | ownedLet shape resolved bound next ih =>
      cases plain with | ownedLet plain => exact .ownedLet shape resolved bound (ih plain)

/-- The extension is conservative on fully exposed application-free programs. -/
theorem typing_iff_expanded : Types g kind ctx n m root ↔
    ∃ plan, Expanded g plan root ∧ Typing g plan kind ctx n m root := by
  constructor
  · exact expand_types
  · rintro ⟨plan, expanded, typed⟩
    exact erase_typing typed expanded.app_free

/-- Even an untyped old execution admits a structural plan with identical
observations; this statement does not assert that such an execution is safe. -/
theorem expand_execution (run : Exec g kind ctx root owners values s v es t) :
    ∃ plan, Expanded g plan root ∧ Evaluation g plan kind ctx root owners values s v es t := by
  induction run with
  | finish result eval => exact ⟨.core, .core (finish_head result), .core (.finish result eval)⟩
  | returnOwner resolved selected =>
      exact ⟨.core, .core (Or.inr (OwnedCoreResults.return_head resolved)), .core (.returnOwner resolved selected)⟩
  | free shape resolved selected next ih =>
      obtain ⟨plan, exposed, run⟩ := ih
      exact ⟨.free plan, .free shape exposed, .free shape resolved selected run⟩
  | allocate shape next ih =>
      obtain ⟨plan, exposed, run⟩ := ih
      exact ⟨.allocate plan, .allocate shape exposed, .allocate shape run⟩
  | lend shape resolved selected reads next ih =>
      obtain ⟨plan, exposed, run⟩ := ih
      exact ⟨.lend plan, .lend shape exposed, .lend shape resolved selected reads run⟩
  | scalarLend shape resolved selected reads next ih =>
      obtain ⟨plan, exposed, run⟩ := ih
      exact ⟨.scalarLend plan, .scalarLend shape exposed, .scalarLend shape resolved selected reads run⟩
  | scalarLet shape eval next ih =>
      obtain ⟨plan, exposed, run⟩ := ih
      exact ⟨.scalarLet plan, .scalarLet shape exposed, .scalarLet shape eval run⟩
  | ownedLet shape resolved selected next ih =>
      obtain ⟨plan, exposed, run⟩ := ih
      exact ⟨.ownedLet plan, .ownedLet shape exposed, .ownedLet shape resolved selected run⟩

/-- On the ordinary valid initial runtime boundary, a fixed exposed typing plan
and the old semantics have exactly the same complete executions. -/
theorem execution_iff (typed : Typing g plan kind ctx n m root)
    (plain : AppFree plan) (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) :
    Evaluation g plan kind ctx root owners values s v es t ↔ Exec g kind ctx root owners values s v es t := by
  constructor
  · intro run; exact erase_execution run plain
  · intro run
    obtain ⟨v', es', t', evaluation⟩ := total typed length scalarLength valid owned
    obtain ⟨rfl, rfl, rfl⟩ := OwnedCoreApplications.core_deterministic (erase_execution evaluation plain) run
    exact evaluation

/-- A single plan simultaneously embeds typing and every complete execution;
the plan choice is not made after seeing a successful trace. -/
theorem expand_typed_execution (typed : Types g kind ctx n m root) :
    ∃ plan, Expanded g plan root ∧ Typing g plan kind ctx n m root ∧
      ∀ owners values s v es t, owners.length = n → values.length = m →
        Valid s → Owns s owners →
        (Evaluation g plan kind ctx root owners values s v es t ↔ Exec g kind ctx root owners values s v es t) := by
  obtain ⟨plan, expanded, newTyped⟩ := expand_types typed
  refine ⟨plan, expanded, newTyped, ?_⟩
  intro owners values s v es t length scalarLength valid owned
  exact execution_iff newTyped expanded.app_free length scalarLength valid owned

end Jihoo.FramedCoreEmbedding
