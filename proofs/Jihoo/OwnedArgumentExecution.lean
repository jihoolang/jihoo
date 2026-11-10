import Jihoo.OwnedCoreContinuation

/-! Actual owned application execution connects the lexical argument, selected
allocation identity, transferred parameter and unchanged runtime capability list.
This is immediate application in the specified fragment, not general dependent
substitution or an implementation-refinement theorem. -/
namespace Jihoo.OwnedArgumentExecution
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext OwnedCoreContinuation
open OwnedArgumentBinding

structure Transfer (g : Graph.Graph) (ctx : Context) (n m argument body : Nat)
    (owners values : List Nat) (s : State) (v : Nat) (es : List Event) (t : State) where
  lexical : Nat
  slot : Nat
  object : Nat
  remaining : List Nat
  argument_variable : Graph.nodeAt g argument = .var lexical
  argument_lookup : ctx[lexical]? = some (.owner slot)
  selected : Select owners slot object remaining
  slot_bound : slot < n
  original_identity : (LinearCoreCallers.bindings (ownerView ctx) owners)[lexical]? = some (some object)
  parameter_identity :
    (LinearCoreCallers.bindings (ownerView (transferred ctx slot)) owners)[0]? = some (some object)
  aliases_dead : ∀ k, ctx[k]? = some (.owner slot) → (transferred ctx slot)[k + 1]? = some .dead
  body_typed : Typed g (transferred ctx slot) n m body
  body_run : Runs g (transferred ctx slot) body owners values s v es t

/-- No producer-supplied object identity or callee trace: both are obtained from
this application execution and aligned with its declarative typing derivation. -/
theorem transfer (typed : Typed g ctx n m root) (shape : OwnedArgumentBinding.Shape g root argument body)
    (argumentShape : Graph.nodeAt g argument = .var lexical)
    (run : Runs g ctx root owners values s v es t) :
    Nonempty (Transfer g ctx n m argument body owners values s v es t) := by
  obtain ⟨slot, resolved, bound, bodyTyped⟩ := typed.ownedVar_inversion shape argumentShape
  obtain ⟨object, remaining, selected, bodyRun⟩ := run.ownedLet_inversion shape resolved
  obtain ⟨k, variableShape, lookup⟩ := ownerSlot_variable resolved
  have original : (LinearCoreCallers.bindings (ownerView ctx) owners)[k]? = some (some object) := by
    simp [LinearCoreCallers.bindings, ownerView, ScalarCoreCallers.ownerView,
      List.getElem?_map, lookup, LinearCoreCallers.Select.lookup_selected selected]
  have parameter : (LinearCoreCallers.bindings (ownerView (transferred ctx slot)) owners)[0]? =
      some (some object) := by rw [transferred_bindings selected]; rfl
  exact ⟨⟨k, slot, object, remaining, variableShape, lookup, selected, bound,
    original, parameter, fun _ h => older_alias_dead h, bodyTyped, bodyRun⟩⟩

/-- The exact selected object is released once by the actual body execution,
while unchanged owners/values/state establish this is transfer, not allocation. -/
theorem safe_transfer (typed : Typed g ctx n m root) (shape : OwnedArgumentBinding.Shape g root argument body)
    (argumentShape : Graph.nodeAt g argument = .var lexical)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) (run : Runs g ctx root owners values s v es t) :
    ∃ witness : Transfer g ctx n m argument body owners values s v es t,
      Steps s es t ∧ Valid t ∧ Owns t [] ∧
      (released es).count witness.object = 1 ∧ t.live witness.object = false := by
  obtain ⟨w⟩ := transfer typed shape argumentShape run
  obtain ⟨steps, finalValid, finalOwned⟩ := execution_safe w.body_typed length scalarLength valid owned w.body_run
  obtain ⟨count, dead⟩ := no_tracked_leaks w.body_typed length scalarLength valid owned w.body_run
    (Or.inl w.selected.member)
  exact ⟨w, steps, finalValid, finalOwned, count, dead⟩

theorem Transfer.ready (w : Transfer g ctx n m argument body owners values s v es t)
    (ready : PureOwnedScalar.Ready ctx values) : PureOwnedScalar.Ready (transferred ctx w.slot) values :=
  ready_preserved ready

theorem Transfer.scalar_closing (w : Transfer g ctx n m argument body owners values s v es t)
    (raw : CoreBridge.Raw) :
    (raw.rename Nat.succ).subst (PureOwnedScalar.closing (transferred ctx w.slot) values) =
      raw.subst (PureOwnedScalar.closing ctx values) := closing_shift raw

end Jihoo.OwnedArgumentExecution
