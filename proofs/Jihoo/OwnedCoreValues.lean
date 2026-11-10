import Jihoo.OwnedCoreContinuation
import Jihoo.OwnedScalarReader

/-! Result-range and ownership safety for the same mixed direct Core judgment.
The scalar model covers nonnegative I64 values only. Initial live payloads and
scalar bindings must be bounded; this is not full signed I64 or whole-Core typing. -/
namespace Jihoo.OwnedCoreValues
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext OwnedScalarReader OwnedCoreContinuation

def ValuesBounded (values : List Nat) : Prop := ∀ v ∈ values, v < 2^63

theorem result_bounded (literal : OwnedScalarContext.LiteralBound result)
    (bounded : ValuesBounded values) (evaluated : result.eval values = some v) : v < 2^63 := by
  cases result with
  | literal value =>
      simp only [ScalarCoreCallers.Result.eval, Option.some.injEq] at evaluated
      subst v
      exact literal
  | scalar slot =>
      exact bounded v (List.mem_of_getElem? evaluated)

theorem freed_payloads (bounded : PayloadsBounded s) : PayloadsBounded (freedState s x) := by
  intro y live
  by_cases eq : y = x
  · simp [freedState, put, eq] at live
  · apply bounded y
    simpa [freedState, put, eq] using live

theorem execution_bounded (graphValid : Graph.valid g = true)
    (typed : Typed g ctx n m root) (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) (payloads : PayloadsBounded s)
    (scalarBounds : ValuesBounded values) (run : Runs g ctx root owners values s v es t) :
    v < 2^63 ∧ PayloadsBounded t := by
  induction typed generalizing owners values s v es t with
  | finish shape checked bound =>
      cases run with
      | finish shape' evaluated =>
          have eq := shape.symm.trans shape'; cases eq
          exact ⟨result_bounded bound scalarBounds evaluated, payloads⟩
      | free other _ _ _ => exact False.elim (finish_not_free shape other)
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; exact False.elim (finish_not_app shape other)
      | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; exact False.elim (finish_not_lend shape other)
      | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; exact False.elim (finish_not_lend shape other)
  | free shape resolved bound typed ih =>
      cases run with
      | finish other _ => exact False.elim (finish_not_free other shape)
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; have := shape.symm.trans other; contradiction
      | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
      | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
      | free other resolved' selected restRun =>
          have eq := shape.symm.trans other; cases eq
          have eq := resolved.symm.trans resolved'; cases eq
          have step := Step.free (owned.live _ selected.member) (owned.leaseFree _ selected.member)
          exact ih (by have := selected.length; omega) scalarLength
            (step_valid valid step) (free_owns owned selected) (freed_payloads payloads)
            scalarBounds restRun
  | allocate a bound typed ih =>
      cases run with
      | finish other _ => obtain ⟨f, x, shape⟩ := a.application; exact False.elim (finish_not_app other shape)
      | free other _ _ _ => obtain ⟨f, x, shape⟩ := a.application; have := shape.symm.trans other; contradiction
      | lend b _ _ _ _ =>
          obtain ⟨f, x, shape⟩ := a.application
          obtain ⟨r, k, other⟩ := b.head
          have := shape.symm.trans other; contradiction
      | scalarLend b _ _ _ _ =>
          obtain ⟨f, x, shape⟩ := a.application
          obtain ⟨r, k, other⟩ := b.head
          have := shape.symm.trans other; contradiction
      | allocate a' restRun =>
          obtain ⟨rfl, rfl⟩ := a.unique a'
          exact ih (by simp [length]) scalarLength
            (step_valid valid (Step.alloc (value := _))) (allocate_owns valid owned)
            (allocated_payloads payloads bound) scalarBounds restRun

  | lend shape resolved bound reading typed ih =>
      cases run with
      | finish other _ => obtain ⟨f, x, h⟩ := shape.head; exact False.elim (finish_not_lend other h)
      | free other _ _ _ => obtain ⟨f, x, h⟩ := shape.head; have := h.symm.trans other; contradiction
      | allocate a _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.application
          have := h.symm.trans other; contradiction
      | scalarLend shape' _ _ _ _ => exact False.elim (shape'.not_owned shape)
      | lend shape' resolved' selected read suffix =>
          obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          have reader := reading.reflect read
          have pre := OwnedLendTransfer.prefix_steps valid (owned.live _ selected.member) reader
          have copiedBound := reads_bounded
            (step_valid valid (Step.beginLease (owned.live _ selected.member)))
            (opened_payloads payloads) (represented_bounded graphValid reading) reader
          exact ih (by simp [length]) scalarLength (steps_valid valid pre)
            (OwnedLendTransfer.transfer_owns valid owned)
            (allocated_payloads (restored_payloads payloads) copiedBound) scalarBounds suffix

  | scalarLend shape resolved bound reading typed ih =>
      cases run with
      | finish other _ => obtain ⟨f, x, h⟩ := shape.head; exact False.elim (finish_not_lend other h)
      | free other _ _ _ => obtain ⟨f, x, h⟩ := shape.head; have := h.symm.trans other; contradiction
      | allocate a _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.application
          have := h.symm.trans other; contradiction
      | lend shape' _ _ _ _ => exact False.elim (shape.not_owned shape')
      | scalarLend shape' resolved' selected read suffix =>
          obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          have reader := reading.reflect read
          have pre := scalar_steps valid (owned.live _ selected.member) reader
          have copiedBound := reads_bounded
            (step_valid valid (Step.beginLease (owned.live _ selected.member)))
            (opened_payloads payloads) (represented_bounded graphValid reading) reader
          exact ih length (by simp [scalarLength]) (steps_valid valid pre)
            (restored_owns owned) (restored_payloads payloads)
            (by simpa [ValuesBounded] using And.intro copiedBound scalarBounds) suffix

/-- One theorem applies ownership and scalar safety to every operational run
of the same judgment. No second reader or result certificate is required. -/
theorem execution_safe_bounded (graphValid : Graph.valid g = true)
    (typed : Typed g ctx n m root) (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) (payloads : PayloadsBounded s)
    (scalarBounds : ValuesBounded values) (run : Runs g ctx root owners values s v es t) :
    Steps s es t ∧ Valid t ∧ Owns t [] ∧ v < 2^63 ∧ PayloadsBounded t := by
  obtain ⟨steps, finalValid, finalOwned⟩ := execution_safe typed length scalarLength valid owned run
  obtain ⟨resultBound, finalPayloads⟩ := execution_bounded graphValid typed length scalarLength
    valid owned payloads scalarBounds run
  exact ⟨steps, finalValid, finalOwned, resultBound, finalPayloads⟩

theorem total_safe_bounded (graphValid : Graph.valid g = true)
    (typed : Typed g ctx n m root) (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) (payloads : PayloadsBounded s)
    (scalarBounds : ValuesBounded values) :
    ∃ v es t, Runs g ctx root owners values s v es t ∧ Steps s es t ∧
      Valid t ∧ Owns t [] ∧ v < 2^63 ∧ PayloadsBounded t := by
  obtain ⟨v, es, t, run⟩ := total typed length scalarLength valid owned
  exact ⟨v, es, t, run,
    execution_safe_bounded graphValid typed length scalarLength valid owned payloads scalarBounds run⟩

end Jihoo.OwnedCoreValues
