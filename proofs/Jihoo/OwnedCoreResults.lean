import Jihoo.OwnedCoreContinuation

/-! Owned results of the same result-indexed Core constructor judgment.
The terminal owner is returned alive, not freed; all other tracked resources
are consumed. Sequential handoff uses a fresh singleton consumer context.
This does not add general owned-producing App syntax, dependent Buffer lengths,
active-reader nesting, an implementation refinement, or payload range claims. -/

namespace Jihoo.OwnedCoreContinuation
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext

@[elab_as_elim] theorem OwnedTyped.induct
    {motive : ∀ ctx n m root, OwnedTyped g ctx n m root → Prop}
    (returnOwner : ∀ {ctx m root} (a : ownerSlot g ctx root = some 0), motive ctx 1 m root (.returnOwner a))
    (free : ∀ {ctx n m root owner body slot} (a : Graph.nodeAt g root = .free owner body) (b : ownerSlot g ctx owner = some slot) (c : slot < n) (d : OwnedTyped g (consumed slot ctx) (n-1) m body), motive (consumed slot ctx) (n-1) m body d → motive ctx n m root (.free a b c d))
    (allocate : ∀ {ctx n m root value body} (a : Allocation g root value body) (b : value < 2^63) (c : OwnedTyped g (fresh ctx) (n+1) m body), motive (fresh ctx) (n+1) m body c → motive ctx n m root (.allocate a b c))
    (lend : ∀ {ctx n m root owner init body slot reader} (a : Shape g root owner init body) (b : ownerSlot g ctx owner = some slot) (c : slot < n) (d : Graph.Represents g (readerRoles ctx slot) init reader) (e : OwnedTyped g (ownedReturned ctx slot) (n+1) m body), motive (ownedReturned ctx slot) (n+1) m body e → motive ctx n m root (.lend a b c d e))
    (scalarLend : ∀ {ctx n m root owner init body slot reader} (a : ScalarShape g root owner init body) (b : ownerSlot g ctx owner = some slot) (c : slot < n) (d : Graph.Represents g (readerRoles ctx slot) init reader) (e : OwnedTyped g (scalarReturned ctx slot) n (m+1) body), motive (scalarReturned ctx slot) n (m+1) body e → motive ctx n m root (.scalarLend a b c d e))
    (scalarLet : ∀ {ctx n m root arg body raw} (a : PureOwnedScalar.Shape g root arg body) (b : PureOwnedScalar.Represents g ctx m arg raw) (c : OwnedTyped g (PureOwnedScalar.bindScalar ctx) n (m+1) body), motive (PureOwnedScalar.bindScalar ctx) n (m+1) body c → motive ctx n m root (.scalarLet a b c))
    (ownedLet : ∀ {ctx n m root argument body slot} (a : OwnedArgumentBinding.Shape g root argument body) (b : ownerSlot g ctx argument = some slot) (c : slot < n) (d : OwnedTyped g (OwnedArgumentBinding.transferred ctx slot) n m body), motive (OwnedArgumentBinding.transferred ctx slot) n m body d → motive ctx n m root (.ownedLet a b c d))
    (h : OwnedTyped g ctx n m root) : motive ctx n m root h := by
  have go : ∀ k ctx n m root (h : Types g k ctx n m root) (eq : k = .owned), motive ctx n m root (Eq.mp (congrArg (fun k => Types g k ctx n m root) eq) h) := by
    intro k ctx n m root h
    induction h with
    | finish _ _ _ => intro eq; cases eq
    | returnOwner a => intro eq; cases eq; exact returnOwner a
    | free a b c d ih => intro eq; cases eq; exact free a b c d (ih rfl)
    | allocate a b c ih => intro eq; cases eq; exact allocate a b c (ih rfl)
    | lend a b c d e ih => intro eq; cases eq; exact lend a b c d e (ih rfl)
    | scalarLend a b c d e ih => intro eq; cases eq; exact scalarLend a b c d e (ih rfl)
    | scalarLet a b c ih => intro eq; cases eq; exact scalarLet a b c (ih rfl)
    | ownedLet a b c d ih => intro eq; cases eq; exact ownedLet a b c d (ih rfl)
  exact go _ _ _ _ _ h rfl

@[elab_as_elim] theorem OwnedRuns.induct
    {motive : ∀ ctx root owners values s value events t, OwnedRuns g ctx root owners values s value events t → Prop}
    (returnOwner : ∀ {ctx root owners values s slot x rest} (a : ownerSlot g ctx root = some slot) (b : Select owners slot x rest), motive ctx root owners values s x [] s (.returnOwner a b))
    (free : ∀ {ctx root owners values s value events t owner body slot x rest} (a : Graph.nodeAt g root = .free owner body) (b : ownerSlot g ctx owner = some slot) (c : Select owners slot x rest) (d : OwnedRuns g (consumed slot ctx) body rest values (freedState s x) value events t), motive (consumed slot ctx) body rest values (freedState s x) value events t d → motive ctx root owners values s value (.free x::events) t (.free a b c d))
    (allocate : ∀ {ctx root owners values s value events t payload body} (a : Allocation g root payload body) (b : OwnedRuns g (fresh ctx) body (s.nextObject::owners) values (allocatedState s payload) value events t), motive (fresh ctx) body (s.nextObject::owners) values (allocatedState s payload) value events t b → motive ctx root owners values s value (.alloc s.nextObject payload::events) t (.allocate a b))
    (lend : ∀ {ctx root owners values s value suffix t owner init body slot x rest copied reads} (a : Shape g root owner init body) (b : ownerSlot g ctx owner = some slot) (c : Select owners slot x rest) (d : Graph.CoreReads g (opened s x) s.nextLease x (readerRoles ctx slot) init copied reads) (e : OwnedRuns g (ownedReturned ctx slot) body (s.nextObject::owners) values (OwnedLendTransfer.final s copied) value suffix t), motive (ownedReturned ctx slot) body (s.nextObject::owners) values (OwnedLendTransfer.final s copied) value suffix t e → motive ctx root owners values s value (OwnedLendTransfer.events s x copied reads ++ suffix) t (.lend a b c d e))
    (scalarLend : ∀ {ctx root owners values s value suffix t owner init body slot x rest copied reads} (a : ScalarShape g root owner init body) (b : ownerSlot g ctx owner = some slot) (c : Select owners slot x rest) (d : Graph.CoreReads g (opened s x) s.nextLease x (readerRoles ctx slot) init copied reads) (e : OwnedRuns g (scalarReturned ctx slot) body owners (copied::values) (restored s) value suffix t), motive (scalarReturned ctx slot) body owners (copied::values) (restored s) value suffix t e → motive ctx root owners values s value (scalarEvents s x reads ++ suffix) t (.scalarLend a b c d e))
    (scalarLet : ∀ {ctx root owners values s value events t arg body computed} (a : PureOwnedScalar.Shape g root arg body) (b : PureOwnedScalar.Eval g ctx arg values computed) (c : OwnedRuns g (PureOwnedScalar.bindScalar ctx) body owners (computed::values) s value events t), motive (PureOwnedScalar.bindScalar ctx) body owners (computed::values) s value events t c → motive ctx root owners values s value events t (.scalarLet a b c))
    (ownedLet : ∀ {ctx root owners values s value events t argument body slot x rest} (a : OwnedArgumentBinding.Shape g root argument body) (b : ownerSlot g ctx argument = some slot) (c : Select owners slot x rest) (d : OwnedRuns g (OwnedArgumentBinding.transferred ctx slot) body owners values s value events t), motive (OwnedArgumentBinding.transferred ctx slot) body owners values s value events t d → motive ctx root owners values s value events t (.ownedLet a b c d))
    (h : OwnedRuns g ctx root owners values s value events t) : motive ctx root owners values s value events t h := by
  have go : ∀ k ctx root owners values s value events t (h : Exec g k ctx root owners values s value events t) (eq : k = .owned), motive ctx root owners values s value events t (Eq.mp (congrArg (fun k => Exec g k ctx root owners values s value events t) eq) h) := by
    intro k ctx root owners values s value events t h
    induction h with
    | finish _ _ => intro eq; cases eq
    | returnOwner a b => intro eq; cases eq; exact returnOwner a b
    | free a b c d ih => intro eq; cases eq; exact free a b c d (ih rfl)
    | allocate a b ih => intro eq; cases eq; exact allocate a b (ih rfl)
    | lend a b c d e ih => intro eq; cases eq; exact lend a b c d e (ih rfl)
    | scalarLend a b c d e ih => intro eq; cases eq; exact scalarLend a b c d e (ih rfl)
    | scalarLet a b c ih => intro eq; cases eq; exact scalarLet a b c (ih rfl)
    | ownedLet a b c d ih => intro eq; cases eq; exact ownedLet a b c d (ih rfl)
  exact go _ _ _ _ _ _ _ _ _ h rfl

end Jihoo.OwnedCoreContinuation

namespace Jihoo.OwnedCoreResults
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext OwnedCoreContinuation

theorem total (typed : OwnedTyped g ctx n m root) (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) :
    ∃ value events t, OwnedRuns g ctx root owners values s value events t := by
  induction typed using OwnedTyped.induct generalizing owners values s with
  | returnOwner resolved =>
      have bound : 0 < owners.length := by omega
      obtain ⟨x, rest, selected⟩ := select_total bound
      exact ⟨x, [], s, .returnOwner resolved selected⟩
  | free shape resolved bound typed ih =>
      have bound' := bound
      rw [← length] at bound'
      obtain ⟨x, rest, selected⟩ := select_total bound'
      have step : Step s (.free x) (freedState s x) :=
        .free (owned.live x selected.member) (owned.leaseFree x selected.member)
      obtain ⟨v, es, t, run⟩ := ih (by have := selected.length; omega) scalarLength
        (step_valid valid step) (free_owns owned selected)
      exact ⟨v, _, t, .free shape resolved selected run⟩
  | allocate shape bound typed ih =>
      obtain ⟨v, es, t, run⟩ := ih (by simp [length]) scalarLength
        (step_valid valid (Step.alloc (value := _))) (allocate_owns valid owned)
      exact ⟨v, _, t, .allocate shape run⟩
  | lend shape resolved bound reading typed ih =>
      have bound' := bound
      rw [← length] at bound'
      obtain ⟨x, rest, selected⟩ := select_total bound'
      have active : (opened s x).lease s.nextLease = some x := by simp [opened, put]
      have env : EnvValid (opened s x) [s.nextLease] := by
        intro l member
        have : l = s.nextLease := List.mem_singleton.mp member
        subst l
        exact ⟨x, active⟩
      obtain ⟨copied, reads, run⟩ := reader_total (env := [s.nextLease]) reading.scoped env
      obtain ⟨v, es, t, suffix⟩ := ih (by simp [length]) scalarLength
        (OwnedLendTransfer.prefix_valid valid (owned.live _ selected.member) run)
        (OwnedLendTransfer.transfer_owns valid owned)
      exact ⟨v, _, t, .lend shape resolved selected (reading.execution active run) suffix⟩
  | scalarLend shape resolved bound reading typed ih =>
      have bound' := bound
      rw [← length] at bound'
      obtain ⟨x, rest, selected⟩ := select_total bound'
      have active : (opened s x).lease s.nextLease = some x := by simp [opened, put]
      have env : EnvValid (opened s x) [s.nextLease] := by
        intro l member
        have : l = s.nextLease := List.mem_singleton.mp member
        subst l
        exact ⟨x, active⟩
      obtain ⟨copied, reads, run⟩ := reader_total (env := [s.nextLease]) reading.scoped env
      obtain ⟨v, es, t, suffix⟩ := ih (values := copied :: values) length (by simp [scalarLength])
        (steps_valid valid (scalar_steps valid (owned.live _ selected.member) run))
        (restored_owns owned)
      exact ⟨v, _, t, .scalarLend shape resolved selected (reading.execution active run) suffix⟩

  | scalarLet shape represented typed ih =>
      obtain ⟨computed, evaluated⟩ := PureOwnedScalar.total represented scalarLength
      obtain ⟨v, es, t, run⟩ := ih (values := computed :: values) length (by simp [scalarLength]) valid owned
      exact ⟨v, es, t, .scalarLet shape evaluated run⟩

  | ownedLet shape resolved bound typed ih =>
      have bound' := bound
      rw [← length] at bound'
      obtain ⟨x, rest, selected⟩ := select_total bound'
      obtain ⟨v, es, t, run⟩ := ih length scalarLength valid owned
      exact ⟨v, es, t, .ownedLet shape resolved selected run⟩

theorem return_head (h : ownerSlot g ctx root = some slot) : ∃ k, Graph.nodeAt g root = .var k := by
  obtain ⟨k, hk, _⟩ := OwnedArgumentBinding.ownerSlot_variable h
  exact ⟨k, hk⟩

theorem return_not_free (h : ownerSlot g ctx root = some slot)
    (shape : Graph.nodeAt g root = .free owner body) : False := by
  obtain ⟨k, hk⟩ := return_head h; have := hk.symm.trans shape; contradiction
theorem return_not_app (h : ownerSlot g ctx root = some slot)
    (shape : Graph.nodeAt g root = .app f a) : False := by
  obtain ⟨k, hk⟩ := return_head h; have := hk.symm.trans shape; contradiction
theorem return_not_lend (h : ownerSlot g ctx root = some slot)
    (shape : Graph.nodeAt g root = .lend o r c) : False := by
  obtain ⟨k, hk⟩ := return_head h; have := hk.symm.trans shape; contradiction

theorem execution_safe (typed : OwnedTyped g ctx n m root) (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) (run : OwnedRuns g ctx root owners values s v es t) :
    Steps s es t ∧ Valid t ∧ Owns t [v] := by
  induction typed using OwnedTyped.induct generalizing owners values s v es t with
  | returnOwner resolved =>
      cases run with
      | returnOwner resolved' selected =>
          have eq := resolved.symm.trans resolved'; cases eq
          cases selected with
          | here =>
              rename_i rest
              have empty : rest = [] := List.length_eq_zero_iff.mp (by simpa using length)
              subst rest
              exact ⟨.nil, valid, owned⟩
      | free other _ _ _ => exact False.elim (return_not_free resolved other)
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; exact False.elim (return_not_app resolved other)
      | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; exact False.elim (return_not_lend resolved other)
      | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; exact False.elim (return_not_lend resolved other)
      | scalarLet p _ _ => obtain ⟨f, h⟩ := p.head; exact False.elim (return_not_app resolved h)
      | ownedLet p _ _ _ => obtain ⟨f, h⟩ := p.head; exact False.elim (return_not_app resolved h)

  | free shape resolved bound typed ih =>
      cases run with
      | returnOwner other _ => exact False.elim (return_not_free other shape)
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; have := shape.symm.trans other; contradiction
      | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
      | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
      | free other resolved' selected restRun =>
          have eq := shape.symm.trans other; cases eq
          have eq := resolved.symm.trans resolved'; cases eq
          have step := Step.free (owned.live _ selected.member) (owned.leaseFree _ selected.member)
          obtain ⟨steps, vt, ot⟩ := ih (by have := selected.length; omega) scalarLength
            (step_valid valid step) (free_owns owned selected) restRun
          exact ⟨.cons step steps, vt, ot⟩
      | scalarLet p _ _ => obtain ⟨f, h⟩ := p.head; have := shape.symm.trans h; contradiction
      | ownedLet p _ _ _ => obtain ⟨f, h⟩ := p.head; have := shape.symm.trans h; contradiction

  | allocate a bound typed ih =>
      cases run with
      | returnOwner other _ => obtain ⟨f, x, shape⟩ := a.application; exact False.elim (return_not_app other shape)
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
          obtain ⟨steps, vt, ot⟩ := ih (by simp [length]) scalarLength
            (step_valid valid (Step.alloc (value := _))) (allocate_owns valid owned) restRun
          exact ⟨.cons .alloc steps, vt, ot⟩
      | scalarLet p _ _ => exact False.elim (a.not_pure p)
      | ownedLet p resolved _ _ => exact False.elim (a.not_owned_binding p resolved)

  | lend shape resolved bound reading typed ih =>
      cases run with
      | returnOwner other _ => obtain ⟨f, x, h⟩ := shape.head; exact False.elim (return_not_lend other h)
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
          obtain ⟨steps, vt, ot⟩ := ih (by simp [length]) scalarLength (steps_valid valid pre)
            (OwnedLendTransfer.transfer_owns valid owned) suffix
          exact ⟨steps_append pre steps, vt, ot⟩
      | scalarLet p _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction
      | ownedLet p _ _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction

  | scalarLend shape resolved bound reading typed ih =>
      cases run with
      | returnOwner other _ => obtain ⟨f, x, h⟩ := shape.head; exact False.elim (return_not_lend other h)
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
          obtain ⟨steps, vt, ot⟩ := ih length (by simp [scalarLength]) (steps_valid valid pre)
            (restored_owns owned) suffix
          exact ⟨steps_append pre steps, vt, ot⟩
      | scalarLet p _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction
      | ownedLet p _ _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction

  | scalarLet shape represented typed ih =>
      cases run with
      | returnOwner h _ => obtain ⟨f, other⟩ := shape.head; exact False.elim (return_not_app h other)
      | free h _ _ _ => obtain ⟨f, other⟩ := shape.head; have := other.symm.trans h; contradiction
      | allocate a _ => exact False.elim (a.not_pure shape)
      | lend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLet shape' evaluated suffix =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          exact ih length (by simp [scalarLength]) valid owned suffix
      | ownedLet p _ _ _ => exact False.elim (p.not_pure shape)

  | ownedLet shape resolved bound typed ih =>
      cases run with
      | returnOwner h _ => obtain ⟨f, other⟩ := shape.head; exact False.elim (return_not_app h other)
      | free h _ _ _ => obtain ⟨f, other⟩ := shape.head; have := other.symm.trans h; contradiction
      | allocate a _ => exact False.elim (a.not_owned_binding shape resolved)
      | lend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLet p _ _ => exact False.elim (shape.not_pure p)
      | ownedLet shape' resolved' selected suffix =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          exact ih length scalarLength valid owned suffix

theorem release_conservation (typed : OwnedTyped g ctx n m root) (length : owners.length = n) (scalarLength : values.length = m)
    (run : OwnedRuns g ctx root owners values s v es t) (x : Nat) :
    (released es).count x + [v].count x = owners.count x + (allocations es).count x := by
  induction typed using OwnedTyped.induct generalizing owners values s v es t with
  | returnOwner resolved =>
      cases run with
      | returnOwner resolved' selected =>
          have eq := resolved.symm.trans resolved'; cases eq
          cases selected with
          | here =>
              rename_i rest
              have empty : rest = [] := List.length_eq_zero_iff.mp (by simpa using length)
              subst rest
              simp [released, allocations]
      | free other _ _ _ => exact False.elim (return_not_free resolved other)
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; exact False.elim (return_not_app resolved other)
      | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; exact False.elim (return_not_lend resolved other)
      | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; exact False.elim (return_not_lend resolved other)
      | scalarLet p _ _ => obtain ⟨f, h⟩ := p.head; exact False.elim (return_not_app resolved h)
      | ownedLet p _ _ _ => obtain ⟨f, h⟩ := p.head; exact False.elim (return_not_app resolved h)

  | free shape resolved bound typed ih =>
      cases run with
      | returnOwner other _ => exact False.elim (return_not_free other shape)
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; have := shape.symm.trans other; contradiction
      | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
      | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
      | free other resolved' selected restRun =>
          have eq := shape.symm.trans other; cases eq
          have eq := resolved.symm.trans resolved'; cases eq
          have h := selected.count x
          have hr := ih (by have := selected.length; omega) scalarLength restRun
          simp only [released, allocations, List.filterMap_cons, List.count_cons] at *
          simp only [beq_iff_eq] at *
          omega
      | scalarLet p _ _ => obtain ⟨f, h⟩ := p.head; have := shape.symm.trans h; contradiction
      | ownedLet p _ _ _ => obtain ⟨f, h⟩ := p.head; have := shape.symm.trans h; contradiction

  | allocate a bound typed ih =>
      cases run with
      | returnOwner other _ => obtain ⟨f, x, shape⟩ := a.application; exact False.elim (return_not_app other shape)
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
          have hr := ih (by simp [length]) scalarLength restRun
          simp only [released, allocations, List.filterMap_cons, List.count_cons] at *
          omega
      | scalarLet p _ _ => exact False.elim (a.not_pure p)
      | ownedLet p resolved _ _ => exact False.elim (a.not_owned_binding p resolved)

  | lend shape resolved bound reading typed ih =>
      cases run with
      | returnOwner other _ => obtain ⟨f, x, h⟩ := shape.head; exact False.elim (return_not_lend other h)
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
          have hr := ih (by simp [length]) scalarLength suffix
          have ha := reader_allocations reader
          have hf := reader_releases reader
          simp only [released, allocations] at ha hf
          simp [OwnedLendTransfer.events, released, allocations, List.filterMap_append,
            ha, hf, List.count_cons] at *
          omega
      | scalarLet p _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction
      | ownedLet p _ _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction

  | scalarLend shape resolved bound reading typed ih =>
      cases run with
      | returnOwner other _ => obtain ⟨f, x, h⟩ := shape.head; exact False.elim (return_not_lend other h)
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
          have hr := ih length (by simp [scalarLength]) suffix
          have ha := reader_allocations reader
          have hf := reader_releases reader
          simp only [released, allocations] at ha hf
          simp [scalarEvents, released, allocations, List.filterMap_append,
            ha, hf] at *
          omega
      | scalarLet p _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction
      | ownedLet p _ _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction

  | scalarLet shape represented typed ih =>
      cases run with
      | returnOwner h _ => obtain ⟨f, other⟩ := shape.head; exact False.elim (return_not_app h other)
      | free h _ _ _ => obtain ⟨f, other⟩ := shape.head; have := other.symm.trans h; contradiction
      | allocate a _ => exact False.elim (a.not_pure shape)
      | lend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLet shape' evaluated suffix =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          exact ih length (by simp [scalarLength]) suffix
      | ownedLet p _ _ _ => exact False.elim (p.not_pure shape)

  | ownedLet shape resolved bound typed ih =>
      cases run with
      | returnOwner h _ => obtain ⟨f, other⟩ := shape.head; exact False.elim (return_not_app h other)
      | free h _ _ _ => obtain ⟨f, other⟩ := shape.head; have := other.symm.trans h; contradiction
      | allocate a _ => exact False.elim (a.not_owned_binding shape resolved)
      | lend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLet p _ _ => exact False.elim (shape.not_pure p)
      | ownedLet shape' resolved' selected suffix =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          exact ih length scalarLength suffix

private theorem no_lease_starts (run : Graph.CoreReads g s token owner ctx root v es) :
    leaseStarts es = 0 := by
  induction run <;> simp_all [leaseStarts, List.filterMap_append]

theorem lease_counter (run : OwnedRuns g ctx root owners values s v es t) :
    t.nextLease = s.nextLease + leaseStarts es := by
  induction run using OwnedRuns.induct with
  | scalarLet _ _ _ ih => exact ih
  | ownedLet _ _ _ _ ih => exact ih
  | returnOwner => simp [leaseStarts]
  | free _ _ _ _ ih => simpa [leaseStarts, freedState] using ih
  | allocate _ _ ih => simpa [leaseStarts, allocatedState] using ih
  | lend _ _ _ read _ ih =>
      have hr := no_lease_starts read
      simp only [leaseStarts] at hr
      simp [OwnedLendTransfer.events, leaseStarts, List.filterMap_append, hr,
        OwnedLendTransfer.final, allocatedState, restored] at *
      omega

  | scalarLend _ _ _ read _ ih =>
      have hr := no_lease_starts read
      simp only [leaseStarts] at hr
      simp [scalarEvents, leaseStarts, List.filterMap_append, hr, restored] at *
      omega

/-- Completed nested lends restore every ambient lease; fresh token counters
may advance, but never move backwards. -/
theorem lease_frame (run : OwnedRuns g ctx root owners values s v es t) :
    t.lease = s.lease ∧ s.nextLease ≤ t.nextLease := by
  induction run using OwnedRuns.induct with
  | scalarLet _ _ _ ih => exact ih
  | ownedLet _ _ _ _ ih => exact ih
  | returnOwner => exact ⟨rfl, Nat.le_refl _⟩
  | free _ _ _ _ ih => exact ih
  | allocate _ _ ih => exact ih
  | lend _ _ _ _ _ ih =>
      refine ⟨ih.1, ?_⟩
      have h := ih.2
      dsimp [OwnedLendTransfer.final, allocatedState, restored] at h
      omega

  | scalarLend _ _ _ _ _ ih =>
      refine ⟨ih.1, ?_⟩
      have h := ih.2
      dsimp [OwnedLendTransfer.final, allocatedState, restored] at h
      omega

/-- Every token created during this execution is expired at return. This
covers all recursively nested reader scopes, not just the outermost one. -/
theorem created_tokens_expired (valid : Valid s) (run : OwnedRuns g ctx root owners values s v es t)
    (fresh : s.nextLease ≤ token) : t.lease token = none := by
  rw [(lease_frame run).1]
  cases h : s.lease token with
  | none => rfl
  | some x => have := (valid.leased token x h).1; omega


theorem OwnedRuns.deterministic (a : OwnedRuns g ctx root owners values s v es t)
    (b : OwnedRuns g ctx root owners values s w fs u) : v = w ∧ es = fs ∧ t = u := by
  induction a using OwnedRuns.induct generalizing w fs u with
  | returnOwner resolved selected =>
      cases b with
      | returnOwner resolved' selected' =>
          have eq := resolved.symm.trans resolved'; cases eq
          obtain ⟨rfl, rfl⟩ := LeaseErasure.select_deterministic selected selected'
          exact ⟨rfl, rfl, rfl⟩
      | free other _ _ _ => exact False.elim (return_not_free resolved other)
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; exact False.elim (return_not_app resolved other)
      | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; exact False.elim (return_not_lend resolved other)
      | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; exact False.elim (return_not_lend resolved other)
      | scalarLet p _ _ => obtain ⟨f, h⟩ := p.head; exact False.elim (return_not_app resolved h)
      | ownedLet p _ _ _ => obtain ⟨f, h⟩ := p.head; exact False.elim (return_not_app resolved h)

  | free shape resolved selected restRun ih =>
      cases b with
      | returnOwner other _ => exact False.elim (return_not_free other shape)
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; have := shape.symm.trans other; contradiction
      | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
      | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
      | free other resolved' selected' restRun' =>
          have eq := shape.symm.trans other; cases eq
          have eq := resolved.symm.trans resolved'; cases eq
          obtain ⟨rfl, rfl⟩ := LeaseErasure.select_deterministic selected selected'
          obtain ⟨rfl, rfl, rfl⟩ := ih restRun'
          exact ⟨rfl, rfl, rfl⟩
      | scalarLet p _ _ => obtain ⟨f, h⟩ := p.head; have := shape.symm.trans h; contradiction
      | ownedLet p _ _ _ => obtain ⟨f, h⟩ := p.head; have := shape.symm.trans h; contradiction

  | allocate a restRun ih =>
      cases b with
      | returnOwner other _ => obtain ⟨f, x, shape⟩ := a.application; exact False.elim (return_not_app other shape)
      | free other _ _ _ => obtain ⟨f, x, shape⟩ := a.application; have := shape.symm.trans other; contradiction
      | lend b _ _ _ _ =>
          obtain ⟨f, x, shape⟩ := a.application
          obtain ⟨r, k, other⟩ := b.head
          have := shape.symm.trans other; contradiction
      | scalarLend b _ _ _ _ =>
          obtain ⟨f, x, shape⟩ := a.application
          obtain ⟨r, k, other⟩ := b.head
          have := shape.symm.trans other; contradiction
      | allocate a' restRun' =>
          obtain ⟨rfl, rfl⟩ := a.unique a'
          obtain ⟨rfl, rfl, rfl⟩ := ih restRun'
          exact ⟨rfl, rfl, rfl⟩
      | scalarLet p _ _ => exact False.elim (a.not_pure p)
      | ownedLet p resolved _ _ => exact False.elim (a.not_owned_binding p resolved)

  | lend shape resolved selected read suffix ih =>
      cases b with
      | returnOwner other _ => obtain ⟨f, x, h⟩ := shape.head; exact False.elim (return_not_lend other h)
      | free other _ _ _ => obtain ⟨f, x, h⟩ := shape.head; have := h.symm.trans other; contradiction
      | allocate a _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.application
          have := h.symm.trans other; contradiction
      | scalarLend shape' _ _ _ _ => exact False.elim (shape'.not_owned shape)
      | lend shape' resolved' selected' read' suffix' =>
          obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          obtain ⟨rfl, rfl⟩ := LeaseErasure.select_deterministic selected selected'
          obtain ⟨rfl, rfl⟩ := core_reads_deterministic read read'
          obtain ⟨rfl, rfl, rfl⟩ := ih suffix'
          exact ⟨rfl, rfl, rfl⟩
      | scalarLet p _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction
      | ownedLet p _ _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction

  | scalarLend shape resolved selected read suffix ih =>
      cases b with
      | returnOwner other _ => obtain ⟨f, x, h⟩ := shape.head; exact False.elim (return_not_lend other h)
      | free other _ _ _ => obtain ⟨f, x, h⟩ := shape.head; have := h.symm.trans other; contradiction
      | allocate a _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.application
          have := h.symm.trans other; contradiction
      | lend shape' _ _ _ _ => exact False.elim (shape.not_owned shape')
      | scalarLend shape' resolved' selected' read' suffix' =>
          obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          obtain ⟨rfl, rfl⟩ := LeaseErasure.select_deterministic selected selected'
          obtain ⟨rfl, rfl⟩ := core_reads_deterministic read read'
          obtain ⟨rfl, rfl, rfl⟩ := ih suffix'
          exact ⟨rfl, rfl, rfl⟩
      | scalarLet p _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction
      | ownedLet p _ _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction

  | scalarLet shape evaluated suffix ih =>
      cases b with
      | returnOwner h _ => obtain ⟨f, other⟩ := shape.head; exact False.elim (return_not_app h other)
      | free h _ _ _ => obtain ⟨f, other⟩ := shape.head; have := other.symm.trans h; contradiction
      | allocate a _ => exact False.elim (a.not_pure shape)
      | lend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLet shape' evaluated' suffix' =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          have eq := PureOwnedScalar.Eval.deterministic evaluated evaluated'
          subst eq
          exact ih suffix'
      | ownedLet p _ _ _ => exact False.elim (p.not_pure shape)

  | ownedLet shape resolved selected suffix ih =>
      cases b with
      | returnOwner h _ => obtain ⟨f, other⟩ := shape.head; exact False.elim (return_not_app h other)
      | free h _ _ _ => obtain ⟨f, other⟩ := shape.head; have := other.symm.trans h; contradiction
      | allocate a _ => exact False.elim (a.not_owned_binding shape resolved)
      | lend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLet p _ _ => exact False.elim (shape.not_pure p)
      | ownedLet shape' resolved' selected' suffix' =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          exact ih suffix'


/-- The returned capability is live and unborrowed, not a leaked or freed alias. -/
theorem returned_live (typed : OwnedTyped g ctx n m root) (length : owners.length = n)
    (scalarLength : values.length = m) (valid : Valid s) (owned : Owns s owners)
    (run : OwnedRuns g ctx root owners values s v es t) :
    t.live v = true ∧ Unborrowed t v := by
  have result := (execution_safe typed length scalarLength valid owned run).2.2
  exact ⟨result.live v (by simp), result.leaseFree v (by simp)⟩

theorem returned_never_freed (typed : OwnedTyped g ctx n m root) (length : owners.length = n)
    (scalarLength : values.length = m) (valid : Valid s) (owned : Owns s owners)
    (run : OwnedRuns g ctx root owners values s v es t) : (released es).count v = 0 := by
  apply List.count_eq_zero.mpr
  intro member
  have safe := (execution_safe typed length scalarLength valid owned run).1
  have dead := released_dead valid safe (released_mem.mp member)
  have live := (returned_live typed length scalarLength valid owned run).1
  rw [live] at dead
  contradiction

/-- Provenance is derived from graph execution and exact conservation, not
supplied as a certificate about the returned address. -/
theorem returned_origin (typed : OwnedTyped g ctx n m root) (length : owners.length = n)
    (scalarLength : values.length = m) (valid : Valid s) (owned : Owns s owners)
    (run : OwnedRuns g ctx root owners values s v es t) : v ∈ owners ∨ v ∈ allocations es := by
  have eq := release_conservation typed length scalarLength run v
  have zero := returned_never_freed typed length scalarLength valid owned run
  simp only [zero, List.count_cons, List.count_nil, beq_self_eq_true, ite_true] at eq
  by_cases h : v ∈ owners
  · exact Or.inl h
  · have absent := List.count_eq_zero.mpr h
    right
    apply List.count_pos_iff.mp
    omega

/-- All tracked capabilities other than the returned one are released once. -/
theorem other_released (typed : OwnedTyped g ctx n m root) (length : owners.length = n)
    (scalarLength : values.length = m) (valid : Valid s) (owned : Owns s owners)
    (run : OwnedRuns g ctx root owners values s v es t)
    (tracked : x ∈ owners ∨ x ∈ allocations es) (other : x ≠ v) :
    (released es).count x = 1 ∧ t.live x = false := by
  have safe := (execution_safe typed length scalarLength valid owned run).1
  have eq := release_conservation typed length scalarLength run x
  have absent : [v].count x = 0 := by simp [Ne.symm other]
  rw [absent, Nat.add_zero] at eq
  have positive : 0 < (released es).count x := by
    rcases tracked with initial | allocated
    · have := List.count_pos_iff.mpr initial; omega
    · have := List.count_pos_iff.mpr allocated; omega
  have member := List.count_pos_iff.mp positive
  have count := (releases_distinct valid safe).count (a := x)
  exact ⟨by simpa [member] using count, released_dead valid safe (released_mem.mp member)⟩

/-- Under initial heap coverage the returned identity is the only live object. -/
theorem heap_singleton (typed : OwnedTyped g ctx n m root) (length : owners.length = n)
    (scalarLength : values.length = m) (valid : Valid s) (owned : Owns s owners)
    (run : OwnedRuns g ctx root owners values s v es t)
    (coverage : ∀ x, s.live x = true → x ∈ owners) :
    ∀ x, t.live x = true ↔ x = v := by
  intro x
  constructor
  · intro live
    by_cases eq : x = v
    · exact eq
    have other : x ≠ v := eq
    have safe := (execution_safe typed length scalarLength valid owned run).1
    have origin := live_origin safe live
    have tracked : x ∈ owners ∨ x ∈ allocations es := by
      rcases origin with initial | allocated
      · exact Or.inl (coverage x initial)
      · exact Or.inr allocated
    have dead := (other_released typed length scalarLength valid owned run tracked other).2
    rw [live] at dead
    contradiction
  · intro eq
    subst x
    exact (returned_live typed length scalarLength valid owned run).1

/-- Fresh lexical handoff, not revival of the producer's local aliases.
The consumer is a derivation of the existing scalar specialization. This is
semantic sequential composition, not yet a general Core App lowering theorem. -/
def consumerContext : Context := [.owner 0]

theorem consumer_parameter (v : Nat) :
    LinearCoreCallers.bindings (ownerView consumerContext) [v] = [some v] := rfl

theorem consumer_has_no_old_alias (k : Nat) : consumerContext[k+1]? = none := by
  simp [consumerContext]

theorem consume_safe (producer : OwnedTyped g ctx n m root) (consumer : Typed g consumerContext 1 0 body)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (produce : OwnedRuns g ctx root owners values s v beforeEvents middle)
    (consume : Runs g consumerContext body [v] [] middle value suffix t) :
    Steps s (beforeEvents ++ suffix) t ∧ Valid t ∧ Owns t [] ∧
    (released (beforeEvents ++ suffix)).count v = 1 ∧ t.live v = false := by
  obtain ⟨before, midValid, midOwned⟩ := execution_safe producer length scalarLength valid owned produce
  obtain ⟨after, finalValid, finalOwned⟩ := OwnedCoreContinuation.execution_safe consumer rfl rfl midValid midOwned consume
  have zero := returned_never_freed producer length scalarLength valid owned produce
  obtain ⟨once, dead⟩ := OwnedCoreContinuation.no_tracked_leaks (x := v) consumer rfl rfl midValid midOwned consume (Or.inl (by simp))
  exact ⟨ScopedLend.steps_append before after, finalValid, finalOwned,
    by simp [releases_append, List.count_append, zero, once], dead⟩

/-- Typing supplies both producer and consumer execution: no successful run is
an assumption in the existence statement. -/
theorem consume_total (producer : OwnedTyped g ctx n m root) (consumer : Typed g consumerContext 1 0 body)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) :
    ∃ v beforeEvents middle value suffix t,
      OwnedRuns g ctx root owners values s v beforeEvents middle ∧
      Runs g consumerContext body [v] [] middle value suffix t ∧
      Steps s (beforeEvents ++ suffix) t ∧ Valid t ∧
      (released (beforeEvents ++ suffix)).count v = 1 ∧ t.live v = false := by
  obtain ⟨v, beforeEvents, middle, produce⟩ := total producer length scalarLength valid owned
  obtain ⟨_, midValid, midOwned⟩ := execution_safe producer length scalarLength valid owned produce
  obtain ⟨value, suffix, t, consume⟩ := OwnedCoreContinuation.total (owners := [v]) (values := []) consumer rfl rfl midValid midOwned
  obtain ⟨safe, finalValid, _, once, dead⟩ := consume_safe producer consumer length scalarLength valid owned produce consume
  exact ⟨v, beforeEvents, middle, value, suffix, t, produce, consume, safe, finalValid, once, dead⟩

/-- Composition accounts for *all* initial and newly created resources, not
only the value crossing the handoff. -/
theorem consume_conservation (producer : OwnedTyped g ctx n m root) (consumer : Typed g consumerContext 1 0 body)
    (length : owners.length = n) (scalarLength : values.length = m)
    (produce : OwnedRuns g ctx root owners values s v beforeEvents middle)
    (consume : Runs g consumerContext body [v] [] middle value suffix t) (x : Nat) :
    (released (beforeEvents ++ suffix)).count x = owners.count x + (allocations (beforeEvents ++ suffix)).count x := by
  have first := release_conservation producer length scalarLength produce x
  have last := OwnedCoreContinuation.release_conservation consumer rfl rfl consume x
  simp only [releases_append, allocations_append, List.count_append]
  omega

theorem consume_no_leaks (producer : OwnedTyped g ctx n m root) (consumer : Typed g consumerContext 1 0 body)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (produce : OwnedRuns g ctx root owners values s v beforeEvents middle)
    (consume : Runs g consumerContext body [v] [] middle value suffix t)
    (tracked : x ∈ owners ∨ x ∈ allocations (beforeEvents ++ suffix)) :
    (released (beforeEvents ++ suffix)).count x = 1 ∧ t.live x = false := by
  have safe := (consume_safe producer consumer length scalarLength valid owned produce consume).1
  have eq := consume_conservation producer consumer length scalarLength produce consume x
  have positive : 0 < (released (beforeEvents ++ suffix)).count x := by
    rcases tracked with initial | allocated
    · have := List.count_pos_iff.mpr initial; omega
    · have := List.count_pos_iff.mpr allocated; omega
  have member := List.count_pos_iff.mp positive
  have count := (releases_distinct valid safe).count (a := x)
  exact ⟨by simpa [member] using count, released_dead valid safe (released_mem.mp member)⟩

/-- Initial coverage closes the composed program's entire heap, not just the
resources named at the return boundary. Ambient untracked objects are excluded. -/
theorem consume_heap_empty (producer : OwnedTyped g ctx n m root) (consumer : Typed g consumerContext 1 0 body)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (produce : OwnedRuns g ctx root owners values s v beforeEvents middle)
    (consume : Runs g consumerContext body [v] [] middle value suffix t)
    (coverage : ∀ x, s.live x = true → x ∈ owners) : ∀ x, t.live x = false := by
  intro x
  cases live : t.live x with
  | false => rfl
  | true =>
      have safe := (consume_safe producer consumer length scalarLength valid owned produce consume).1
      have origin := live_origin safe live
      have tracked : x ∈ owners ∨ x ∈ allocations (beforeEvents ++ suffix) := by
        rcases origin with initial | allocated
        · exact Or.inl (coverage x initial)
        · exact Or.inr allocated
      have dead := (consume_no_leaks producer consumer length scalarLength valid owned produce consume tracked).2
      rw [live] at dead
      contradiction

end Jihoo.OwnedCoreResults
