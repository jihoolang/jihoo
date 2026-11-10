import Jihoo.OwnedScalarContext

/-! Declarative ownership and scalar-binding rules on original Core graph
nodes. Literal/bound-scalar return, free, allocation and both scalar/owned-result
Lends share one judgment and execution relation. Owner and scalar environments
are distinct; no accepted-callee or safe-trace premise is assumed. Numeric reader
bounds need a separate heap/literal invariant: this module alone does not claim
full I64/dependent typing or whole-Core semantics. -/
namespace Jihoo.OwnedCoreContinuation
open HeapLeases ScopedLend LinearHeapPrograms
open OwnedScalarContext
abbrev Shape := OwnedLendContext.Shape

inductive Allocation (g : Graph.Graph) (root value body : Nat) : Prop where
  | intro (function argument domain length payload : Nat) :
      Graph.nodeAt g root = .app function argument →
      Graph.nodeAt g function = .lam false domain body →
      Graph.bufferOne g domain = true →
      Graph.nodeAt g argument = .alloc length payload →
      Graph.nodeAt g length = .natural 1 →
      Graph.nodeAt g payload = .integer value → Allocation g root value body

theorem Allocation.unique (a : Allocation g root v b) (a' : Allocation g root v' b') :
    v = v' ∧ b = b' := by
  obtain ⟨f, arg, d, l, p, h, hf, hd, ha, hl, hp⟩ := a
  obtain ⟨f', arg', d', l', p', h', hf', hd', ha', hl', hp'⟩ := a'
  have eq := h.symm.trans h'; cases eq
  have eq := hf.symm.trans hf'; cases eq
  have eq := ha.symm.trans ha'; cases eq
  have eq := hp.symm.trans hp'; cases eq
  exact ⟨rfl, rfl⟩

abbrev LiteralBound := OwnedScalarContext.LiteralBound

inductive Typed (g : Graph.Graph) : Context → Nat → Nat → Nat → Prop where
  | finish : resultAt g ctx root = some result → result.check m = true → LiteralBound result → Typed g ctx 0 m root
  | free : Graph.nodeAt g root = .free owner body → ownerSlot g ctx owner = some slot →
      slot < n → Typed g (consumed slot ctx) (n - 1) m body → Typed g ctx n m root
  | allocate : Allocation g root value body → value < 2^63 →
      Typed g (fresh ctx) (n + 1) m body → Typed g ctx n m root

  | lend : Shape g root owner init body → ownerSlot g ctx owner = some slot → slot < n →
      Graph.Represents g (readerRoles ctx slot) init reader →
      Typed g (ownedReturned ctx slot) (n + 1) m body → Typed g ctx n m root

  | scalarLend : ScalarShape g root owner init body → ownerSlot g ctx owner = some slot → slot < n →
      Graph.Represents g (readerRoles ctx slot) init reader →
      Typed g (scalarReturned ctx slot) n (m + 1) body → Typed g ctx n m root

def freedState (s : State) (x : Nat) : State := { s with live := put s.live x false }

inductive Runs (g : Graph.Graph) : Context → Nat → List Nat → List Nat → State → Nat → List Event → State → Prop where
  | finish : resultAt g ctx root = some result → result.eval values = some value → Runs g ctx root owners values s value [] s
  | free : Graph.nodeAt g root = .free owner body → ownerSlot g ctx owner = some slot →
      Select owners slot x rest → Runs g (consumed slot ctx) body rest values (freedState s x) value events t →
      Runs g ctx root owners values s value (.free x :: events) t
  | allocate : Allocation g root payload body →
      Runs g (fresh ctx) body (s.nextObject :: owners) values (allocatedState s payload) value events t →
      Runs g ctx root owners values s value (.alloc s.nextObject payload :: events) t

  | lend : Shape g root owner init body → ownerSlot g ctx owner = some slot →
      Select owners slot x rest →
      Graph.CoreReads g (opened s x) s.nextLease x (readerRoles ctx slot) init copied reads →
      Runs g (ownedReturned ctx slot) body (s.nextObject :: owners) values
        (OwnedLendTransfer.final s copied) value suffix t →
      Runs g ctx root owners values s value (OwnedLendTransfer.events s x copied reads ++ suffix) t

  | scalarLend : ScalarShape g root owner init body → ownerSlot g ctx owner = some slot →
      Select owners slot x rest →
      Graph.CoreReads g (opened s x) s.nextLease x (readerRoles ctx slot) init copied reads →
      Runs g (scalarReturned ctx slot) body owners (copied :: values)
        (restored s) value suffix t →
      Runs g ctx root owners values s value (scalarEvents s x reads ++ suffix) t

theorem free_owns (owned : Owns s owners) (selected : Select owners slot x rest) :
    Owns (freedState s x) rest := by
  obtain ⟨distinct, absent⟩ := selected.unique owned.distinct
  refine ⟨distinct, ?_, ?_⟩
  · intro y hy
    have ne : y ≠ x := fun eq => absent (eq ▸ hy)
    simp [freedState, put, ne, owned.live y (selected.subset y hy)]
  · intro y hy
    exact owned.leaseFree y (selected.subset y hy)

theorem total (typed : Typed g ctx n m root) (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) :
    ∃ value events t, Runs g ctx root owners values s value events t := by
  induction typed generalizing owners values s with
  | finish shape checked bound =>
      have : owners = [] := List.length_eq_zero_iff.mp length
      subst owners
      obtain ⟨v, hv⟩ := ScalarCoreCallers.Result.total checked scalarLength
      exact ⟨v, [], s, .finish shape hv⟩
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

theorem Allocation.application (a : Allocation g root v b) :
    ∃ f x, Graph.nodeAt g root = .app f x := by
  cases a with | intro f x _ _ _ h _ _ _ _ _ => exact ⟨f, x, h⟩

theorem finish_head (h : resultAt g ctx root = some result) :
    (∃ v, Graph.nodeAt g root = .integer v) ∨ (∃ k, Graph.nodeAt g root = .var k) := by
  cases hg : Graph.nodeAt g root <;> simp [resultAt, ScalarCoreCallers.resultAt, hg] at h
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩

theorem finish_not_free (h : resultAt g ctx root = some result)
    (shape : Graph.nodeAt g root = .free owner body) : False := by
  simp [resultAt, ScalarCoreCallers.resultAt, shape] at h
theorem finish_not_app (h : resultAt g ctx root = some result)
    (shape : Graph.nodeAt g root = .app f a) : False := by
  simp [resultAt, ScalarCoreCallers.resultAt, shape] at h
theorem finish_not_lend (h : resultAt g ctx root = some result)
    (shape : Graph.nodeAt g root = .lend o r c) : False := by
  simp [resultAt, ScalarCoreCallers.resultAt, shape] at h

theorem execution_safe (typed : Typed g ctx n m root) (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) (run : Runs g ctx root owners values s v es t) :
    Steps s es t ∧ Valid t ∧ Owns t [] := by
  induction typed generalizing owners values s v es t with
  | finish shape checked bound =>
      cases run with
      | finish _ _ => exact ⟨.nil, valid, ⟨by simp, by simp, by simp⟩⟩
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
          obtain ⟨steps, vt, ot⟩ := ih (by have := selected.length; omega) scalarLength
            (step_valid valid step) (free_owns owned selected) restRun
          exact ⟨.cons step steps, vt, ot⟩
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
          obtain ⟨steps, vt, ot⟩ := ih (by simp [length]) scalarLength
            (step_valid valid (Step.alloc (value := _))) (allocate_owns valid owned) restRun
          exact ⟨.cons .alloc steps, vt, ot⟩

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
          obtain ⟨steps, vt, ot⟩ := ih (by simp [length]) scalarLength (steps_valid valid pre)
            (OwnedLendTransfer.transfer_owns valid owned) suffix
          exact ⟨steps_append pre steps, vt, ot⟩

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
          obtain ⟨steps, vt, ot⟩ := ih length (by simp [scalarLength]) (steps_valid valid pre)
            (restored_owns owned) suffix
          exact ⟨steps_append pre steps, vt, ot⟩

/-- Accounting follows the original graph execution, including allocations
inside the continuation, rather than a separately supplied usage trace. -/
theorem release_conservation (typed : Typed g ctx n m root) (length : owners.length = n) (scalarLength : values.length = m)
    (run : Runs g ctx root owners values s v es t) (x : Nat) :
    (released es).count x = owners.count x + (allocations es).count x := by
  induction typed generalizing owners values s v es t with
  | finish shape checked bound =>
      cases run with
      | finish _ _ =>
          have : owners = [] := List.length_eq_zero_iff.mp length
          subst owners
          simp [released, allocations]
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
          have h := selected.count x
          have hr := ih (by have := selected.length; omega) scalarLength restRun
          simp only [released, allocations, List.filterMap_cons, List.count_cons] at *
          simp only [beq_iff_eq] at *
          omega
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
          have hr := ih (by simp [length]) scalarLength restRun
          simp only [released, allocations, List.filterMap_cons, List.count_cons] at *
          omega

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
          have hr := ih (by simp [length]) scalarLength suffix
          have ha := reader_allocations reader
          have hf := reader_releases reader
          simp only [released, allocations] at ha hf
          simp [OwnedLendTransfer.events, released, allocations, List.filterMap_append,
            ha, hf, List.count_cons] at *
          omega
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
          have hr := ih length (by simp [scalarLength]) suffix
          have ha := reader_allocations reader
          have hf := reader_releases reader
          simp only [released, allocations] at ha hf
          simp [scalarEvents, released, allocations, List.filterMap_append,
            ha, hf] at *
          omega

theorem no_tracked_leaks (typed : Typed g ctx n m root) (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) (run : Runs g ctx root owners values s v es t)
    (tracked : x ∈ owners ∨ x ∈ allocations es) :
    (released es).count x = 1 ∧ t.live x = false := by
  have steps := (execution_safe typed length scalarLength valid owned run).1
  have conserved := release_conservation typed length scalarLength run x
  have positive : 0 < (released es).count x := by
    rcases tracked with initial | allocated
    · have := List.count_pos_iff.mpr initial; omega
    · have := List.count_pos_iff.mpr allocated; omega
  have member := List.count_pos_iff.mp positive
  have count := (releases_distinct valid steps).count (a := x)
  exact ⟨by simpa [member] using count, released_dead valid steps (released_mem.mp member)⟩

/-- Number of lexical reader entries in the actual heap event trace. -/
def leaseStarts (events : List Event) : Nat :=
  (events.filterMap fun e => match e with | .beginLease _ _ => some () | _ => none).length

theorem leaseStarts_append : leaseStarts (xs ++ ys) = leaseStarts xs + leaseStarts ys := by
  simp [leaseStarts, List.filterMap_append]

private theorem CoreReads.no_lease_starts (run : Graph.CoreReads g s token owner ctx root v es) :
    leaseStarts es = 0 := by
  induction run <;> simp_all [leaseStarts, List.filterMap_append]

theorem lease_counter (run : Runs g ctx root owners values s v es t) :
    t.nextLease = s.nextLease + leaseStarts es := by
  induction run with
  | finish => simp [leaseStarts]
  | free _ _ _ _ ih => simpa [leaseStarts, freedState] using ih
  | allocate _ _ ih => simpa [leaseStarts, allocatedState] using ih
  | lend _ _ _ read _ ih =>
      have hr := CoreReads.no_lease_starts read
      simp only [leaseStarts] at hr
      simp [OwnedLendTransfer.events, leaseStarts, List.filterMap_append, hr,
        OwnedLendTransfer.final, allocatedState, restored] at *
      omega

  | scalarLend _ _ _ read _ ih =>
      have hr := CoreReads.no_lease_starts read
      simp only [leaseStarts] at hr
      simp [scalarEvents, leaseStarts, List.filterMap_append, hr, restored] at *
      omega

/-- Completed nested lends restore every ambient lease; fresh token counters
may advance, but never move backwards. -/
theorem lease_frame (run : Runs g ctx root owners values s v es t) :
    t.lease = s.lease ∧ s.nextLease ≤ t.nextLease := by
  induction run with
  | finish => exact ⟨rfl, Nat.le_refl _⟩
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
theorem created_tokens_expired (valid : Valid s) (run : Runs g ctx root owners values s v es t)
    (fresh : s.nextLease ≤ token) : t.lease token = none := by
  rw [(lease_frame run).1]
  cases h : s.lease token with
  | none => rfl
  | some x => have := (valid.leased token x h).1; omega

/-- If the initial capability environment covers every live object, every
final object is dead. Ambient objects outside that environment are not owned. -/
theorem heap_empty (typed : Typed g ctx n m root) (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) (run : Runs g ctx root owners values s v es t)
    (coverage : ∀ x, s.live x = true → x ∈ owners) : ∀ x, t.live x = false := by
  intro x
  cases live : t.live x with
  | false => rfl
  | true =>
      have steps := (execution_safe typed length scalarLength valid owned run).1
      have origin := live_origin steps live
      have tracked : x ∈ owners ∨ x ∈ allocations es := by
        rcases origin with initial | allocated
        · exact Or.inl (coverage x initial)
        · exact Or.inr allocated
      have dead := (no_tracked_leaks typed length scalarLength valid owned run tracked).2
      rw [live] at dead
      contradiction


theorem Typed.free_inversion (typed : Typed g ctx n m root)
    (shape : Graph.nodeAt g root = .free owner body) :
    ∃ slot, ownerSlot g ctx owner = some slot ∧ slot < n ∧
      Typed g (consumed slot ctx) (n - 1) m body := by
  cases typed with
  | finish h _ _ => exact False.elim (finish_not_free h shape)
  | free other resolved bound rest =>
      have eq := shape.symm.trans other; cases eq
      exact ⟨_, resolved, bound, rest⟩
  | allocate a _ _ => obtain ⟨f, x, other⟩ := a.application; have := shape.symm.trans other; contradiction
  | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
  | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction

theorem Typed.finish_inversion (typed : Typed g ctx n m root)
    (shape : Graph.nodeAt g root = .integer value) : n = 0 ∧ value < 2^63 := by
  cases typed with
  | finish h _ bound =>
      simp [resultAt, ScalarCoreCallers.resultAt, shape] at h
      subst h
      exact ⟨rfl, bound⟩
  | free other _ _ _ => have := shape.symm.trans other; contradiction
  | allocate a _ _ => obtain ⟨f, x, other⟩ := a.application; have := shape.symm.trans other; contradiction
  | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
  | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction

theorem dead_owner_rejected (shape : Graph.nodeAt g root = .free owner body)
    (dead : ownerSlot g ctx owner = none) : ¬ Typed g ctx n m root := by
  intro typed
  obtain ⟨slot, resolved, _⟩ := typed.free_inversion shape
  rw [dead] at resolved
  contradiction

theorem Typed.lend_inversion (typed : Typed g ctx n m root)
    (shape : Shape g root owner init body) :
    ∃ slot reader, ownerSlot g ctx owner = some slot ∧ slot < n ∧
      Graph.Represents g (readerRoles ctx slot) init reader ∧
      Typed g (ownedReturned ctx slot) (n + 1) m body := by
  cases typed with
  | finish h _ _ => obtain ⟨f, x, other⟩ := shape.head; exact False.elim (finish_not_lend h other)
  | free other _ _ _ => obtain ⟨f, x, h⟩ := shape.head; have := h.symm.trans other; contradiction
  | allocate a _ _ =>
      obtain ⟨f, x, h⟩ := shape.head
      obtain ⟨r, k, other⟩ := a.application
      have := h.symm.trans other; contradiction
  | lend shape' resolved bound reading rest =>
      obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
      exact ⟨_, _, resolved, bound, reading, rest⟩
  | scalarLend shape' _ _ _ _ => exact False.elim (shape'.not_owned shape)

theorem Typed.scalarLend_inversion (typed : Typed g ctx n m root)
    (shape : ScalarShape g root owner init body) :
    ∃ slot reader, ownerSlot g ctx owner = some slot ∧ slot < n ∧
      Graph.Represents g (readerRoles ctx slot) init reader ∧
      Typed g (scalarReturned ctx slot) n (m + 1) body := by
  cases typed with
  | finish h _ _ => obtain ⟨f, x, other⟩ := shape.head; exact False.elim (finish_not_lend h other)
  | free other _ _ _ => obtain ⟨f, x, h⟩ := shape.head; have := h.symm.trans other; contradiction
  | allocate a _ _ =>
      obtain ⟨f, x, h⟩ := shape.head
      obtain ⟨r, k, other⟩ := a.application
      have := h.symm.trans other; contradiction
  | lend shape' _ _ _ _ => exact False.elim (shape.not_owned shape')
  | scalarLend shape' resolved bound reading rest =>
      obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
      exact ⟨_, _, resolved, bound, reading, rest⟩

private theorem core_reads_deterministic (a : Graph.CoreReads g s token owner ctx root v es)
    (b : Graph.CoreReads g s token owner ctx root w fs) : v = w ∧ es = fs := by
  induction a generalizing w fs with
  | scalar shape => cases b <;> simp_all <;> first | exact ih (by assumption) | omega
  | read shape role bound lease => cases b <;> simp_all <;> first | exact ih (by assumption) | omega
  | strict shape _ _ ia ib =>
      cases b <;> simp_all
      obtain ⟨rfl, rfl⟩ := ia (by assumption)
      obtain ⟨rfl, rfl⟩ := ib (by assumption)
      exact ⟨rfl, rfl⟩
  | app shape lam ty _ _ ia ib =>
      cases b <;> simp_all
      obtain ⟨rfl, rfl⟩ := ia (by assumption)
      obtain ⟨rfl, rfl⟩ := ib (by assumption)
      exact ⟨rfl, rfl⟩
  | yes shape left right bound _ ih => cases b <;> simp_all <;> first | exact ih (by assumption) | omega
  | no shape left right bound _ ih => cases b <;> simp_all <;> first | exact ih (by assumption) | omega

/-- The graph semantics fixes the actual returned scalar, complete effect
trace and final heap, independently of any particular typing derivation. -/
theorem Runs.deterministic (a : Runs g ctx root owners values s v es t)
    (b : Runs g ctx root owners values s w fs u) : v = w ∧ es = fs ∧ t = u := by
  induction a generalizing w fs u with
  | finish shape value =>
      cases b with
      | finish shape' value' =>
          have eq := shape.symm.trans shape'; cases eq
          have eq := value.symm.trans value'; cases eq
          exact ⟨rfl, rfl, rfl⟩
      | free other _ _ _ => exact False.elim (finish_not_free shape other)
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; exact False.elim (finish_not_app shape other)
      | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; exact False.elim (finish_not_lend shape other)
      | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; exact False.elim (finish_not_lend shape other)
  | free shape resolved selected restRun ih =>
      cases b with
      | finish other _ => exact False.elim (finish_not_free other shape)
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; have := shape.symm.trans other; contradiction
      | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
      | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
      | free other resolved' selected' restRun' =>
          have eq := shape.symm.trans other; cases eq
          have eq := resolved.symm.trans resolved'; cases eq
          obtain ⟨rfl, rfl⟩ := LeaseErasure.select_deterministic selected selected'
          obtain ⟨rfl, rfl, rfl⟩ := ih restRun'
          exact ⟨rfl, rfl, rfl⟩
  | allocate a restRun ih =>
      cases b with
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
      | allocate a' restRun' =>
          obtain ⟨rfl, rfl⟩ := a.unique a'
          obtain ⟨rfl, rfl, rfl⟩ := ih restRun'
          exact ⟨rfl, rfl, rfl⟩
  | lend shape resolved selected read suffix ih =>
      cases b with
      | finish other _ => obtain ⟨f, x, h⟩ := shape.head; exact False.elim (finish_not_lend other h)
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
  | scalarLend shape resolved selected read suffix ih =>
      cases b with
      | finish other _ => obtain ⟨f, x, h⟩ := shape.head; exact False.elim (finish_not_lend other h)
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

end Jihoo.OwnedCoreContinuation
