import Jihoo.OwnedCoreResults

/-! Recursive syntactic closure of the existing resource judgment under a
capture-free direct Buffer1 application whose argument is itself an App.
Argument evaluation uses the original environment. The body is checked only
against its parameter, so no outer lexical binding can be read or revived.
This is not arbitrary dependent substitution, higher-order closure invocation,
or a proof about the production lowerer. -/
namespace Jihoo.OwnedCoreApplications
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext OwnedCoreContinuation

inductive Shape (g : Graph.Graph) (root argument body : Nat) : Prop where
  | intro (function domain producer argumentValue : Nat) :
      Graph.nodeAt g root = .app function argument →
      Graph.nodeAt g function = .lam false domain body →
      Graph.bufferOne g domain = true →
      Graph.nodeAt g argument = .app producer argumentValue →
      Shape g root argument body

theorem Shape.unique (a : Shape g root arg body) (b : Shape g root arg' body') :
    arg = arg' ∧ body = body' := by
  cases a with
  | intro f d p v h hf _ _ =>
    cases b with
    | intro f' d' p' v' h' hf' _ _ =>
      have eq := h.symm.trans h'; cases eq
      have eq := hf.symm.trans hf'; cases eq
      exact ⟨rfl, rfl⟩

theorem Shape.not_core (shape : Shape g root arg body)
    (typed : Types g kind ctx n m root) : False := by
  cases shape with
  | intro f d p v head lam buffer argument =>
    cases typed with
    | finish result _ _ =>
        exact finish_not_app result head
    | returnOwner resolved => exact OwnedCoreResults.return_not_app resolved head
    | free h _ _ _ => have eq := head.symm.trans h; contradiction
    | allocate alloc _ _ =>
        cases alloc with
        | intro fn arg ty size value h hf _ ha _ _ =>
            have eq := head.symm.trans h; cases eq
            have eq := argument.symm.trans ha; contradiction
    | lend h _ _ _ _ =>
        obtain ⟨reader, cont, h⟩ := h.head
        have eq := head.symm.trans h; contradiction
    | scalarLend h _ _ _ _ =>
        obtain ⟨reader, cont, h⟩ := h.head
        have eq := head.symm.trans h; contradiction
    | scalarLet h _ _ =>
        cases h with
        | intro fn ty h hf ht =>
            have eq := head.symm.trans h; cases eq
            have eq := lam.symm.trans hf; cases eq
            simp [Graph.bufferOne, ht] at buffer
    | ownedLet h resolved _ _ =>
        cases h with
        | intro fn ty h _ _ =>
            have eq := head.symm.trans h; cases eq
            obtain ⟨k, varShape, _⟩ := OwnedArgumentBinding.ownerSlot_variable resolved
            have eq := argument.symm.trans varShape; contradiction

/-- Old constructor rules are leaves; actual applications compose recursively. -/
inductive Typing (g : Graph.Graph) : ResultKind → Context → Nat → Nat → Nat → Prop where
  | core : Types g kind ctx n m root → Typing g kind ctx n m root
  | apply : Shape g root argument body → Typing g .owned ctx n m argument →
      Typing g kind OwnedCoreResults.consumerContext 1 0 body →
      Typing g kind ctx n m root

inductive Evaluation (g : Graph.Graph) : ResultKind → Context → Nat → List Nat → List Nat → State → Nat → List Event → State → Prop where
  | core : Exec g kind ctx root owners values s value events t →
      Evaluation g kind ctx root owners values s value events t
  | apply : Shape g root argument body →
      Evaluation g .owned ctx argument owners values s returned before middle →
      Evaluation g kind OwnedCoreResults.consumerContext body [returned] [] middle value after t →
      Evaluation g kind ctx root owners values s value (before ++ after) t

def resultOwners : ResultKind → Nat → List Nat
  | .scalar, _ => []
  | .owned, v => [v]

theorem core_total (typed : Types g kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) :
    ∃ value events t, Exec g kind ctx root owners values s value events t := by
  cases kind with
  | scalar => exact OwnedCoreContinuation.total typed length scalarLength valid owned
  | owned => exact OwnedCoreResults.total typed length scalarLength valid owned

theorem core_safe (typed : Types g kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (run : Exec g kind ctx root owners values s value events t) :
    Steps s events t ∧ Valid t ∧ Owns t (resultOwners kind value) := by
  cases kind with
  | scalar => exact OwnedCoreContinuation.execution_safe typed length scalarLength valid owned run
  | owned => exact OwnedCoreResults.execution_safe typed length scalarLength valid owned run

/-- Untyped evaluation leaves cannot impersonate the new application rule. -/
theorem Shape.not_exec (shape : Shape g root arg body)
    (run : Exec g kind ctx root owners values s value events t) : False := by
  cases shape with
  | intro f d p v head lam buffer argument =>
    cases run with
    | finish result _ => exact finish_not_app result head
    | returnOwner resolved _ => exact OwnedCoreResults.return_not_app resolved head
    | free h _ _ _ => have eq := head.symm.trans h; contradiction
    | allocate alloc _ =>
        cases alloc with
        | intro fn arg ty size value h hf _ ha _ _ =>
            have eq := head.symm.trans h; cases eq
            have eq := argument.symm.trans ha; contradiction
    | lend h _ _ _ _ =>
        obtain ⟨reader, cont, h⟩ := h.head
        have eq := head.symm.trans h; contradiction
    | scalarLend h _ _ _ _ =>
        obtain ⟨reader, cont, h⟩ := h.head
        have eq := head.symm.trans h; contradiction
    | scalarLet h _ _ =>
        cases h with
        | intro fn ty h hf ht =>
            have eq := head.symm.trans h; cases eq
            have eq := lam.symm.trans hf; cases eq
            simp [Graph.bufferOne, ht] at buffer
    | ownedLet h resolved _ _ =>
        cases h with
        | intro fn ty h _ _ =>
            have eq := head.symm.trans h; cases eq
            obtain ⟨k, varShape, _⟩ := OwnedArgumentBinding.ownerSlot_variable resolved
            have eq := argument.symm.trans varShape; contradiction

theorem execution_safe (typed : Typing g kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (run : Evaluation g kind ctx root owners values s value events t) :
    Steps s events t ∧ Valid t ∧ Owns t (resultOwners kind value) := by
  induction typed generalizing owners values s value events t with
  | core typed =>
      cases run with
      | core run => exact core_safe typed length scalarLength valid owned run
      | apply shape _ _ => exact False.elim (shape.not_core typed)
  | apply shape producer consumer ihp ihc =>
      cases run with
      | core run => exact False.elim (shape.not_exec run)
      | apply shape' produce consume =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          obtain ⟨before, midValid, midOwned⟩ := ihp length scalarLength valid owned produce
          obtain ⟨after, finalValid, finalOwned⟩ := ihc rfl rfl midValid midOwned consume
          exact ⟨steps_append before after, finalValid, finalOwned⟩

theorem total (typed : Typing g kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) :
    ∃ value events t, Evaluation g kind ctx root owners values s value events t := by
  induction typed generalizing owners values s with
  | core typed =>
      obtain ⟨v, es, t, run⟩ := core_total typed length scalarLength valid owned
      exact ⟨v, es, t, .core run⟩
  | apply shape producer consumer ihp ihc =>
      obtain ⟨v, es, middle, produce⟩ := ihp length scalarLength valid owned
      obtain ⟨_, midValid, midOwned⟩ := execution_safe producer length scalarLength valid owned produce
      obtain ⟨result, suffix, t, consume⟩ := ihc (owners := [v]) (values := []) rfl rfl midValid midOwned
      exact ⟨result, _, t, .apply shape produce consume⟩

theorem core_conservation (typed : Types g kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (run : Exec g kind ctx root owners values s value events t) (x : Nat) :
    (released events).count x + (resultOwners kind value).count x =
      owners.count x + (allocations events).count x := by
  cases kind with
  | scalar => simpa [resultOwners] using OwnedCoreContinuation.release_conservation typed length scalarLength run x
  | owned => exact OwnedCoreResults.release_conservation typed length scalarLength run x

theorem conservation (typed : Typing g kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (run : Evaluation g kind ctx root owners values s value events t) (x : Nat) :
    (released events).count x + (resultOwners kind value).count x =
      owners.count x + (allocations events).count x := by
  induction typed generalizing owners values s value events t with
  | core typed =>
      cases run with
      | core run => exact core_conservation typed length scalarLength run x
      | apply shape _ _ => exact False.elim (shape.not_core typed)
  | apply shape producer consumer ihp ihc =>
      cases run with
      | core run => exact False.elim (shape.not_exec run)
      | apply shape' produce consume =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          have first := ihp length scalarLength produce
          have last := ihc rfl rfl consume
          simp only [resultOwners] at first
          simp only [releases_append, allocations_append, List.count_append]
          omega


theorem core_deterministic (a : Exec g kind ctx root owners values s v es t)
    (b : Exec g kind ctx root owners values s v' es' t') : v = v' ∧ es = es' ∧ t = t' := by
  cases kind with
  | scalar => exact OwnedCoreContinuation.Runs.deterministic a b
  | owned => exact OwnedCoreResults.OwnedRuns.deterministic a b

/-- Determinism holds for arbitrary executions, not just one selected typed run. -/
theorem Evaluation.deterministic
    (a : Evaluation g kind ctx root owners values s v es t)
    (b : Evaluation g kind ctx root owners values s v' es' t') : v = v' ∧ es = es' ∧ t = t' := by
  induction a generalizing v' es' t' with
  | core run =>
      cases b with
      | core other => exact core_deterministic run other
      | apply shape _ _ => exact False.elim (shape.not_exec run)
  | apply shape produce consume ihp ihc =>
      cases b with
      | core run => exact False.elim (shape.not_exec run)
      | apply shape' produce' consume' =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          obtain ⟨rfl, rfl, rfl⟩ := ihp produce'
          obtain ⟨rfl, rfl, rfl⟩ := ihc consume'
          exact ⟨rfl, rfl, rfl⟩

theorem returned_live (typed : Typing g .owned ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (run : Evaluation g .owned ctx root owners values s v es t) :
    t.live v = true ∧ Unborrowed t v := by
  have own := (execution_safe typed length scalarLength valid owned run).2.2
  exact ⟨own.live v (by simp [resultOwners]), own.leaseFree v (by simp [resultOwners])⟩

theorem returned_never_freed (typed : Typing g .owned ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (run : Evaluation g .owned ctx root owners values s v es t) : (released es).count v = 0 := by
  apply List.count_eq_zero.mpr
  intro member
  have safe := (execution_safe typed length scalarLength valid owned run).1
  have dead := released_dead valid safe (released_mem.mp member)
  have live := (returned_live typed length scalarLength valid owned run).1
  rw [live] at dead
  contradiction

theorem returned_origin (typed : Typing g .owned ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (run : Evaluation g .owned ctx root owners values s v es t) :
    v ∈ owners ∨ v ∈ allocations es := by
  have eq := conservation typed length scalarLength run v
  have zero := returned_never_freed typed length scalarLength valid owned run
  simp only [resultOwners, zero, List.count_cons, List.count_nil, beq_self_eq_true, ite_true] at eq
  by_cases h : v ∈ owners
  · exact Or.inl h
  · right
    have absent := List.count_eq_zero.mpr h
    apply List.count_pos_iff.mp
    omega

/-- Exactly the result capability may survive. No initial or newly allocated
capability may be silently discarded at a recursive call boundary. -/
theorem other_released (typed : Typing g kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (run : Evaluation g kind ctx root owners values s v es t)
    (tracked : x ∈ owners ∨ x ∈ allocations es)
    (notReturned : x ∉ resultOwners kind v) :
    (released es).count x = 1 ∧ t.live x = false := by
  have safe := (execution_safe typed length scalarLength valid owned run).1
  have eq := conservation typed length scalarLength run x
  have absent := List.count_eq_zero.mpr notReturned
  rw [absent, Nat.add_zero] at eq
  have positive : 0 < (released es).count x := by
    rcases tracked with initial | allocated
    · have := List.count_pos_iff.mpr initial; omega
    · have := List.count_pos_iff.mpr allocated; omega
  have member := List.count_pos_iff.mp positive
  have count := (releases_distinct valid safe).count (a := x)
  exact ⟨by simpa [member] using count, released_dead valid safe (released_mem.mp member)⟩

theorem no_scalar_leaks (typed : Typing g .scalar ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (run : Evaluation g .scalar ctx root owners values s v es t)
    (tracked : x ∈ owners ∨ x ∈ allocations es) :
    (released es).count x = 1 ∧ t.live x = false :=
  other_released typed length scalarLength valid owned run tracked (by simp [resultOwners])

theorem heap_accounted (typed : Typing g kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (run : Evaluation g kind ctx root owners values s v es t)
    (coverage : ∀ x, s.live x = true → x ∈ owners) :
    ∀ x, t.live x = true ↔ x ∈ resultOwners kind v := by
  intro x
  constructor
  · intro live
    by_cases h : x ∈ resultOwners kind v
    · exact h
    have safe := (execution_safe typed length scalarLength valid owned run).1
    have origin := live_origin safe live
    have tracked : x ∈ owners ∨ x ∈ allocations es := by
      rcases origin with initial | allocated
      · exact Or.inl (coverage x initial)
      · exact Or.inr allocated
    have dead := (other_released typed length scalarLength valid owned run tracked h).2
    rw [live] at dead
    contradiction
  · exact fun member => (execution_safe typed length scalarLength valid owned run).2.2.live x member

theorem core_lease_frame (run : Exec g kind ctx root owners values s v es t) :
    t.lease = s.lease := by
  cases kind with
  | scalar => exact (OwnedCoreContinuation.lease_frame run).1
  | owned => exact (OwnedCoreResults.lease_frame run).1

/-- Every recursive call preserves all ambient lease entries. -/
theorem lease_frame (run : Evaluation g kind ctx root owners values s v es t) :
    t.lease = s.lease := by
  induction run with
  | core run => exact core_lease_frame run
  | apply _ _ _ first last => exact last.trans first

theorem created_tokens_expired (valid : Valid s)
    (run : Evaluation g kind ctx root owners values s v es t)
    (newToken : s.nextLease ≤ l) : t.lease l = none := by
  rw [lease_frame run]
  cases h : s.lease l with
  | none => rfl
  | some x => have := (valid.leased l x h).1; omega

theorem Shape.head (shape : Shape g root arg body) : ∃ f, Graph.nodeAt g root = .app f arg := by
  cases shape with | intro f _ _ _ head _ _ _ => exact ⟨f, head⟩

theorem Typing.apply_inversion (typed : Typing g kind ctx n m root)
    (shape : Shape g root arg body) :
    Typing g .owned ctx n m arg ∧ Typing g kind OwnedCoreResults.consumerContext 1 0 body := by
  cases typed with
  | core typed => exact False.elim (shape.not_core typed)
  | apply other producer consumer =>
      obtain ⟨rfl, rfl⟩ := shape.unique other
      exact ⟨producer, consumer⟩

theorem Typing.owned_variable_inversion (typed : Typing g .owned ctx n m root)
    (variableShape : Graph.nodeAt g root = .var k) :
    n = 1 ∧ ownerSlot g ctx root = some 0 := by
  cases typed with
  | apply shape _ _ =>
      obtain ⟨_, head⟩ := shape.head
      have eq := variableShape.symm.trans head; contradiction
  | core typed =>
      cases typed with
      | returnOwner resolved => exact ⟨rfl, resolved⟩
      | free head _ _ _ => have eq := variableShape.symm.trans head; contradiction
      | allocate shape _ _ =>
          obtain ⟨_, _, head⟩ := shape.application
          have eq := variableShape.symm.trans head; contradiction
      | lend shape _ _ _ _ =>
          obtain ⟨_, _, head⟩ := shape.head
          have eq := variableShape.symm.trans head; contradiction
      | scalarLend shape _ _ _ _ =>
          obtain ⟨_, _, head⟩ := shape.head
          have eq := variableShape.symm.trans head; contradiction
      | scalarLet shape _ _ =>
          cases shape with
          | intro _ _ head _ _ => have eq := variableShape.symm.trans head; contradiction
      | ownedLet shape _ _ _ =>
          obtain ⟨_, head⟩ := shape.head
          have eq := variableShape.symm.trans head; contradiction

/-- Inverting the real App node recovers the argument's actual returned object,
not a guessed or equal-payload substitute, and binds it at parameter index zero. -/
theorem Evaluation.apply_inversion (run : Evaluation g kind ctx root owners values s value events t)
    (shape : Shape g root arg body) :
    ∃ returned before middle after,
      Evaluation g .owned ctx arg owners values s returned before middle ∧
      Evaluation g kind OwnedCoreResults.consumerContext body [returned] [] middle value after t ∧
      events = before ++ after ∧
      LinearCoreCallers.bindings (ownerView OwnedCoreResults.consumerContext) [returned] = [some returned] := by
  cases run with
  | core run => exact False.elim (shape.not_exec run)
  | apply shape' produce consume =>
      obtain ⟨rfl, rfl⟩ := shape.unique shape'
      exact ⟨_, _, _, _, produce, consume, rfl, rfl⟩

/-- A scalar-returning call releases the transferred argument identity exactly
once, even when its producer returned a fresh object with an equal payload. -/
theorem scalar_call_releases_argument (typed : Typing g .scalar ctx n m root)
    (shape : Shape g root arg body)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (run : Evaluation g .scalar ctx root owners values s value events t) :
    ∃ returned before middle after,
      Evaluation g .owned ctx arg owners values s returned before middle ∧
      Evaluation g .scalar OwnedCoreResults.consumerContext body [returned] [] middle value after t ∧
      events = before ++ after ∧ (released events).count returned = 1 ∧ t.live returned = false := by
  obtain ⟨producer, consumer⟩ := typed.apply_inversion shape
  obtain ⟨returned, before, middle, after, produce, consume, eq, _⟩ := run.apply_inversion shape
  have origin := returned_origin producer length scalarLength valid owned produce
  have tracked : returned ∈ owners ∨ returned ∈ allocations events := by
    rcases origin with initial | allocated
    · exact Or.inl initial
    · right
      rw [eq, allocations_append]
      exact List.mem_append_left _ allocated
  obtain ⟨once, dead⟩ := no_scalar_leaks typed length scalarLength valid owned run tracked
  exact ⟨returned, before, middle, after, produce, consume, eq, once, dead⟩

end Jihoo.OwnedCoreApplications
