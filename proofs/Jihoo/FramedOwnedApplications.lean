import Jihoo.OwnedCallContext
import Jihoo.OwnedApplicationFrame

/-! Unified continuation closure and explicit resource-partition plans for recursive actual Core applications.
The plan is an input to typing and execution, not a claim about the native
checker generating it. Determinism is for one fixed plan, not across arbitrary
partitions. Scalar capture and retained owner frames preserve lexical indices.
Supported Free, Alloc, mixed Lend, scalar-let and owned-let continuations may
contain recursive calls directly. Readers remain the existing restricted
reader grammar: calls in Lend continuations run after the lease is closed.
This remains direct Buffer1 application, not general dependent substitution. -/
namespace Jihoo.FramedOwnedApplications
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext OwnedCoreContinuation
open OwnedCoreApplications

inductive Plan where
  | core
  | apply (limit : Nat) (argument body : Plan)
  | free (rest : Plan)
  | allocate (rest : Plan)
  | lend (rest : Plan)
  | scalarLend (rest : Plan)
  | scalarLet (rest : Plan)
  | ownedLet (rest : Plan)
  deriving DecidableEq, Repr

inductive Typing (g : Graph.Graph) : Plan → ResultKind → Context → Nat → Nat → Nat → Prop where
  | core : Types g kind ctx n m root → Typing g .core kind ctx n m root
  | apply : Shape g root argument body → p ≤ n →
      Typing g argumentPlan .owned (OwnedCallContext.producer ctx p) p m argument →
      Typing g bodyPlan kind (OwnedCallContext.body ctx p) (n-p+1) m body →
      Typing g (.apply p argumentPlan bodyPlan) kind ctx n m root

  | free : Graph.nodeAt g root = .free owner body → ownerSlot g ctx owner = some slot →
      slot < n → Typing g restPlan kind (consumed slot ctx) (n-1) m body →
      Typing g (.free restPlan) kind ctx n m root
  | allocate : Allocation g root value body → value < 2^63 →
      Typing g restPlan kind (fresh ctx) (n+1) m body →
      Typing g (.allocate restPlan) kind ctx n m root
  | lend : OwnedLendContext.Shape g root owner init body → ownerSlot g ctx owner = some slot → slot < n →
      Graph.Represents g (readerRoles ctx slot) init reader →
      Typing g restPlan kind (ownedReturned ctx slot) (n+1) m body →
      Typing g (.lend restPlan) kind ctx n m root
  | scalarLend : ScalarShape g root owner init body → ownerSlot g ctx owner = some slot → slot < n →
      Graph.Represents g (readerRoles ctx slot) init reader →
      Typing g restPlan kind (scalarReturned ctx slot) n (m+1) body →
      Typing g (.scalarLend restPlan) kind ctx n m root
  | scalarLet : PureOwnedScalar.Shape g root arg body →
      PureOwnedScalar.Represents g ctx m arg raw →
      Typing g restPlan kind (PureOwnedScalar.bindScalar ctx) n (m+1) body →
      Typing g (.scalarLet restPlan) kind ctx n m root
  | ownedLet : OwnedArgumentBinding.Shape g root argument body →
      ownerSlot g ctx argument = some slot → slot < n →
      Typing g restPlan kind (OwnedArgumentBinding.transferred ctx slot) n m body →
      Typing g (.ownedLet restPlan) kind ctx n m root

inductive Evaluation (g : Graph.Graph) : Plan → ResultKind → Context → Nat → List Nat → List Nat → State → Nat → List Event → State → Prop where
  | core : Exec g kind ctx root owners values s value events t →
      Evaluation g .core kind ctx root owners values s value events t
  | apply : Shape g root argument body →
      Evaluation g argumentPlan .owned (OwnedCallContext.producer ctx p) argument (owners.take p) values s returned before middle →
      Evaluation g bodyPlan kind (OwnedCallContext.body ctx p) body (returned :: owners.drop p) values middle value after t →
      Evaluation g (.apply p argumentPlan bodyPlan) kind ctx root owners values s value (before ++ after) t

  | free : Graph.nodeAt g root = .free owner body → ownerSlot g ctx owner = some slot →
      Select owners slot x rest →
      Evaluation g restPlan kind (consumed slot ctx) body rest values (freedState s x) value events t →
      Evaluation g (.free restPlan) kind ctx root owners values s value (.free x :: events) t
  | allocate : Allocation g root payload body →
      Evaluation g restPlan kind (fresh ctx) body (s.nextObject :: owners) values (allocatedState s payload) value events t →
      Evaluation g (.allocate restPlan) kind ctx root owners values s value (.alloc s.nextObject payload :: events) t
  | lend : OwnedLendContext.Shape g root owner init body → ownerSlot g ctx owner = some slot →
      Select owners slot x rest →
      Graph.CoreReads g (opened s x) s.nextLease x (readerRoles ctx slot) init copied reads →
      Evaluation g restPlan kind (ownedReturned ctx slot) body (s.nextObject :: owners) values
        (OwnedLendTransfer.final s copied) value suffix t →
      Evaluation g (.lend restPlan) kind ctx root owners values s value (OwnedLendTransfer.events s x copied reads ++ suffix) t
  | scalarLend : ScalarShape g root owner init body → ownerSlot g ctx owner = some slot →
      Select owners slot x rest →
      Graph.CoreReads g (opened s x) s.nextLease x (readerRoles ctx slot) init copied reads →
      Evaluation g restPlan kind (scalarReturned ctx slot) body owners (copied :: values)
        (restored s) value suffix t →
      Evaluation g (.scalarLend restPlan) kind ctx root owners values s value (scalarEvents s x reads ++ suffix) t
  | scalarLet : PureOwnedScalar.Shape g root arg body →
      PureOwnedScalar.Eval g ctx arg values computed →
      Evaluation g restPlan kind (PureOwnedScalar.bindScalar ctx) body owners (computed :: values) s value events t →
      Evaluation g (.scalarLet restPlan) kind ctx root owners values s value events t
  | ownedLet : OwnedArgumentBinding.Shape g root argument body →
      ownerSlot g ctx argument = some slot → Select owners slot x rest →
      Evaluation g restPlan kind (OwnedArgumentBinding.transferred ctx slot) body owners values s value events t →
      Evaluation g (.ownedLet restPlan) kind ctx root owners values s value events t

theorem Evaluation.deterministic
    (a : Evaluation g plan kind ctx root owners values s v es t)
    (b : Evaluation g plan kind ctx root owners values s v' es' t') :
    v = v' ∧ es = es' ∧ t = t' := by
  induction a generalizing v' es' t' with
  | core run =>
      cases b with
      | core other => exact OwnedCoreApplications.core_deterministic run other
  | apply shape produce consume ihp ihc =>
      cases b with
      | apply shape' produce' consume' =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          obtain ⟨rfl, rfl, rfl⟩ := ihp produce'
          obtain ⟨rfl, rfl, rfl⟩ := ihc consume'
          exact ⟨rfl, rfl, rfl⟩

  | free shape resolved selected restRun ih =>
      cases b with
      | free other resolved' selected' restRun' =>
          have eq := shape.symm.trans other; cases eq
          have eq := resolved.symm.trans resolved'; cases eq
          obtain ⟨rfl, rfl⟩ := LeaseErasure.select_deterministic selected selected'
          obtain ⟨rfl, rfl, rfl⟩ := ih restRun'
          exact ⟨rfl, rfl, rfl⟩

  | allocate a restRun ih =>
      cases b with
      | allocate a' restRun' =>
          obtain ⟨rfl, rfl⟩ := a.unique a'
          obtain ⟨rfl, rfl, rfl⟩ := ih restRun'
          exact ⟨rfl, rfl, rfl⟩

  | lend shape resolved selected read suffix ih =>
      cases b with
      | lend shape' resolved' selected' read' suffix' =>
          obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          obtain ⟨rfl, rfl⟩ := LeaseErasure.select_deterministic selected selected'
          obtain ⟨rfl, rfl⟩ := core_reads_deterministic read read'
          obtain ⟨rfl, rfl, rfl⟩ := ih suffix'
          exact ⟨rfl, rfl, rfl⟩

  | scalarLend shape resolved selected read suffix ih =>
      cases b with
      | scalarLend shape' resolved' selected' read' suffix' =>
          obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          obtain ⟨rfl, rfl⟩ := LeaseErasure.select_deterministic selected selected'
          obtain ⟨rfl, rfl⟩ := core_reads_deterministic read read'
          obtain ⟨rfl, rfl, rfl⟩ := ih suffix'
          exact ⟨rfl, rfl, rfl⟩

  | scalarLet shape evaluated suffix ih =>
      cases b with
      | scalarLet shape' evaluated' suffix' =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          have eq := PureOwnedScalar.Eval.deterministic evaluated evaluated'
          subst eq
          exact ih suffix'

  | ownedLet shape resolved selected suffix ih =>
      cases b with
      | ownedLet shape' resolved' selected' suffix' =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          exact ih suffix'


/-- The returned capability is live and unborrowed, not a leaked or freed alias. -/

theorem conservation (typed : Typing g plan kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (run : Evaluation g plan kind ctx root owners values s value events t) (x : Nat) :
    (released events).count x + (resultOwners kind value).count x =
      owners.count x + (allocations events).count x := by
  induction typed generalizing owners values s value events t with
  | core typed =>
      cases run with
      | core run => exact core_conservation typed length scalarLength run x
  | @apply root argument body p n argumentPlan ctx m bodyPlan kind shape bound producer consumer ihp ihc =>
      cases run with
      | apply shape' produce consume =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          have first := ihp (by simp [List.length_take, length, Nat.min_eq_left bound]) scalarLength produce
          have last := ihc (by simp [List.length_drop, length]) scalarLength consume
          have count : owners.count x = (owners.take p).count x + (owners.drop p).count x := by
            rw [← List.count_append, List.take_append_drop]
          simp only [resultOwners, List.count_cons, List.count_nil] at first
          simp only [List.count_cons] at last
          simp only [releases_append, allocations_append, List.count_append]
          omega

  | free shape resolved bound typed ih =>
      cases run with
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
      | allocate a' restRun =>
          obtain ⟨rfl, rfl⟩ := a.unique a'
          have hr := ih (by simp [length]) scalarLength restRun
          simp only [released, allocations, List.filterMap_cons, List.count_cons] at *
          omega

  | lend shape resolved bound reading typed ih =>
      cases run with
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

  | scalarLet shape represented typed ih =>
      cases run with
      | scalarLet shape' evaluated suffix =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          exact ih length (by simp [scalarLength]) suffix

  | ownedLet shape resolved bound typed ih =>
      cases run with
      | ownedLet shape' resolved' selected suffix =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          exact ih length scalarLength suffix

theorem lease_frame (run : Evaluation g plan kind ctx root owners values s v es t) :
    t.lease = s.lease := by
  induction run with
  | core run => exact core_lease_frame run
  | apply _ _ _ first last => exact last.trans first

  | free _ _ _ _ ih => exact ih
  | allocate _ _ ih => exact ih
  | lend _ _ _ _ _ ih => exact ih
  | scalarLend _ _ _ _ _ ih => exact ih
  | scalarLet _ _ _ ih => exact ih
  | ownedLet _ _ _ _ ih => exact ih

theorem created_tokens_expired (valid : Valid s)
    (run : Evaluation g plan kind ctx root owners values s v es t)
    (newToken : s.nextLease ≤ l) : t.lease l = none := by
  rw [lease_frame run]
  cases h : s.lease l with
  | none => rfl
  | some x => have := (valid.leased l x h).1; omega


theorem owns_take (owned : Owns s owners) : Owns s (owners.take p) := by
  refine ⟨owned.distinct.take, ?_, ?_⟩
  · intro x member
    exact owned.live x (List.mem_of_mem_take member)
  · intro x member
    exact owned.leaseFree x (List.mem_of_mem_take member)

theorem execution_safe (typed : Typing g plan kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (run : Evaluation g plan kind ctx root owners values s value events t) :
    Steps s events t ∧ Valid t ∧ Owns t (resultOwners kind value) := by
  induction typed generalizing owners values s value events t with
  | core typed =>
      cases run with
      | core run => exact core_safe typed length scalarLength valid owned run
  | @apply root argument body p n argumentPlan ctx m bodyPlan kind shape bound producer consumer ihp ihc =>
      cases run with
      | apply shape' produce consume =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          have prefixLength : (owners.take p).length = p := by simp [List.length_take, length, Nat.min_eq_left bound]
          obtain ⟨before, midValid, midOwned⟩ := ihp prefixLength scalarLength valid (owns_take owned) produce
          have fullOwned : Owns s (owners.take p ++ owners.drop p) := by simpa using owned
          have account := conservation producer prefixLength scalarLength produce
          have combined := OwnedApplicationFrame.recombine valid fullOwned before midOwned (lease_frame produce) account
          obtain ⟨after, finalValid, finalOwned⟩ := ihc (by simp [resultOwners, List.length_drop, length]) scalarLength midValid combined consume
          exact ⟨steps_append before after, finalValid, finalOwned⟩

  | free shape resolved bound typed ih =>
      cases run with
      | free other resolved' selected restRun =>
          have eq := shape.symm.trans other; cases eq
          have eq := resolved.symm.trans resolved'; cases eq
          have step := Step.free (owned.live _ selected.member) (owned.leaseFree _ selected.member)
          obtain ⟨steps, vt, ot⟩ := ih (by have := selected.length; omega) scalarLength
            (step_valid valid step) (free_owns owned selected) restRun
          exact ⟨.cons step steps, vt, ot⟩

  | allocate a bound typed ih =>
      cases run with
      | allocate a' restRun =>
          obtain ⟨rfl, rfl⟩ := a.unique a'
          obtain ⟨steps, vt, ot⟩ := ih (by simp [length]) scalarLength
            (step_valid valid (Step.alloc (value := _))) (allocate_owns valid owned) restRun
          exact ⟨.cons .alloc steps, vt, ot⟩

  | lend shape resolved bound reading typed ih =>
      cases run with
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
      | scalarLend shape' resolved' selected read suffix =>
          obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          have reader := reading.reflect read
          have pre := scalar_steps valid (owned.live _ selected.member) reader
          obtain ⟨steps, vt, ot⟩ := ih length (by simp [scalarLength]) (steps_valid valid pre)
            (restored_owns owned) suffix
          exact ⟨steps_append pre steps, vt, ot⟩

  | scalarLet shape represented typed ih =>
      cases run with
      | scalarLet shape' evaluated suffix =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          exact ih length (by simp [scalarLength]) valid owned suffix

  | ownedLet shape resolved bound typed ih =>
      cases run with
      | ownedLet shape' resolved' selected suffix =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          exact ih length scalarLength valid owned suffix

theorem total (typed : Typing g plan kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) :
    ∃ value events t, Evaluation g plan kind ctx root owners values s value events t := by
  induction typed generalizing owners values s with
  | core typed =>
      obtain ⟨v, es, t, run⟩ := core_total typed length scalarLength valid owned
      exact ⟨v, es, t, .core run⟩
  | @apply root argument body p n argumentPlan ctx m bodyPlan kind shape bound producer consumer ihp ihc =>
      have prefixLength : (owners.take p).length = p := by simp [List.length_take, length, Nat.min_eq_left bound]
      obtain ⟨v, es, middle, produce⟩ := ihp prefixLength scalarLength valid (owns_take owned)
      obtain ⟨before, midValid, midOwned⟩ := execution_safe producer prefixLength scalarLength valid (owns_take owned) produce
      have fullOwned : Owns s (owners.take p ++ owners.drop p) := by simpa using owned
      have account := conservation producer prefixLength scalarLength produce
      have combined := OwnedApplicationFrame.recombine valid fullOwned before midOwned (lease_frame produce) account
      obtain ⟨value, after, t, consume⟩ := ihc (owners := v :: owners.drop p) (values := values)
        (by simp [List.length_drop, length]) scalarLength midValid combined
      exact ⟨value, _, t, .apply shape produce consume⟩


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

theorem no_writes (run : Evaluation g plan kind ctx root owners values s v es t) :
    OwnedApplicationFrame.NoWrites es := by
  induction run with
  | core run => exact OwnedApplicationFrame.core_no_writes run
  | apply _ _ _ first last => exact OwnedApplicationFrame.no_writes_append first last

  | free _ _ _ _ ih => intro x v; simpa using ih x v
  | allocate _ _ ih => intro x v; simpa using ih x v
  | lend _ _ _ reads _ ih =>
      have nr := OwnedApplicationFrame.reader_no_writes reads
      intro x v
      simp [OwnedLendTransfer.events, nr x v, ih x v]
  | scalarLend _ _ _ reads _ ih =>
      have nr := OwnedApplicationFrame.reader_no_writes reads
      intro x v
      simp [scalarEvents, nr x v, ih x v]
  | scalarLet _ _ _ ih | ownedLet _ _ _ _ ih => exact ih

theorem apply_bound (typed : Typing g (.apply p a b) kind ctx n m root) : p ≤ n := by
  cases typed with | apply _ bound _ _ => exact bound

theorem invalid_split_rejected (bound : n < p) :
    ¬ Typing g (.apply p a b) kind ctx n m root := by
  intro typed
  have := apply_bound typed
  omega

theorem Typing.apply_inversion (typed : Typing g (.apply p a b) kind ctx n m root)
    (shape : Shape g root arg body) :
    p ≤ n ∧ Typing g a .owned (OwnedCallContext.producer ctx p) p m arg ∧
      Typing g b kind (OwnedCallContext.body ctx p) (n-p+1) m body := by
  cases typed with
  | apply other bound producer consumer =>
      obtain ⟨rfl, rfl⟩ := shape.unique other
      exact ⟨bound, producer, consumer⟩

theorem Evaluation.apply_inversion (run : Evaluation g (.apply p a b) kind ctx root owners values s value events t)
    (shape : Shape g root arg body) :
    ∃ returned before middle after,
      Evaluation g a .owned (OwnedCallContext.producer ctx p) arg (owners.take p) values s returned before middle ∧
      Evaluation g b kind (OwnedCallContext.body ctx p) body (returned :: owners.drop p) values middle value after t ∧
      events = before ++ after := by
  cases run with
  | apply shape' produce consume =>
      obtain ⟨rfl, rfl⟩ := shape.unique shape'
      exact ⟨_, _, _, _, produce, consume, rfl⟩

/-- Safety of the precise boundary extracted from an actual App: every retained
object keeps its payload and live authority, and cannot be the returned object. -/
theorem application_boundary (typed : Typing g (.apply p a b) kind ctx n m root)
    (shape : Shape g root arg body)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (run : Evaluation g (.apply p a b) kind ctx root owners values s value events t) :
    ∃ returned before middle after,
      Evaluation g a .owned (OwnedCallContext.producer ctx p) arg (owners.take p) values s returned before middle ∧
      Evaluation g b kind (OwnedCallContext.body ctx p) body (returned :: owners.drop p) values middle value after t ∧
      events = before ++ after ∧ Owns middle (returned :: owners.drop p) ∧
      (∀ x ∈ owners.drop p, x ≠ returned ∧ x ∉ released before ∧ middle.payload x = s.payload x) := by
  obtain ⟨bound, producer, consumer⟩ := typed.apply_inversion shape
  obtain ⟨returned, before, middle, after, produce, consume, eq⟩ := run.apply_inversion shape
  have prefixLength : (owners.take p).length = p := by simp [List.length_take, length, Nat.min_eq_left bound]
  obtain ⟨steps, midValid, midOwned⟩ := execution_safe producer prefixLength scalarLength valid (owns_take owned) produce
  have combinedOwned : Owns s (owners.take p ++ owners.drop p) := by simpa using owned
  have account := conservation producer prefixLength scalarLength produce
  have combined := OwnedApplicationFrame.recombine valid combinedOwned steps midOwned (lease_frame produce) account
  refine ⟨returned, before, middle, after, produce, consume, eq, combined, ?_⟩
  intro x member
  have absent := OwnedApplicationFrame.frame_not_accounted valid combinedOwned steps account member
  have old := valid.allocated x ((OwnedApplicationFrame.owns_right combinedOwned).live x member)
  exact ⟨by simpa [resultOwners] using absent.2, absent.1,
    OwnedApplicationFrame.old_payload old steps (no_writes produce)⟩

theorem returned_live (typed : Typing g plan .owned ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (run : Evaluation g plan .owned ctx root owners values s v es t) :
    t.live v = true ∧ Unborrowed t v := by
  have own := (execution_safe typed length scalarLength valid owned run).2.2
  exact ⟨own.live v (by simp [resultOwners]), own.leaseFree v (by simp [resultOwners])⟩

theorem returned_never_freed (typed : Typing g plan .owned ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (run : Evaluation g plan .owned ctx root owners values s v es t) : (released es).count v = 0 := by
  apply List.count_eq_zero.mpr
  intro member
  have safe := (execution_safe typed length scalarLength valid owned run).1
  have dead := released_dead valid safe (released_mem.mp member)
  have live := (returned_live typed length scalarLength valid owned run).1
  rw [live] at dead
  contradiction

theorem returned_origin (typed : Typing g plan .owned ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (run : Evaluation g plan .owned ctx root owners values s v es t) :
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
theorem other_released (typed : Typing g plan kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (run : Evaluation g plan kind ctx root owners values s v es t)
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

theorem no_scalar_leaks (typed : Typing g plan .scalar ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (run : Evaluation g plan .scalar ctx root owners values s v es t)
    (tracked : x ∈ owners ∨ x ∈ allocations es) :
    (released es).count x = 1 ∧ t.live x = false :=
  other_released typed length scalarLength valid owned run tracked (by simp [resultOwners])

theorem heap_accounted (typed : Typing g plan kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (run : Evaluation g plan kind ctx root owners values s v es t)
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


/-- A whole closed constructor/call composition executes from the empty heap.
Its final live heap consists exactly of its owned result (or is empty for a
scalar result). Successful execution and untouched frames are not premises. -/
theorem closed_total_accounted (typed : Typing g plan kind [] 0 0 root) :
    ∃ value events t,
      Evaluation g plan kind [] root [] [] empty value events t ∧
      Steps empty events t ∧ Valid t ∧
      (∀ x, t.live x = true ↔ x ∈ resultOwners kind value) := by
  obtain ⟨value, events, t, run⟩ := total (owners := []) (values := []) typed rfl rfl empty_valid empty_owns
  obtain ⟨steps, valid, _⟩ := execution_safe typed rfl rfl empty_valid empty_owns run
  have accounted := heap_accounted typed rfl rfl empty_valid empty_owns run (by simp [empty])
  exact ⟨value, events, t, run, steps, valid, accounted⟩

/-- Every completed scalar execution of such a closed program releases every
allocated object once, independently of the particular evaluation derivation. -/
theorem closed_scalar_release (typed : Typing g plan .scalar [] 0 0 root)
    (run : Evaluation g plan .scalar [] root [] [] empty value events t)
    (allocated : x ∈ allocations events) :
    (released events).count x = 1 ∧ t.live x = false :=
  no_scalar_leaks typed rfl rfl empty_valid empty_owns run (Or.inr allocated)

end Jihoo.FramedOwnedApplications
