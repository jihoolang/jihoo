import Jihoo.OwnedCoreApplications

/-! Framing derived from actual resource accounting and primitive freshness.
No assumption that an execution leaves the frame untouched is supplied. -/
namespace Jihoo.OwnedApplicationFrame
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext OwnedCoreContinuation OwnedCoreApplications

theorem step_object_mono (step : Step s e t) : s.nextObject ≤ t.nextObject := by
  cases step <;> simp

theorem allocations_fresh (run : Steps s es t) (member : x ∈ allocations es) :
    s.nextObject ≤ x := by
  induction run with
  | nil => simp [allocations] at member
  | @cons start event middle events finish step tail ih =>
      have mono := step_object_mono step
      cases step <;> simp only [allocations, List.filterMap_cons, List.mem_cons] at member
      case alloc payload =>
        rcases member with rfl | rest
        · exact Nat.le_refl _
        · have := ih rest; omega
      all_goals exact Nat.le_trans mono (ih member)

theorem live_without_release (live : s.live x = true) (run : Steps s es t)
    (absent : Event.free x ∉ es) : t.live x = true := by
  induction run with
  | nil => exact live
  | @cons start event middle events finish step tail ih =>
      have ne : event ≠ Event.free x := fun eq => absent (by simp [eq])
      have rest : Event.free x ∉ events := fun h => absent (by simp [h])
      apply ih _ rest
      cases step <;> try exact live
      case alloc value => simp [put, live]
      case free y _ _ =>
        have neq : x ≠ y := by intro eq; subst y; exact ne rfl
        simp [put, neq, live]

theorem owns_left (owned : Owns s (xs ++ ys)) : Owns s xs := by
  constructor
  · exact (List.pairwise_append.mp owned.distinct).1
  · intro x h; exact owned.live x (List.mem_append_left ys h)
  · intro x h; exact owned.leaseFree x (List.mem_append_left ys h)

theorem owns_right (owned : Owns s (xs ++ ys)) : Owns s ys := by
  constructor
  · exact (List.pairwise_append.mp owned.distinct).2.1
  · intro x h; exact owned.live x (List.mem_append_right xs h)
  · intro x h; exact owned.leaseFree x (List.mem_append_right xs h)

theorem owner_frame_separate (owned : Owns s (xs ++ frame)) (member : x ∈ frame) : x ∉ xs := by
  intro h
  exact (List.pairwise_append.mp owned.distinct).2.2 x h x member rfl

/-- Conservation and fresh allocation jointly prevent any ambient capability
from being released or returned as if it were owned by the producer. -/
theorem frame_not_accounted {results : List Nat} (valid : Valid s) (owned : Owns s (owners ++ frame))
    (run : Steps s es t)
    (account : ∀ x, (released es).count x + results.count x = owners.count x + (allocations es).count x)
    (member : x ∈ frame) : x ∉ released es ∧ x ∉ results := by
  have old := valid.allocated x ((owns_right owned).live x member)
  have absent := owner_frame_separate owned member
  have fresh : x ∉ allocations es := by
    intro h; have := allocations_fresh run h; omega
  have eq := account x
  rw [List.count_eq_zero.mpr absent, List.count_eq_zero.mpr fresh] at eq
  exact ⟨List.count_eq_zero.mp (by omega), List.count_eq_zero.mp (by omega)⟩

/-- Generic frame recombination. Safety and accounting are derived by the
caller from its typing judgment; neither disjointness nor noninterference of
its final result is assumed. -/
theorem recombine (valid : Valid s) (owned : Owns s (owners ++ frame))
    (run : Steps s es t) (resultOwned : Owns t results)
    (leases : t.lease = s.lease)
    (account : ∀ x, (released es).count x + results.count x = owners.count x + (allocations es).count x) :
    Owns t (results ++ frame) := by
  have framed := owns_right owned
  constructor
  · apply List.pairwise_append.mpr
    refine ⟨resultOwned.distinct, framed.distinct, ?_⟩
    intro x hx y hy eq
    subst y
    exact (frame_not_accounted valid owned run account hy).2 hx
  · intro x h
    rcases List.mem_append.mp h with result | ambient
    · exact resultOwned.live x result
    · exact live_without_release (framed.live x ambient) run
        (fun h => (frame_not_accounted valid owned run account ambient).1 (released_mem.mpr h))
  · intro x h
    rcases List.mem_append.mp h with result | ambient
    · exact resultOwned.leaseFree x result
    · intro l; rw [leases]; exact framed.leaseFree x ambient l

/-- Every complete typed application retains the unrelated initial inventory. -/
theorem framed_safe (typed : Typing g kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s (owners ++ frame))
    (run : Evaluation g kind ctx root owners values s value es t) :
    Steps s es t ∧ Valid t ∧ Owns t (resultOwners kind value ++ frame) := by
  obtain ⟨steps, vt, resultOwned⟩ := execution_safe typed length scalarLength valid (owns_left owned) run
  exact ⟨steps, vt, recombine valid owned steps resultOwned (lease_frame run)
    (conservation typed length scalarLength run)⟩

/-- This source fragment can allocate payloads and read them, but has no
in-place store constructor. This property is proved from its execution rules. -/
def NoWrites (es : List Event) : Prop := ∀ x v, Event.write x v ∉ es

theorem no_writes_append (a : NoWrites xs) (b : NoWrites ys) : NoWrites (xs ++ ys) := by
  intro x v h
  rcases List.mem_append.mp h with h | h
  · exact a x v h
  · exact b x v h

theorem reader_no_writes (run : Graph.CoreReads g s token owner ctx root v es) : NoWrites es := by
  induction run with
  | scalar _ => intro x v; simp
  | read _ _ _ _ => intro x v; simp
  | strict _ _ _ first last | app _ _ _ _ _ first last => exact no_writes_append first last
  | yes _ _ _ _ _ ih | no _ _ _ _ _ ih => exact ih

theorem core_no_writes (run : Exec g kind ctx root owners values s v es t) : NoWrites es := by
  induction run with
  | finish _ _ | returnOwner _ _ => intro x v; simp
  | free _ _ _ _ ih => intro x v; simpa using ih x v
  | allocate _ _ ih => intro x v; simpa using ih x v
  | lend _ _ _ reads _ ih =>
      have nr := reader_no_writes reads
      intro x v
      simp [OwnedLendTransfer.events, nr x v, ih x v]
  | scalarLend _ _ _ reads _ ih =>
      have nr := reader_no_writes reads
      intro x v
      simp [scalarEvents, nr x v, ih x v]
  | scalarLet _ _ _ ih | ownedLet _ _ _ _ ih => exact ih

theorem no_writes (run : Evaluation g kind ctx root owners values s v es t) : NoWrites es := by
  induction run with
  | core run => exact core_no_writes run
  | apply _ _ _ first last => exact no_writes_append first last

/-- A no-write execution cannot change any previously allocated payload;
new allocations use fresh identities, even when their payloads are equal. -/
theorem old_payload (old : x < s.nextObject) (run : Steps s es t) (writes : NoWrites es) :
    t.payload x = s.payload x := by
  induction run with
  | nil => rfl
  | @cons start event middle events finish step tail ih =>
      have rest : NoWrites events := by
        intro y v h; exact writes y v (by simp [h])
      have monotone := step_object_mono step
      have bound : x < middle.nextObject := by omega
      have final := ih bound rest
      apply final.trans
      cases step <;> try rfl
      case alloc v =>
        have neq : x ≠ start.nextObject := by omega
        simp [put, neq]
      case write y v _ _ => exact False.elim (writes y v (by simp))

theorem frame_payload (typed : Typing g kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s (owners ++ frame))
    (run : Evaluation g kind ctx root owners values s value es t)
    (member : x ∈ frame) : t.payload x = s.payload x := by
  have old := valid.allocated x ((owns_right owned).live x member)
  exact old_payload old (execution_safe typed length scalarLength valid (owns_left owned) run).1 (no_writes run)

end Jihoo.OwnedApplicationFrame
