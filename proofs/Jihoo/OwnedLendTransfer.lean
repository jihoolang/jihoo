import Jihoo.LinearHeapPrograms

/-! Effectful reader prefix for an owned Buffer1 result. Existing scoped reader
semantics supplies the scalar; allocation occurs while the original lease is
active. Only the lexical lender closes its freshly created token. No source
admission, arbitrary safe trace, or native allocator correspondence is assumed. -/
namespace Jihoo.OwnedLendTransfer
open HeapLeases ScopedLend LinearHeapPrograms

def final (s : State) (v : Nat) : State := allocatedState (restored s) v

def events (s : State) (x v : Nat) (reads : List Event) : List Event :=
  .beginLease s.nextLease x :: (reads ++ [.alloc s.nextObject v, .close s.nextLease])

theorem allocate_close (valid : Valid s) :
    { allocatedState (opened s x) v with
      lease := put (allocatedState (opened s x) v).lease s.nextLease none } = final s v := by
  have h := close_restores (x := x) valid
  have he := congrArg (fun t => allocatedState t v) h
  exact he

theorem prefix_steps (valid : Valid s) (live : s.live x = true)
    (read : Reads (opened s x) [s.nextLease] r v es) :
    Steps s (events s x v es) (final s v) := by
  apply Steps.cons (Step.beginLease live)
  apply steps_append (reader_steps read)
  apply Steps.cons Step.alloc
  have close : Step (allocatedState (opened s x) v) (.close s.nextLease) (final s v) := by
    rw [← allocate_close (x := x) (v := v) valid]
    exact Step.close (x := x) (by simp [allocatedState, opened, put])
  exact Steps.cons close Steps.nil

theorem prefix_valid (valid : Valid s) (live : s.live x = true)
    (read : Reads (opened s x) [s.nextLease] r v es) : Valid (final s v) :=
  steps_valid valid (prefix_steps valid live read)

theorem restored_valid (valid : Valid s) : Valid (restored s) := by
  constructor
  · exact valid.allocated
  · intro l x h
    obtain ⟨bound, live⟩ := valid.leased l x h
    exact ⟨by dsimp [restored]; omega, live⟩

theorem transfer_owns (valid : Valid s) (owned : Owns s owners) :
    Owns (final s v) (s.nextObject :: owners) := by
  have restoredOwned : Owns (restored s) owners :=
    ⟨owned.distinct, owned.live, owned.leaseFree⟩
  exact allocate_owns (restored_valid valid) restoredOwned

theorem fresh_original (valid : Valid s) (owned : Owns s owners) (member : x ∈ owners) :
    s.nextObject ≠ x := by
  have := valid.allocated x (owned.live x member)
  omega

theorem original_live (owned : Owns s owners) (member : x ∈ owners) :
    (final s v).live x = true := by
  simp [final, allocatedState, restored, put, owned.live x member]

theorem original_payload (valid : Valid s) (live : s.live x = true) :
    (final s v).payload x = s.payload x := by
  have bound := valid.allocated x live
  simp [final, allocatedState, restored, put, Nat.ne_of_lt bound]

theorem result_payload : (final s v).payload s.nextObject = v := by
  simp [final, allocatedState, restored, put]

theorem copied_read_value (read : Reads (opened s x) [s.nextLease] (.read 0) v es) :
    v = s.payload x := by
  obtain ⟨l, y, slot, lease, value⟩ := read_observation read
  simp only [List.getElem?_cons_zero, Option.some.injEq] at slot
  subst l
  simp [opened, put] at lease
  subst y
  exact value

theorem copied_read_payload
    (read : Reads (opened s x) [s.nextLease] (.read 0) v es) :
    (final s v).payload s.nextObject = s.payload x := by
  rw [result_payload, copied_read_value read]

/-- All preexisting leases, including unrelated lenders, are unchanged. -/
theorem lease_frame : (final s v).lease = s.lease := rfl

theorem local_token_expired (valid : Valid s) :
    s.nextLease < (final s v).nextLease ∧ (final s v).lease s.nextLease = none := by
  exact ⟨Nat.lt_succ_self _, lease_fresh valid⟩

theorem local_token_stays_expired (valid : Valid s) (run : Steps (final s v) es t) :
    s.nextLease < t.nextLease ∧ t.lease s.nextLease = none :=
  expired_steps (local_token_expired valid).1 (local_token_expired valid).2 run

end Jihoo.OwnedLendTransfer
