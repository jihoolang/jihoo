import Jihoo.SizedBufferHeap
import Jihoo.OwnedLendTransfer

/-! Owned results of a sized read-only lender. The reader allocates a fresh
uniform buffer while its original owner's lease is active. Original and result
lengths are independent; only the read index is bounded by the original length.
The source typing judgment supplies that bound and runtime allocation length. -/
namespace Jihoo.SizedOwnedLend
open SizedBufferHeap
open LinearHeapPrograms

/-- Closing the local lease and allocating the reader result commute: the
result owns a fresh identity and retains its separately interpreted length. -/
def final (s : State) (length value : Nat) : State := allocate (restore s) length value

def events (s : State) (owner index length : Nat) : List Event :=
  [.beginLease s.heap.nextLease owner,
   .read s.heap.nextLease index (s.heap.payload owner),
   .alloc s.heap.nextObject length (s.heap.payload owner),
   .close s.heap.nextLease]

theorem allocate_close (valid : Valid s) :
    close (allocate (lend s owner) length value) s.heap.nextLease = final s length value := by
  have h := close_lend_restore (x := owner) valid
  exact congrArg (fun t => allocate t length value) h

/-- The allocation occurs before lease closure, rather than silently copying
an owner after its lifetime has ended. -/
theorem prefix_steps (valid : Valid s) (live : s.heap.live owner = true)
    (bound : index < s.length owner) :
    Steps s (events s owner index length) (final s length (s.heap.payload owner)) := by
  have lease : (lend s owner).heap.lease s.heap.nextLease = some owner := by
    simp [lend, HeapLeases.put]
  have read : Step (lend s owner)
      (.read s.heap.nextLease index (s.heap.payload owner)) (lend s owner) :=
    .read lease bound
  have shut : Step (allocate (lend s owner) length (s.heap.payload owner))
      (.close s.heap.nextLease) (final s length (s.heap.payload owner)) := by
    rw [← allocate_close (owner := owner) valid]
    exact .close (x := owner) (by simp [allocate, lend, HeapLeases.put])
  exact .cons (.beginLease live) (.cons read (.cons .alloc (.cons shut .nil)))

theorem prefix_valid (valid : Valid s) (live : s.heap.live owner = true)
    (bound : index < s.length owner) : Valid (final s length (s.heap.payload owner)) :=
  steps_valid valid (prefix_steps valid live bound)

/-- The old owner list remains live and distinct from the fresh reader result. -/
theorem transfer_owns (valid : Valid s) (owned : Owns s.heap owners) :
    Owns (final s length value).heap (s.heap.nextObject :: owners) :=
  OwnedLendTransfer.transfer_owns (v := value) valid owned

theorem fresh_original (valid : Valid s) (owned : Owns s.heap owners)
    (member : owner ∈ owners) : s.heap.nextObject ≠ owner :=
  OwnedLendTransfer.fresh_original valid owned member

theorem result_length : (final s length value).length s.heap.nextObject = length :=
  allocation_length

theorem original_length (valid : Valid s) (live : s.heap.live owner = true) :
    (final s length value).length owner = s.length owner := by
  have bound := valid.allocated owner live
  simp [final, allocate, restore, ScopedLend.restored, HeapLeases.put, Nat.ne_of_lt bound]

theorem original_live (owned : Owns s.heap owners) (member : owner ∈ owners) :
    (final s length value).heap.live owner = true :=
  OwnedLendTransfer.original_live (v := value) owned member

theorem result_payload : (final s length value).heap.payload s.heap.nextObject = value :=
  OwnedLendTransfer.result_payload (v := value)

theorem original_payload (valid : Valid s) (live : s.heap.live owner = true) :
    (final s length value).heap.payload owner = s.heap.payload owner :=
  OwnedLendTransfer.original_payload (v := value) valid live

/-- Unrelated leases are unchanged and the newly opened token is expired. -/
theorem lease_frame : (final s length value).heap.lease = s.heap.lease := rfl

theorem local_token_expired (valid : Valid s) :
    s.heap.nextLease < (final s length value).heap.nextLease ∧
    (final s length value).heap.lease s.heap.nextLease = none :=
  OwnedLendTransfer.local_token_expired (v := value) valid

theorem local_token_stays_expired (valid : Valid s)
    (run : Steps (final s length value) es t) :
    s.heap.nextLease < t.heap.nextLease ∧ t.heap.lease s.heap.nextLease = none :=
  HeapLeases.expired_steps (local_token_expired (length := length) (value := value) valid).1
    (local_token_expired (length := length) (value := value) valid).2 (steps_project run)

end Jihoo.SizedOwnedLend
