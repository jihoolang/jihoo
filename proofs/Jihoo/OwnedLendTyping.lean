import Jihoo.OwnedLendTransfer
import Jihoo.OwnedCoreContinuation

/-! Direct declarative ownership rule for an original Core Lend whose reader
allocates an owned Buffer1. This is a specified rule subset, not whole-Core
HasType or a theorem about the native checker. No accepted-callee certificate or
assumed safe execution is a premise. -/
namespace Jihoo.OwnedLendTyping
open HeapLeases ScopedLend LinearHeapPrograms

/-- Extract constructor identities without executing a reader or continuation. -/
def spine (g : ScopedLend.Graph.Graph) (root type : Nat) : Option (Nat × Nat) := do
  let .lam false domain body := ScopedLend.Graph.nodeAt g root | none
  if !ScopedLend.Graph.bufferOne g domain then none else do
  let .pi false input output := ScopedLend.Graph.nodeAt g type | none
  if !ScopedLend.Graph.bufferOne g input || ScopedLend.Graph.nodeAt g output != .i64 then none else do
  let .lend owner reader cont := ScopedLend.Graph.nodeAt g body | none
  if ScopedLend.Graph.nodeAt g owner != .var 0 then none else do
  let .lam false refTy allocation := ScopedLend.Graph.nodeAt g reader | none
  if !ScopedLend.Graph.refOne g refTy then none else do
  let .alloc length init := ScopedLend.Graph.nodeAt g allocation | none
  if ScopedLend.Graph.nodeAt g length != .natural 1 then none else do
  let .lam false resultTy inner := ScopedLend.Graph.nodeAt g cont | none
  let .lam false ownerTy rest := ScopedLend.Graph.nodeAt g inner | none
  if !ScopedLend.Graph.bufferOne g resultTy || !ScopedLend.Graph.bufferOne g ownerTy then none else
  return (init, rest)

def context : LinearCoreCallers.Context := [some 1, some 0, some 1]

structure Typed (g : ScopedLend.Graph.Graph) (root type : Nat) where
  init : Nat
  rest : Nat
  reader : Reader
  valid : ScopedLend.Graph.valid g = true
  shape : spine g root type = some (init, rest)
  reading : ScopedLend.Graph.Represents g [.borrow, .owner] init reader
  continuing : OwnedCoreContinuation.Typed g context 2 rest

/-- Operational rule retains real graph identities, reader evaluation and
continuation evaluation; ownership safety is proved from Typed separately. -/
inductive Runs (g : ScopedLend.Graph.Graph) (root type : Nat) (s : State) (x : Nat) :
    Nat → List Event → State → Prop where
  | intro : spine g root type = some (init, rest) →
      ScopedLend.Graph.CoreReads g (opened s x) s.nextLease x [.borrow, .owner] init copied reads →
      OwnedCoreContinuation.Runs g context rest [s.nextObject, x] (OwnedLendTransfer.final s copied) value suffix t →
      Runs g root type s x value (OwnedLendTransfer.events s x copied reads ++ suffix) t

theorem singleton_owns (live : s.live x = true) (free : Unborrowed s x) :
    Owns s [x] := by
  constructor
  · simp
  · intro y member; simpa using (List.mem_singleton.mp member ▸ live)
  · intro y member; simpa using (List.mem_singleton.mp member ▸ free)

theorem total (typed : Typed g root type) (valid : Valid s)
    (live : s.live x = true) (free : Unborrowed s x) :
    ∃ value events t, Runs g root type s x value events t := by
  have active : (opened s x).lease s.nextLease = some x := by simp [opened, put]
  have env : EnvValid (opened s x) [s.nextLease] := by
    intro l member
    have : l = s.nextLease := List.mem_singleton.mp member
    subst l
    exact ⟨x, active⟩
  obtain ⟨copied, reads, reading⟩ := reader_total (env := [s.nextLease]) typed.reading.scoped env
  have owned := OwnedLendTransfer.transfer_owns (v := copied) valid (singleton_owns live free)
  obtain ⟨value, suffix, t, continuation⟩ := OwnedCoreContinuation.total typed.continuing (by rfl)
    (OwnedLendTransfer.prefix_valid valid live reading) owned
  exact ⟨value, _, t, .intro typed.shape (typed.reading.execution active reading) continuation⟩

/-- Every graph execution, not just the totality witness, obeys primitive heap
semantics and preserves Valid. -/
theorem execution_safe (typed : Typed g root type) (valid : Valid s)
    (live : s.live x = true) (free : Unborrowed s x)
    (run : Runs g root type s x value events t) : Steps s events t ∧ Valid t := by
  cases run with
  | intro shape reading continuation =>
      have eq := typed.shape.symm.trans shape
      cases eq
      have reader := typed.reading.reflect reading
      have preSteps := OwnedLendTransfer.prefix_steps valid live reader
      obtain ⟨suffix, finalValid, _⟩ := OwnedCoreContinuation.execution_safe typed.continuing rfl
        (steps_valid valid preSteps) (OwnedLendTransfer.transfer_owns valid (singleton_owns live free)) continuation
      exact ⟨steps_append preSteps suffix, finalValid⟩

/-- The local borrow cannot escape: it is expired before continuation execution
and remains expired throughout any later valid primitive execution. -/
theorem token_expires (typed : Typed g root type) (valid : Valid s)
    (live : s.live x = true) (free : Unborrowed s x)
    (run : Runs g root type s x value events t) :
    s.nextLease < t.nextLease ∧ t.lease s.nextLease = none := by
  cases run with
  | intro shape reading continuation =>
      have eq := typed.shape.symm.trans shape
      cases eq
      have reader := typed.reading.reflect reading
      have suffix := (OwnedCoreContinuation.execution_safe typed.continuing rfl
        (OwnedLendTransfer.prefix_valid valid live reader) (OwnedLendTransfer.transfer_owns valid (singleton_owns live free)) continuation).1
      exact OwnedLendTransfer.local_token_stays_expired valid suffix

theorem owner_released_once (typed : Typed g root type) (valid : Valid s)
    (live : s.live x = true) (free : Unborrowed s x)
    (run : Runs g root type s x value es t) (member : y ∈ [s.nextObject, x]) :
    (released es).count y = 1 ∧ t.live y = false := by
  cases run with
  | intro shape reading continuation =>
      have eq := typed.shape.symm.trans shape
      cases eq
      have reader := typed.reading.reflect reading
      obtain ⟨count, dead⟩ := OwnedCoreContinuation.no_tracked_leaks typed.continuing rfl
        (OwnedLendTransfer.prefix_valid valid live reader)
        (OwnedLendTransfer.transfer_owns valid (singleton_owns live free)) continuation
        (Or.inl member)
      have noReadFree := reader_releases reader
      simp only [released] at noReadFree
      exact ⟨by simpa [OwnedLendTransfer.events, released, List.filterMap_append,
        noReadFree] using count, dead⟩

/-- Both aliases to the original refer to one capability; the returned buffer
has a distinct capability. Each is released exactly once in the complete run. -/
theorem two_owners_released (typed : Typed g root type) (valid : Valid s)
    (live : s.live x = true) (free : Unborrowed s x)
    (run : Runs g root type s x value es t) :
    s.nextObject ≠ x ∧ (released es).count x = 1 ∧
    (released es).count s.nextObject = 1 ∧ t.live x = false ∧ t.live s.nextObject = false := by
  obtain ⟨oldCount, oldDead⟩ := owner_released_once typed valid live free run (by simp : x ∈ [s.nextObject, x])
  obtain ⟨newCount, newDead⟩ := owner_released_once typed valid live free run (by simp : s.nextObject ∈ [s.nextObject, x])
  exact ⟨OwnedLendTransfer.fresh_original valid (singleton_owns live free) (by simp),
    oldCount, newCount, oldDead, newDead⟩

theorem lease_frame (run : Runs g root type s x value es t) :
    t.lease = s.lease ∧ t.nextLease = s.nextLease + 1 := by
  cases run with
  | intro _ _ continuation => exact OwnedCoreContinuation.lease_frame continuation

/-- Full final heap emptiness requires that the original owner accounts for all
initial live objects. Without this premise ambient objects are preserved, not
incorrectly declared leaks of this call. -/
theorem heap_empty (typed : Typed g root type) (valid : Valid s)
    (live : s.live x = true) (free : Unborrowed s x)
    (run : Runs g root type s x value es t)
    (coverage : ∀ y, s.live y = true → y = x) : ∀ y, t.live y = false := by
  cases run with
  | intro shape reading continuation =>
      have eq := typed.shape.symm.trans shape
      cases eq
      have reader := typed.reading.reflect reading
      apply OwnedCoreContinuation.heap_empty typed.continuing rfl
        (OwnedLendTransfer.prefix_valid valid live reader)
        (OwnedLendTransfer.transfer_owns valid (singleton_owns live free)) continuation
      intro y alive
      by_cases fresh : y = s.nextObject
      · simp [fresh]
      · have oldLive : s.live y = true := by
          simpa [OwnedLendTransfer.final, allocatedState, restored, put, fresh] using alive
        simp [coverage y oldLive]

end Jihoo.OwnedLendTyping
