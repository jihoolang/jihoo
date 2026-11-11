import Jihoo.HeapLeases
import Jihoo.LinearHeapPrograms

/-! Length-indexed, uniform-fill, read-only buffers. The payload is a fill value,
not a vector: this module deliberately has no Store/write event. The lifecycle
projection reuses the established heap identity and lease semantics. -/
namespace Jihoo.SizedBufferHeap
open HeapLeases

structure SizedState where
  heap : HeapLeases.State
  length : Nat → Nat

abbrev State := SizedState

def empty : State := ⟨HeapLeases.empty, fun _ => 0⟩
abbrev Valid (s : State) : Prop := HeapLeases.Valid s.heap

inductive Event where
  | alloc (object length fill : Nat)
  | free (object : Nat)
  | beginLease (token object : Nat)
  | close (token : Nat)
  | read (token index value : Nat)
  deriving DecidableEq, Repr

def Event.project : Event → HeapLeases.Event
  | .alloc x _ v => .alloc x v
  | .free x => .free x
  | .beginLease l x => .beginLease l x
  | .close l => .close l
  | .read l _ v => .read l v

def allocate (s : State) (n v : Nat) : State :=
  ⟨{ s.heap with nextObject := s.heap.nextObject + 1, live := put s.heap.live s.heap.nextObject true, payload := put s.heap.payload s.heap.nextObject v },
   put s.length s.heap.nextObject n⟩

def release (s : State) (x : Nat) : State :=
  ⟨{ s.heap with live := put s.heap.live x false }, s.length⟩
def lend (s : State) (x : Nat) : State :=
  ⟨{ s.heap with nextLease := s.heap.nextLease + 1, lease := put s.heap.lease s.heap.nextLease (some x) }, s.length⟩
def close (s : State) (l : Nat) : State :=
  ⟨{ s.heap with lease := put s.heap.lease l none }, s.length⟩

inductive Step : State → Event → State → Prop where
  | alloc : Step s (.alloc s.heap.nextObject n v) (allocate s n v)
  | free : s.heap.live x = true → Unborrowed s.heap x →
      Step s (.free x) (release s x)
  | beginLease : s.heap.live x = true →
      Step s (.beginLease s.heap.nextLease x) (lend s x)
  | close : s.heap.lease l = some x → Step s (.close l) (close s l)
  | read : s.heap.lease l = some x → i < s.length x →
      Step s (.read l i (s.heap.payload x)) s

inductive Steps : State → List Event → State → Prop where
  | nil : Steps s [] s
  | cons : Step s e t → Steps t es u → Steps s (e :: es) u

theorem step_project (run : Step s e t) : HeapLeases.Step s.heap e.project t.heap := by
  cases run with
  | alloc => exact .alloc
  | free live unborrowed => exact .free live unborrowed
  | beginLease live => exact .beginLease live
  | close present => exact .close present
  | read present _ => exact .read present

theorem steps_project (run : Steps s es t) :
    HeapLeases.Steps s.heap (es.map Event.project) t.heap := by
  induction run with
  | nil => exact .nil
  | cons step _ ih => exact .cons (step_project step) ih

theorem empty_valid : Valid empty := HeapLeases.empty_valid

theorem step_valid (valid : Valid s) (run : Step s e t) : Valid t :=
  HeapLeases.step_valid valid (step_project run)

theorem steps_valid (valid : Valid s) (run : Steps s es t) : Valid t :=
  HeapLeases.steps_valid valid (steps_project run)

/-- Every successful read has a live leased object and an in-bounds index. -/
theorem read_bound (valid : Valid s) (run : Step s (.read l i v) t) :
    ∃ x, s.heap.lease l = some x ∧ s.heap.live x = true ∧
      i < s.length x ∧ v = s.heap.payload x := by
  cases run with
  | read present bound => exact ⟨_, present, (valid.leased _ _ present).2, bound, rfl⟩

/-- Zero-length buffers can be allocated and freed but never read. -/
theorem zero_unreadable (present : s.heap.lease l = some x) (zero : s.length x = 0) :
    ¬ Step s (.read l i v) t := by
  intro run
  cases run with
  | read other bound =>
    have eq : _ = x := Option.some.inj (other.symm.trans present)
    subst eq
    omega

theorem allocation_fresh (valid : Valid s) : s.heap.live s.heap.nextObject = false :=
  HeapLeases.allocation_fresh valid

theorem allocation_length : (allocate s n v).length s.heap.nextObject = n := by
  simp [allocate, put]

theorem release_length : (release s x).length = s.length := rfl
theorem lend_length : (lend s x).length = s.length := rfl
theorem close_length : (close s l).length = s.length := rfl

/-- Lengths of allocated identities never change, even after Free. -/
theorem length_preserved (old : x < s.heap.nextObject) (run : Step s e t) :
    x < t.heap.nextObject ∧ t.length x = s.length x := by
  cases run <;> simp_all [allocate, release, lend, close, put]
  omega

theorem lengths_preserved (old : x < s.heap.nextObject) (run : Steps s es t) :
    x < t.heap.nextObject ∧ t.length x = s.length x := by
  induction run with
  | nil => exact ⟨old, rfl⟩
  | cons step _ ih =>
    obtain ⟨bound, eq⟩ := length_preserved old step
    obtain ⟨bound', eq'⟩ := ih bound
    exact ⟨bound', eq'.trans eq⟩

/-- In this uniform-fill fragment, even freed objects retain their old fill.
New allocations use fresh identities; no write transition is available. -/
theorem payload_preserved (old : x < s.heap.nextObject) (run : Step s e t) :
    t.heap.payload x = s.heap.payload x := by
  cases run <;> simp_all [allocate, release, lend, close, put]
  omega

theorem payloads_preserved (old : x < s.heap.nextObject) (run : Steps s es t) :
    t.heap.payload x = s.heap.payload x := by
  induction run with
  | nil => rfl
  | cons step _ ih =>
    exact (ih (length_preserved old step).1).trans (payload_preserved old step)

/-- A conservative embedding of the previous single-cell read-only model. -/
def buffer1 (s : HeapLeases.State) : State := ⟨s, fun _ => 1⟩

def Event.single : HeapLeases.Event → Event
  | .alloc x v => .alloc x 1 v
  | .free x => .free x
  | .beginLease l x => .beginLease l x
  | .close l => .close l
  | .read l v => .read l 0 v
  | .write x v => .alloc x 1 v -- outside the embedding's no-write domain

def ReadOnly (e : HeapLeases.Event) : Prop :=
  ∀ x v, e ≠ .write x v

theorem project_readonly (e : Event) : ReadOnly e.project := by
  cases e <;> simp [ReadOnly, Event.project]

theorem single_project (readonly : ReadOnly e) : (Event.single e).project = e := by
  cases e <;> simp_all [Event.single, Event.project, ReadOnly]

theorem buffer1_step (run : HeapLeases.Step s e t) (readonly : ReadOnly e) :
    Step (buffer1 s) (Event.single e) (buffer1 t) := by
  cases run with
  | alloc =>
    have eq : put (fun _ : Nat => 1) s.nextObject 1 = (fun _ => 1) := by
      funext x; simp [put]
    simpa [Event.single, buffer1, allocate, eq] using
      (Step.alloc (s := buffer1 s) (n := 1))
  | free live unborrowed => exact .free live unborrowed
  | beginLease live => exact .beginLease live
  | close present => exact .close present
  | read present => exact .read present (by simp [buffer1])
  | write live unborrowed => exact False.elim (readonly _ _ rfl)

theorem buffer1_steps (run : HeapLeases.Steps s es t)
    (readonly : ∀ e ∈ es, ReadOnly e) :
    Steps (buffer1 s) (es.map Event.single) (buffer1 t) := by
  induction run with
  | nil => exact .nil
  | cons step _ ih =>
    exact .cons (buffer1_step step (readonly _ (by simp)))
      (ih (by intro e h; exact readonly e (by simp [h])))

/-- Return from a read-only lease preserves all object fields and lengths;
only the fresh lease counter advances. -/
def restore (s : State) : State := ⟨ScopedLend.restored s.heap, s.length⟩

theorem restore_length : (restore s).length = s.length := rfl

/-- Fresh allocation extends the existing ownership projection. -/
theorem allocate_owns (valid : Valid s)
    (owned : LinearHeapPrograms.Owns s.heap owners) :
    LinearHeapPrograms.Owns (allocate s n v).heap (s.heap.nextObject :: owners) :=
  LinearHeapPrograms.allocate_owns valid owned

/-- Releasing a selected capability preserves every other live capability. -/
theorem release_owns (owned : LinearHeapPrograms.Owns s.heap owners)
    (selected : LinearHeapPrograms.Select owners slot x rest) :
    LinearHeapPrograms.Owns (release s x).heap rest := by
  obtain ⟨distinct, absent⟩ := selected.unique owned.distinct
  refine ⟨distinct, ?_, ?_⟩
  · intro y member
    have ne : y ≠ x := fun eq => absent (eq ▸ member)
    simp [release, put, ne, owned.live _ (selected.subset _ member)]
  · intro y member
    exact owned.leaseFree _ (selected.subset _ member)

theorem restored_owns (owned : LinearHeapPrograms.Owns s.heap owners) :
    LinearHeapPrograms.Owns (restore s).heap owners :=
  ⟨owned.distinct, owned.live, owned.leaseFree⟩

theorem close_lend_restore (valid : Valid s) :
    close (lend s x) s.heap.nextLease = restore s := by
  have h := ScopedLend.close_restores (s := s.heap) (x := x) valid
  cases s
  simp only [close, lend, restore]
  congr 1

/-- Typing supplies liveness and the index bound. The full lease cycle is then
constructed, not assumed as an already safe event trace. -/
theorem read_cycle (valid : Valid s) (live : s.heap.live x = true)
    (bound : i < s.length x) :
    Steps s [.beginLease s.heap.nextLease x,
      .read s.heap.nextLease i (s.heap.payload x), .close s.heap.nextLease]
      (restore s) := by
  have lease : (lend s x).heap.lease s.heap.nextLease = some x := by
    simp [lend, put]
  have read : Step (lend s x) (.read s.heap.nextLease i (s.heap.payload x))
      (lend s x) := .read lease bound
  have shut : Step (lend s x) (.close s.heap.nextLease) (restore s) := by
    rw [← close_lend_restore valid]
    exact .close lease
  exact .cons (.beginLease live) (.cons read (.cons shut .nil))

end Jihoo.SizedBufferHeap
