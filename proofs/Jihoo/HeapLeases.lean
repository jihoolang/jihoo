import Jihoo.QuantityControl

/-! Heap identities and explicit read leases for the runtime specification.
Objects and leases have separate monotonically fresh identities. A lease is
not ownership: it authorizes reads only until the lender closes it. This is a
primitive runtime semantics, not a proof of the native checker or allocator.
In particular a typing/translation theorem must still ensure that only the
lender can close a lease and that returned Core values do not retain it. -/
namespace Jihoo.HeapLeases

structure State where
  nextObject : Nat
  nextLease : Nat
  live : Nat → Bool
  payload : Nat → Nat
  lease : Nat → Option Nat

def empty : State := ⟨0, 0, fun _ => false, fun _ => 0, fun _ => none⟩

def put (f : Nat → α) (k : Nat) (v : α) : Nat → α :=
  fun j => if j = k then v else f j

structure Valid (s : State) : Prop where
  allocated : ∀ x, s.live x = true → x < s.nextObject
  leased : ∀ l x, s.lease l = some x → l < s.nextLease ∧ s.live x = true

def Unborrowed (s : State) (x : Nat) : Prop := ∀ l, s.lease l ≠ some x

inductive Event where
  | alloc (object value : Nat)
  | free (object : Nat)
  | beginLease (token object : Nat)
  | close (token : Nat)
  | read (token value : Nat)
  | write (object value : Nat)
  deriving DecidableEq, Repr

/-- Reads carry the observed value, so lease validity is also a statement about
which object's contents were observed. Allocation failure/overflow traps may
stop a prefix; this model makes no progress or allocation-success claim. -/
inductive Step : State → Event → State → Prop where
  | alloc : Step s (.alloc s.nextObject value)
      { s with nextObject := s.nextObject + 1, live := put s.live s.nextObject true, payload := put s.payload s.nextObject value }
  | free : s.live x = true → Unborrowed s x →
      Step s (.free x) { s with live := put s.live x false }
  | beginLease : s.live x = true → Step s (.beginLease s.nextLease x)
      { s with nextLease := s.nextLease + 1, lease := put s.lease s.nextLease (some x) }
  | close : s.lease l = some x → Step s (.close l) { s with lease := put s.lease l none }
  | read : s.lease l = some x → Step s (.read l (s.payload x)) s
  | write : s.live x = true → Unborrowed s x →
      Step s (.write x value) { s with payload := put s.payload x value }

theorem empty_valid : Valid empty := by
  constructor <;> simp [empty]

theorem step_valid (valid : Valid s) (step : Step s e t) : Valid t := by
  cases step with
  | alloc =>
    constructor
    · intro x hx
      simp only [put] at hx
      split at hx
      · dsimp; omega
      · exact Nat.lt_trans (valid.allocated x hx) (Nat.lt_succ_self _)
    · intro l x hx
      obtain ⟨hl, hLive⟩ := valid.leased l x hx
      exact ⟨hl, by simp [put, hLive]⟩
  | free live free =>
    constructor
    · intro x hx
      simp only [put] at hx
      split at hx
      · contradiction
      · exact valid.allocated x hx
    · intro l x hx
      obtain ⟨hl, hLive⟩ := valid.leased l x hx
      refine ⟨hl, ?_⟩
      simp only [put]
      split
      · next he => subst x; exact False.elim (free l hx)
      · exact hLive
  | beginLease live =>
    constructor
    · exact valid.allocated
    · intro l x hx
      simp only [put] at hx
      split at hx
      · next he => simp only [Option.some.injEq] at hx; subst x; exact ⟨by dsimp; omega, live⟩
      · obtain ⟨hl, hLive⟩ := valid.leased l x hx
        exact ⟨by dsimp; omega, hLive⟩
  | close present =>
    constructor
    · exact valid.allocated
    · intro l x hx
      simp only [put] at hx
      split at hx
      · contradiction
      · exact valid.leased l x hx
  | read => exact valid
  | write => exact ⟨valid.allocated, valid.leased⟩

/-- Fresh objects cannot alias any previously live object. -/
theorem allocation_fresh (valid : Valid s) : s.live s.nextObject = false := by
  cases h : s.live s.nextObject
  · rfl
  · have := valid.allocated _ h; omega

theorem lease_fresh (valid : Valid s) : s.lease s.nextLease = none := by
  cases h : s.lease s.nextLease
  · rfl
  · have := (valid.leased _ _ h).1; omega

theorem read_live (valid : Valid s) (step : Step s (.read l v) t) :
    ∃ x, s.lease l = some x ∧ s.live x = true ∧ v = s.payload x := by
  cases step with
  | read h => exact ⟨_, h, (valid.leased _ _ h).2, rfl⟩

theorem borrowed_not_freed (borrowed : s.lease l = some x) : ¬ Step s (.free x) t := by
  intro step
  cases step with
  | free _ h => exact h l borrowed

theorem borrowed_not_written (borrowed : s.lease l = some x) :
    ¬ Step s (.write x value) t := by
  intro step
  cases step with
  | write _ h => exact h l borrowed

/-- An expired lease token never becomes valid again, even after other lends. -/
theorem expired_step (old : l < s.nextLease) (expired : s.lease l = none)
    (step : Step s e t) : l < t.nextLease ∧ t.lease l = none := by
  cases step <;> simp_all [put]
  case beginLease => exact ⟨by omega, by omega⟩

/-- Freed identities cannot be recycled by allocation. An implementation may
reuse addresses, but then needs a generation/ownership simulation for this rule. -/
theorem dead_step (old : x < s.nextObject) (dead : s.live x = false)
    (step : Step s e t) : x < t.nextObject ∧ t.live x = false := by
  cases step <;> simp_all [put]
  case alloc => exact ⟨by omega, by omega⟩

inductive Steps : State → List Event → State → Prop where
  | nil : Steps s [] s
  | cons : Step s e t → Steps t es u → Steps s (e :: es) u

theorem steps_valid (valid : Valid s) (run : Steps s es t) : Valid t := by
  induction run with
  | nil => exact valid
  | cons step _ ih => exact ih (step_valid valid step)

theorem expired_steps (old : l < s.nextLease) (expired : s.lease l = none)
    (run : Steps s es t) : l < t.nextLease ∧ t.lease l = none := by
  induction run with
  | nil => exact ⟨old, expired⟩
  | cons step _ ih =>
    obtain ⟨ho, he⟩ := expired_step old expired step
    exact ih ho he

theorem dead_steps (old : x < s.nextObject) (dead : s.live x = false)
    (run : Steps s es t) : x < t.nextObject ∧ t.live x = false := by
  induction run with
  | nil => exact ⟨old, dead⟩
  | cons step _ ih =>
    obtain ⟨ho, he⟩ := dead_step old dead step
    exact ih ho he

/-- The lifetime endpoint excludes stale reads after any intervening trace. -/
theorem closed_lease_unreadable (valid : Valid s) (close : Step s (.close l) t)
    (run : Steps t es u) : ¬ Step u (.read l value) v := by
  cases close with
  | close present =>
    have h := expired_steps (s := { s with lease := put s.lease l none }) (valid.leased _ _ present).1 (by simp [put]) run
    intro read
    cases read with
    | read present => simp [h.2] at present

/-- No second free is possible after arbitrary allocation/borrow/write steps. -/
theorem no_double_free (valid : Valid s) (free : Step s (.free x) t)
    (run : Steps t es u) : ¬ Step u (.free x) v := by
  cases free with
  | free live _ =>
    have h := dead_steps (s := { s with live := put s.live x false }) (valid.allocated _ live) (by simp [put]) run
    intro second
    cases second with
    | free live _ => simp [h.2] at live

/-- A reader may open/close nested leases, but cannot close its lender's token.
This is the authority side condition to discharge when typing Core `Lend`. -/
def ReaderEvents (l : Nat) (es : List Event) : Prop := .close l ∉ es

theorem reader_step (valid : Valid s) (borrowed : s.lease l = some x)
    (notClose : e ≠ .close l) (step : Step s e t) :
    t.lease l = some x ∧ t.payload x = s.payload x := by
  have hx := valid.allocated x (valid.leased l x borrowed).2
  have hl := (valid.leased l x borrowed).1
  cases step <;> simp_all [put]
  case alloc => omega
  case beginLease => omega
  case close => exact Ne.symm notClose
  case write y value live hFree =>
    intro he; subst y; exact False.elim (hFree l borrowed)

/-- Arbitrarily nested reader activity cannot change or invalidate the lent
object. This is a heap/value frame property, not just counting a resource use. -/
theorem reader_steps (valid : Valid s) (borrowed : s.lease l = some x)
    (region : ReaderEvents l es) (run : Steps s es t) :
    t.lease l = some x ∧ t.live x = true ∧ t.payload x = s.payload x := by
  induction run with
  | nil => exact ⟨borrowed, (valid.leased _ _ borrowed).2, rfl⟩
  | @cons start event middle events finish step tail ih =>
    have hn : event ≠ Event.close l := by
      intro he; subst he; exact region (by simp)
    have hr : ReaderEvents l events := by
      intro member; exact region (by simp [member])
    obtain ⟨hb, hv⟩ := reader_step valid borrowed hn step
    obtain ⟨hb', hl', hv'⟩ := ih (step_valid valid step) hb hr
    exact ⟨hb', hl', hv'.trans hv⟩

/-- The heap observation coupled to quantity accounting: only destruction,
not reads or lease opens, consumes an owned allocation identity. -/
def released (es : List Event) : List Nat :=
  es.filterMap fun e => match e with | .free x => some x | _ => none

theorem released_mem : x ∈ released es ↔ Event.free x ∈ es := by
  induction es with
  | nil => simp [released]
  | cons e es ih => cases e <;> simp_all [released]

theorem released_dead (valid : Valid s) (run : Steps s es t)
    (member : Event.free x ∈ es) : t.live x = false := by
  induction run with
  | nil => simp at member
  | @cons start event middle events finish step tail ih =>
    simp only [List.mem_cons] at member
    rcases member with eq | rest
    · subst eq
      cases step with
      | free live _ =>
        exact (dead_steps (s := { start with live := put start.live x false })
          (valid.allocated _ live) (by simp [put]) tail).2
    · exact ih (step_valid valid step) rest

/-- Quantity accounting and heap execution now speak about the SAME free
identities. The projection/correspondence premise is explicit, rather than
assuming a scalar use denotes a deallocation. Under it a completed demand-one
owner is actually dead, not merely observed once in an abstract control trace. -/
theorem checked_owner_released (valid : Valid s) (run : Steps s es t)
    (projection : Quantity.Finishes c (released es)) (checked : c.demand x = some 1) :
    (released es).count x = 1 ∧ t.live x = false := by
  have count := projection.count_eq checked
  refine ⟨count, released_dead valid run (released_mem.mp ?_)⟩
  have positive : 0 < (released es).count x := by omega
  exact List.count_pos_iff.mp positive

end Jihoo.HeapLeases
