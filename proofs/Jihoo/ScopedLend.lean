import Jihoo.HeapLeases
import Jihoo.QuantityLendProjection

/-! A specified read-only/scalar fragment of Core Lend, not arbitrary Core.
The reader uses bound borrow slots and cannot close a token, consume an owner,
or return a reference. Its continuation consumes the returned owner, optionally
storing the scalar result first. These restrictions are explicit syntax, rather
than postulated authority and free-event projection of arbitrary traces. -/
namespace Jihoo.ScopedLend
open HeapLeases

inductive Reader where
  | scalar (value : Nat)
  | read (slot : Nat)
  | seq (first second : Reader)
  | branch (condition : Bool) (yes no : Reader)
  deriving DecidableEq, Repr

inductive Scoped : Nat → Reader → Prop where
  | scalar : Scoped n (.scalar v)
  | read : k < n → Scoped n (.read k)
  | seq : Scoped n a → Scoped n b → Scoped n (.seq a b)
  | branch : Scoped n a → Scoped n b → Scoped n (.branch condition a b)

/-- A reader environment contains only active borrow tokens, never owners. -/
def EnvValid (s : State) (env : List Nat) : Prop :=
  ∀ l ∈ env, ∃ x, s.lease l = some x

/-- The value result is scalar, so no result constructor can hold a lease.
Both branches must be scoped, but only the selected branch executes. -/
inductive Reads (s : State) (env : List Nat) : Reader → Nat → List Event → Prop where
  | scalar : Reads s env (.scalar v) v []
  | read : env[k]? = some l → s.lease l = some x →
      Reads s env (.read k) (s.payload x) [.read l (s.payload x)]
  | seq : Reads s env a v xs → Reads s env b w ys → Reads s env (.seq a b) w (xs ++ ys)
  | yes : Reads s env a v es → Reads s env (.branch true a b) v es
  | no : Reads s env b v es → Reads s env (.branch false a b) v es

theorem read_observation (read : Reads s env (.read k) v es) :
    ∃ l x, env[k]? = some l ∧ s.lease l = some x ∧ v = s.payload x := by
  cases read with
  | read slot lease => exact ⟨_, _, slot, lease, rfl⟩

/-- Typed/scoped readers cannot get stuck looking up a borrow. -/
theorem reader_total (scope : Scoped env.length r) (valid : EnvValid s env) :
    ∃ v es, Reads s env r v es := by
  induction r generalizing env with
  | scalar => exact ⟨_, [], .scalar⟩
  | read k =>
    cases scope with
    | read bound =>
      have lookup : env[k]? = some env[k] := List.getElem?_eq_getElem bound
      obtain ⟨x, hx⟩ := valid env[k] (List.getElem_mem bound)
      exact ⟨_, _, .read lookup hx⟩
  | seq a b ia ib =>
    cases scope with
    | seq ha hb =>
      obtain ⟨v, xs, ha⟩ := ia ha valid
      obtain ⟨w, ys, hb⟩ := ib hb valid
      exact ⟨_, _, .seq ha hb⟩
  | branch condition a b ia ib =>
    cases scope with
    | branch ha hb =>
      cases condition with
      | false => obtain ⟨v, es, h⟩ := ib hb valid; exact ⟨_, _, .no h⟩
      | true => obtain ⟨v, es, h⟩ := ia ha valid; exact ⟨_, _, .yes h⟩

theorem steps_append (a : Steps s xs t) (b : Steps t ys u) : Steps s (xs ++ ys) u := by
  induction a with
  | nil => exact b
  | cons h _ ih => exact .cons h (ih b)

/-- This primitive execution witness is derived from reader syntax; no caller
supplies an arbitrary heap trace or asserts its safety. -/
theorem reader_steps (read : Reads s env r v es) : Steps s es s := by
  induction read with
  | scalar => exact .nil
  | read _ h => exact .cons (.read h) .nil
  | seq _ _ ia ib => exact steps_append ia ib
  | yes _ ih | no _ ih => exact ih

/-- Structural authority: every reader derivation leaves all closes to Lend. -/
theorem reader_authority (read : Reads s env r v es) : ReaderEvents l es := by
  induction read with
  | scalar => simp [ReaderEvents]
  | read => simp [ReaderEvents]
  | seq _ _ ia ib => simpa [ReaderEvents] using And.intro ia ib
  | yes _ ih | no _ ih => exact ih

theorem reader_releases (read : Reads s env r v es) : released es = [] := by
  induction read with
  | scalar => rfl
  | read => rfl
  | seq _ _ ia ib =>
    simp only [released, List.filterMap_append] at *
    rw [ia, ib]
    rfl
  | yes _ ih | no _ ih => exact ih

def opened (s : State) (x : Nat) : State :=
  { s with nextLease := s.nextLease + 1, lease := put s.lease s.nextLease (some x) }

def restored (s : State) : State := { s with nextLease := s.nextLease + 1 }

/-- Scope exit restores every previous lease, not just the lent owner's token.
The fresh-token counter advances so an expired handle cannot be reused. -/
theorem close_restores (valid : Valid s) :
    { opened s x with lease := put (opened s x).lease s.nextLease none } = restored s := by
  have fresh := lease_fresh valid
  have leases : put (opened s x).lease s.nextLease none = s.lease := by
    funext l
    by_cases h : l = s.nextLease
    · subst l; simp [put, fresh]
    · simp [put, opened, h]
  cases s
  simp_all [opened, restored]

inductive Continuation where
  | free
  | freeOriginal
  | storeResult
  deriving DecidableEq, Repr

def finalState (s : State) (x v : Nat) : Continuation → State
  | .free | .freeOriginal => { restored s with live := put s.live x false }
  | .storeResult => { restored s with live := put s.live x false, payload := put s.payload x v }

def continuationEvents (x v : Nat) : Continuation → List Event
  | .free | .freeOriginal => [.free x]
  | .storeResult => [.write x v, .free x]

/-- The continuation receives the very same allocation identity; no scalar
payload is reinterpreted as an owner or a lease token. -/
theorem continuation_steps (live : s.live x = true) (available : Unborrowed s x) :
    Steps (restored s) (continuationEvents x v k) (finalState s x v k) := by
  cases k with
  | free | freeOriginal => exact .cons (.free live available) .nil
  | storeResult => exact .cons (.write live available) (.cons (.free live available) .nil)

/-- Core's continuation opens scalar result then returned-owner binders. The
old owner is therefore slot 2; its returned alias is slot 0. -/
def continuationControl : Continuation → Quantity.Control
  | .free | .storeResult => .use 0
  | .freeOriginal => .use 2

def sourceControl (k : Continuation) : Quantity.Control :=
  Quantity.LendProjection.scopedLend 0 .unrestricted .pure (continuationControl k)

theorem source_quantity_checked :
    Quantity.LendProjection.checkedLend 0 .unrestricted .pure (continuationControl k) =
      some (sourceControl k) := by
  cases k <;> decide

theorem source_quantity_finishes : Quantity.Finishes (sourceControl k) [0] := by
  cases k <;> exact Quantity.LendProjection.scoped_lend_finishes
    (owner := 0) (mode := .unrestricted) Quantity.Finishes.pure Quantity.Finishes.use

/-- Interpret the sole external owner slot as this allocation identity.
This is constructed here, not an assumed mapping of arbitrary Core contexts. -/
def heapControl (x : Nat) (k : Continuation) : Quantity.Control :=
  (sourceControl k).rename (fun _ => x)

theorem heap_quantity_checked : (heapControl x k).demand x = some 1 := by
  cases k <;> simp [heapControl, sourceControl, continuationControl,
    Quantity.LendProjection.scopedLend, Quantity.Control.alias,
    Quantity.Control.rename, Quantity.openOwner, Quantity.lift, Quantity.Control.demand]

/-- The rule mirrors `g(f(Borrow(x)), x)`: bind a read token, evaluate scalar f,
end its scope, pass the scalar result and unchanged owner identity to g. -/
inductive Executes (s : State) (x : Nat) (body : Reader) (k : Continuation) :
    Nat → List Event → State → Prop where
  | lend : Reads (opened s x) [s.nextLease] body v reads →
      Executes s x body k v
        ([.beginLease s.nextLease x] ++ reads ++ [.close s.nextLease] ++ continuationEvents x v k)
        (finalState s x v k)

/-- Source scoping plus a live target with no preexisting lease discharges all primitive
read/close/write/free preconditions for this Lend fragment. -/
theorem lend_total (valid : Valid s) (live : s.live x = true)
    (available : Unborrowed s x) (scope : Scoped 1 body) :
    ∃ v es t, Executes s x body k v es t ∧ Steps s es t := by
  have env : EnvValid (opened s x) [s.nextLease] := by
    intro l member
    simp only [List.mem_singleton] at member
    subst l
    exact ⟨x, by simp [opened, put]⟩
  obtain ⟨v, reads, reader⟩ := reader_total (env := [s.nextLease]) scope env
  refine ⟨v, _, _, .lend reader, ?_⟩
  have closed : Step (opened s x) (.close s.nextLease) (restored s) := by
    rw [← close_restores (x := x) valid]
    exact .close (x := x) (by simp [opened, put])
  exact steps_append (steps_append (Steps.cons (Step.beginLease live) (reader_steps reader))
    (Steps.cons closed Steps.nil)) (continuation_steps live available)

/-- Every source derivation, not merely the witness chosen by totality, has
an actual primitive execution. -/
theorem execution_steps (valid : Valid s) (live : s.live x = true)
    (available : Unborrowed s x) (run : Executes s x body k v es t) : Steps s es t := by
  cases run with
  | lend reader =>
    have closed : Step (opened s x) (.close s.nextLease) (restored s) := by
      rw [← close_restores (x := x) valid]
      exact .close (x := x) (by simp [opened, put])
    exact steps_append (steps_append (Steps.cons (Step.beginLease live) (reader_steps reader))
      (Steps.cons closed Steps.nil)) (continuation_steps live available)

/-- Reader-local tokens do not escape into the returned lease environment.
Existing ambient borrows survive unchanged; only the fresh counter advances. -/
theorem execution_lease_frame (run : Executes s x body k v es t) :
    t.lease = s.lease ∧ t.nextLease = s.nextLease + 1 := by
  cases run
  cases k <;> exact ⟨rfl, rfl⟩

/-- Even arbitrary later heap activity cannot use the reader's expired token. -/
theorem execution_token_expires (valid : Valid s)
    (run : Executes s x body k v es t) (later : Steps t tail u) :
    ¬ Step u (.read s.nextLease w) final := by
  obtain ⟨leases, counter⟩ := execution_lease_frame run
  have expired : t.lease s.nextLease = none := by rw [leases]; exact lease_fresh valid
  have old : s.nextLease < t.nextLease := by omega
  have h := expired_steps old expired later
  intro bad
  cases bad with
  | read lookup => simp [h.2] at lookup

/-- The control/free projection is computed from source constructors, removing
#132's arbitrary trace-projection premise for this fragment. -/
theorem execution_releases (run : Executes s x body k v es t) : released es = [x] := by
  cases run with
  | lend reader =>
    have hr := reader_releases reader
    cases k <;> simp_all [released, List.filterMap_append, continuationEvents]

theorem execution_quantity (run : Executes s x body k v es t) :
    Quantity.Finishes (heapControl x k) (released es) := by
  rw [execution_releases run]
  exact (source_quantity_finishes (k := k)).rename (fun _ => x)

theorem lend_owner_dead (valid : Valid s) (live : s.live x = true)
    (available : Unborrowed s x) (run : Executes s x body k v es t) :
    Valid t ∧ (released es).count x = 1 ∧ t.live x = false := by
  have steps := execution_steps valid live available run
  exact ⟨steps_valid valid steps,
    checked_owner_released valid steps (execution_quantity run) heap_quantity_checked⟩

end Jihoo.ScopedLend
