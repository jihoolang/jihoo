import Jihoo.SizedBufferContext

/-!
Compact environments for sized-buffer erasure. Source environments retain a
slot for a proof value; runtime environments contain only observable values.
The mask records which source slots survive, and `rank mask k` counts the
surviving slots strictly before source index `k`.
-/

namespace Jihoo.SizedErasure

inductive Value where
  | nat (n : Nat)
  | scalar (v : Nat)
  | owner (x : Nat)
  | borrow (x : Nat)
  deriving DecidableEq, Repr

def Value.embed : Value → SizedBufferContext.Value
  | .nat n => .nat n
  | .scalar v => .scalar v
  | .owner x => .owner x
  | .borrow x => .borrow x

@[simp] theorem Value.embed_inj {v w : Value} : v.embed = w.embed ↔ v = w := by
  cases v <;> cases w <;> simp [Value.embed]

@[simp] theorem Value.embed_ne_ghost (v : Value) : v.embed ≠ .ghost := by
  cases v <;> simp [Value.embed]

abbrev Mask := List Bool
abbrev Env := List Value

/-- The runtime index of a retained source slot. -/
def rank : Mask → Nat → Nat
  | _, 0 => 0
  | [], _ + 1 => 0
  | true :: mask, k + 1 => rank mask k + 1
  | false :: mask, k + 1 => rank mask k

@[simp] theorem rank_zero (mask : Mask) : rank mask 0 = 0 := by cases mask <;> rfl
@[simp] theorem rank_nil (k : Nat) : rank [] k = 0 := by cases k <;> rfl
@[simp] theorem rank_keep (mask : Mask) (k : Nat) :
    rank (true :: mask) (k + 1) = rank mask k + 1 := rfl
@[simp] theorem rank_drop (mask : Mask) (k : Nat) :
    rank (false :: mask) (k + 1) = rank mask k := rfl

theorem rank_eq_count_take (mask : Mask) (k : Nat) :
    rank mask k = (mask.take k).count true := by
  induction mask generalizing k with
  | nil => simp
  | cons keep mask ih =>
    cases k with
    | zero => simp
    | succ k => cases keep <;> simp [rank, ih]

/-- Every compact value has a source slot, and every removed slot is ghost. -/
inductive EnvRel : Mask → SizedBufferContext.Env → Env → Prop where
  | nil : EnvRel [] [] []
  | consKeep {mask source target} (v : Value) (tail : EnvRel mask source target) :
      EnvRel (true :: mask) (v.embed :: source) (v :: target)
  | consGhost {mask source target} (tail : EnvRel mask source target) :
      EnvRel (false :: mask) (.ghost :: source) target

/-- Executable input compaction removes precisely proof placeholders. Stale
runtime aliases remain values and retain their slots. -/
def compactEnv : SizedBufferContext.Env → Mask × Env
  | [] => ([], [])
  | .ghost :: rest =>
      let (mask, runtime) := compactEnv rest
      (false :: mask, runtime)
  | .nat n :: rest =>
      let (mask, runtime) := compactEnv rest
      (true :: mask, .nat n :: runtime)
  | .scalar v :: rest =>
      let (mask, runtime) := compactEnv rest
      (true :: mask, .scalar v :: runtime)
  | .owner x :: rest =>
      let (mask, runtime) := compactEnv rest
      (true :: mask, .owner x :: runtime)
  | .borrow x :: rest =>
      let (mask, runtime) := compactEnv rest
      (true :: mask, .borrow x :: runtime)

theorem compactEnv_related (env : SizedBufferContext.Env) :
    EnvRel (compactEnv env).1 env (compactEnv env).2 := by
  induction env with
  | nil => exact .nil
  | cons value rest ih =>
      cases value with
      | ghost => exact .consGhost ih
      | nat n => exact .consKeep (.nat n) ih
      | scalar v => exact .consKeep (.scalar v) ih
      | owner x => exact .consKeep (.owner x) ih
      | borrow x => exact .consKeep (.borrow x) ih

namespace EnvRel

variable {mask : Mask} {source : SizedBufferContext.Env} {target : Env}
variable {k j n x slot : Nat} {ctx : SizedBufferContext.Context} {owners : List Nat}

theorem source_length (h : EnvRel mask source target) : source.length = mask.length := by
  induction h <;> simp_all

theorem target_length (h : EnvRel mask source target) :
    target.length = rank mask mask.length := by
  induction h <;> simp_all

theorem length_le (h : EnvRel mask source target) : target.length ≤ source.length := by
  induction h <;> simp_all <;> omega

theorem strictly_shorter (h : EnvRel mask source target)
    (present : SizedBufferContext.Value.ghost ∈ source) : target.length < source.length := by
  induction h with
  | nil => simp at present
  | consKeep v tail ih =>
      rcases List.mem_cons.mp present with eq | rest
      · exact False.elim (v.embed_ne_ghost eq.symm)
      · exact Nat.succ_lt_succ (ih rest)
  | consGhost tail _ih =>
      have bound := tail.length_le
      simp only [List.length_cons]
      omega

theorem ghost_lookup (h : EnvRel mask source target)
    (erased : mask[k]? = some false) : source[k]? = some .ghost := by
  induction h generalizing k with
  | nil => simp at erased
  | consKeep v tail ih =>
    cases k with
    | zero => simp at erased
    | succ k => exact ih erased
  | consGhost tail ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih erased

theorem ghost_iff (h : EnvRel mask source target) :
    source[k]? = some .ghost ↔ mask[k]? = some false := by
  constructor
  · intro lookup
    induction h generalizing k with
    | nil => simp at lookup
    | consKeep v tail ih =>
      cases k with
      | zero =>
        exact False.elim (v.embed_ne_ghost (Option.some.inj lookup))
      | succ k => exact ih lookup
    | consGhost tail ih =>
      cases k with
      | zero => rfl
      | succ k => exact ih lookup
  · exact h.ghost_lookup

/-- A non-ghost source lookup necessarily refers to a retained slot. -/
theorem retained_of_nonGhost (h : EnvRel mask source target) {v : SizedBufferContext.Value}
    (lookup : source[k]? = some v) (nonGhost : v ≠ .ghost) :
    mask[k]? = some true := by
  induction h generalizing k with
  | nil => simp at lookup
  | consKeep w tail ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih lookup
  | consGhost tail ih =>
    cases k with
    | zero => exact False.elim (nonGhost (Option.some.inj lookup).symm)
    | succ k => exact ih lookup

theorem retained_of_lookup (h : EnvRel mask source target) {v : Value}
    (lookup : source[k]? = some v.embed) : mask[k]? = some true :=
  h.retained_of_nonGhost lookup v.embed_ne_ghost

/-- Retained source lookups and compact runtime lookups agree at `rank`. -/
theorem retained_lookup_iff (h : EnvRel mask source target) {v : Value}
    (retained : mask[k]? = some true) :
    source[k]? = some v.embed ↔ target[rank mask k]? = some v := by
  induction h generalizing k with
  | nil => simp at retained
  | consKeep w tail ih =>
    cases k with
    | zero => simp
    | succ k => simpa using ih retained
  | consGhost tail ih =>
    cases k with
    | zero => simp at retained
    | succ k => simpa using ih retained

theorem lookup (h : EnvRel mask source target) {v : Value}
    (sourceLookup : source[k]? = some v.embed) : target[rank mask k]? = some v :=
  (h.retained_lookup_iff (h.retained_of_lookup sourceLookup)).mp sourceLookup

/-- A target lookup always originates at a retained source slot. -/
theorem lookup_source (h : EnvRel mask source target) {v : Value}
    (targetLookup : target[j]? = some v) :
    ∃ k, mask[k]? = some true ∧ rank mask k = j ∧ source[k]? = some v.embed := by
  induction h generalizing j with
  | nil => simp at targetLookup
  | consKeep w tail ih =>
    cases j with
    | zero =>
      have eq : w = v := Option.some.inj targetLookup
      subst w
      exact ⟨0, rfl, rfl, rfl⟩
    | succ j =>
      obtain ⟨k, retained, rnk, lookup⟩ := ih targetLookup
      exact ⟨k + 1, retained, by simp [rnk], lookup⟩
  | consGhost tail ih =>
    obtain ⟨k, retained, rnk, lookup⟩ := ih targetLookup
    exact ⟨k + 1, retained, rnk, lookup⟩

theorem nat_lookup (h : EnvRel mask source target)
    (sourceLookup : source[k]? = some (.nat n)) :
    target[rank mask k]? = some (.nat n) :=
  h.lookup (v := .nat n) sourceLookup

theorem scalar_lookup (h : EnvRel mask source target)
    (sourceLookup : source[k]? = some (.scalar v)) :
    target[rank mask k]? = some (.scalar v) :=
  h.lookup (v := .scalar v) sourceLookup

theorem owner_lookup (h : EnvRel mask source target)
    (sourceLookup : source[k]? = some (.owner x)) :
    target[rank mask k]? = some (.owner x) :=
  h.lookup (v := .owner x) sourceLookup

theorem borrow_lookup (h : EnvRel mask source target)
    (sourceLookup : source[k]? = some (.borrow x)) :
    target[rank mask k]? = some (.borrow x) :=
  h.lookup (v := .borrow x) sourceLookup

/-- Typing's natural-variable lookup supplies both retention and its value. -/
theorem typed_nat_lookup (h : EnvRel mask source target)
    (agrees : SizedBufferContext.Agrees ctx owners source)
    (typed : ctx[k]? = some (.nat n)) :
    mask[k]? = some true ∧ target[rank mask k]? = some (.nat n) := by
  have lookup := agrees.nat_lookup k n typed
  exact ⟨h.retained_of_lookup (v := .nat n) lookup, h.nat_lookup lookup⟩

theorem typed_scalar_lookup (h : EnvRel mask source target)
    (agrees : SizedBufferContext.Agrees ctx owners source)
    (typed : ctx[k]? = some .scalar) :
    mask[k]? = some true ∧ ∃ v, target[rank mask k]? = some (.scalar v) := by
  obtain ⟨v, lookup⟩ := agrees.scalar_lookup k typed
  exact ⟨h.retained_of_lookup (v := .scalar v) lookup, v, h.scalar_lookup lookup⟩

theorem typed_owner_lookup (h : EnvRel mask source target)
    (agrees : SizedBufferContext.Agrees ctx owners source)
    (typed : ctx[k]? = some (.owner slot)) :
    mask[k]? = some true ∧
      ∃ x, owners[slot]? = some x ∧ target[rank mask k]? = some (.owner x) := by
  obtain ⟨x, ownerLookup, lookup⟩ := agrees.owner_lookup k slot typed
  exact ⟨h.retained_of_lookup (v := .owner x) lookup,
    x, ownerLookup, h.owner_lookup lookup⟩

theorem typed_bound_erased (h : EnvRel mask source target)
    (agrees : SizedBufferContext.Agrees ctx owners source)
    (typed : ctx[k]? = some (.bound fact)) : mask[k]? = some false :=
  h.ghost_iff.mp (agrees.bound_lookup k fact typed)

end EnvRel

/- A proof slot in the middle changes every later runtime index. -/
example : rank [true, false, true, false, true] 4 = 2 := rfl

example : EnvRel [true, false, true]
    [.nat 7, .ghost, .owner 3] [.nat 7, .owner 3] :=
  .consKeep (.nat 7) (.consGhost (.consKeep (.owner 3) .nil))

example (h : EnvRel [true, false, true] source target)
    (lookup : source[2]? = some (.owner 3)) : target[1]? = some (.owner 3) :=
  h.owner_lookup lookup

end Jihoo.SizedErasure
