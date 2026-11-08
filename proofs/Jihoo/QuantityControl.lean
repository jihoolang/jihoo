import Std.Tactic

/-! A control-flow foundation for the quantity obligation. This is not a
translation of Core terms: resolving binders, erased arguments, saturated calls
and recursive cases into this control language remains an explicit obligation.
Events identify uses of an outer resource, not allocation/free actions. -/
namespace Jihoo.Quantity

/-- Borrowed slots are unrestricted only for quantity accounting. This mode
carries no claim about lease validity or lifetime safety. -/
inductive BinderMode where
  | linear | erased | unrestricted | borrowed
  deriving DecidableEq, Repr

inductive Control where
  | pure
  | use (resource : Nat)
  | seq (a b : Control)
  | branch (a b : Control)
  | repeat (body : Control)
  | once (body : Control)
  | closure (body : Control)
  | erased (body : Control)
  | trap
  | scope (mode : BinderMode) (body : Control)
  deriving DecidableEq, Repr

/-- Compatibility spelling for a fresh linear local owner. -/
abbrev Control.bind (body : Control) : Control := .scope .linear body

/-- Check one resource. Reusable code must not capture it. Branches must agree
on demand. Erased code and a returned closure execute no events. -/
def Control.demand (resource : Nat) : Control → Option Nat
  | .pure | .trap | .erased _ => some 0
  | .use x => some (if x = resource then 1 else 0)
  | .seq a b => do return (← a.demand resource) + (← b.demand resource)
  | .branch a b => do
      let x ← a.demand resource
      let y ← b.demand resource
      if x = y then some x else none
  | .repeat b | .closure b => do
      let n ← b.demand resource
      if n = 0 then some 0 else none
  | .scope .linear b => do
      let localDemand ← b.demand 0
      if localDemand = 1 then b.demand (resource + 1) else none
  | .scope .erased b => do
      let localDemand ← b.demand 0
      if localDemand = 0 then b.demand (resource + 1) else none
  | .scope .unrestricted b | .scope .borrowed b => b.demand (resource + 1)
  | .once b => b.demand resource

/-- Telescopes are written outermost first; every mode occupies one slot. -/
def Control.scopes (modes : List BinderMode) (body : Control) : Control :=
  modes.foldr Control.scope body

/-- Remove the locally bound resource and shift outer resource names down.
A new iteration's local owner is distinct from owners of previous iterations. -/
def discharge : List Nat → List Nat
  | [] => []
  | 0 :: xs => discharge xs
  | (n + 1) :: xs => n :: discharge xs

theorem discharge_count (xs : List Nat) (r : Nat) :
    (discharge xs).count r = xs.count (r + 1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases x <;> simp [discharge, List.count_cons, ih]

/-- Successful executions. Repetition has any finite iteration count, and
branches are nondeterministic: the checker must justify every choice. -/
inductive Finishes : Control → List Nat → Prop where
  | pure : Finishes .pure []
  | use : Finishes (.use x) [x]
  | seq : Finishes a xs → Finishes b ys → Finishes (.seq a b) (xs ++ ys)
  | left : Finishes a xs → Finishes (.branch a b) xs
  | right : Finishes b xs → Finishes (.branch a b) xs
  | repeatZero : Finishes (.repeat b) []
  | repeatNext : Finishes b xs → Finishes (.repeat b) ys →
      Finishes (.repeat b) (xs ++ ys)
  | once : Finishes b xs → Finishes (.once b) xs
  | closure : Finishes (.closure b) []
  | erased : Finishes (.erased b) []
  | bind : Finishes b xs → Finishes (.scope mode b) (discharge xs)

/-- Any finite execution prefix, including a trap and a prefix of a diverging
repeat. No assumption that a successful continuation exists is made. -/
inductive Prefix : Control → List Nat → Prop where
  | start : Prefix c []
  | use : Prefix (.use x) [x]
  | seqLeft : Prefix a xs → Prefix (.seq a b) xs
  | seqRight : Finishes a xs → Prefix b ys → Prefix (.seq a b) (xs ++ ys)
  | left : Prefix a xs → Prefix (.branch a b) xs
  | right : Prefix b xs → Prefix (.branch a b) xs
  | repeatNext : Finishes b xs → Prefix (.repeat b) ys →
      Prefix (.repeat b) (xs ++ ys)
  | repeatBody : Prefix b xs → Prefix (.repeat b) xs
  | once : Prefix b xs → Prefix (.once b) xs
  | bind : Prefix b xs → Prefix (.scope mode b) (discharge xs)

private theorem seq_demand (h : (Control.seq a b).demand r = some n) :
    ∃ x y, a.demand r = some x ∧ b.demand r = some y ∧ x + y = n := by
  simp only [Control.demand] at h
  cases ha : a.demand r <;> cases hb : b.demand r <;> simp_all

private theorem branch_demand (h : (Control.branch a b).demand r = some n) :
    a.demand r = some n ∧ b.demand r = some n := by
  simp only [Control.demand] at h
  cases ha : a.demand r <;> cases hb : b.demand r <;> simp_all

private theorem repeat_demand (h : (Control.repeat b).demand r = some n) :
    b.demand r = some 0 ∧ n = 0 := by
  simp only [Control.demand] at h
  cases hb : b.demand r <;> simp_all

private theorem bind_demand (h : (Control.bind b).demand r = some n) :
    b.demand 0 = some 1 ∧ b.demand (r + 1) = some n := by
  simp only [Control.demand] at h
  cases hb : b.demand 0 <;> simp_all

private theorem scope_outer (h : (Control.scope mode b).demand r = some n) :
    b.demand (r + 1) = some n := by
  cases mode <;> simp only [Control.demand] at h
  · cases hb : b.demand 0 <;> simp_all
  · cases hb : b.demand 0 <;> simp_all
  · exact h
  · exact h

private theorem scope_erased (h : (Control.scope .erased b).demand r = some n) :
    b.demand 0 = some 0 := by
  simp only [Control.demand] at h
  cases hb : b.demand 0 <;> simp_all

/-- All slots, including erased and unrestricted slots, shift an outer owner.
No assumption of uniform linear binder modes is used. -/
theorem scopes_outer (h : (Control.scopes modes b).demand r = some n) :
    b.demand (r + modes.length) = some n := by
  induction modes generalizing r with
  | nil => simpa [Control.scopes] using h
  | cons mode modes ih =>
      have ho := scope_outer h
      have hi := ih ho
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

private theorem closure_demand (h : (Control.closure b).demand r = some n) : n = 0 :=
  (repeat_demand h).2

/-- Exact accounting for every successful execution, not a selected branch. -/
theorem Finishes.count_eq (run : Finishes c xs) :
    c.demand r = some n → xs.count r = n := by
  induction run generalizing r n with
  | pure | erased => simp [Control.demand]
  | @use x =>
      by_cases hx : x = r
      · subst x
        intro h
        have hn : n = 1 := by simpa [Control.demand] using h.symm
        simp [hn]
      · simp [Control.demand, hx]
  | seq ha hb iha ihb =>
      intro h
      obtain ⟨x, y, hx, hy, rfl⟩ := seq_demand h
      simp [List.count_append, iha hx, ihb hy]
  | left ha ih => intro h; exact ih (branch_demand h).1
  | right hb ih => intro h; exact ih (branch_demand h).2
  | repeatZero => intro h; simpa using (repeat_demand h).2.symm
  | repeatNext ha hb iha ihb =>
      intro h
      have hz := repeat_demand h
      simp [List.count_append, iha hz.1, ihb h, hz.2]
  | once ha ih => exact ih
  | bind ha ih => intro h; rw [discharge_count]; exact ih (scope_outer h)
  | closure => intro h; simpa using (closure_demand h).symm

/-- A trap may abandon a resource, but no finite execution prefix can consume
it more often than the checked demand. This also covers diverging executions. -/
theorem Prefix.count_le (run : Prefix c xs) :
    c.demand r = some n → xs.count r ≤ n := by
  induction run generalizing r n with
  | start => simp
  | @use x =>
      by_cases hx : x = r
      · subst x
        intro h
        have hn : n = 1 := by simpa [Control.demand] using h.symm
        simp [hn]
      · simp [Control.demand, hx]
  | seqLeft ha ih =>
      intro h
      obtain ⟨x, y, hx, _, rfl⟩ := seq_demand h
      exact Nat.le_trans (ih hx) (Nat.le_add_right _ _)
  | seqRight ha hb ih =>
      intro h
      obtain ⟨x, y, hx, hy, rfl⟩ := seq_demand h
      simp only [List.count_append, ha.count_eq hx]
      exact Nat.add_le_add_left (ih hy) _
  | left ha ih => intro h; exact ih (branch_demand h).1
  | right hb ih => intro h; exact ih (branch_demand h).2
  | repeatNext ha hb ih =>
      intro h
      have hz := repeat_demand h
      simp only [List.count_append, ha.count_eq hz.1, Nat.zero_add]
      exact ih h
  | repeatBody ha ih =>
      intro h
      have hz := repeat_demand h
      simpa [hz.2] using ih hz.1
  | once ha ih => exact ih
  | bind ha ih => intro h; rw [discharge_count]; exact ih (scope_outer h)

theorem Finishes.prefix (run : Finishes c xs) : Prefix c xs := by
  induction run with
  | pure | repeatZero | closure | erased => exact .start
  | use => exact .use
  | seq ha hb iha ihb => exact .seqRight ha ihb
  | left ha ih => exact .left ih
  | right hb ih => exact .right ih
  | repeatNext ha hb iha ihb => exact .repeatNext ha ihb
  | once ha ih => exact .once ih
  | bind ha ih => exact .bind ih

/-- The local ownership obligation is checked independently of every outer
resource. Successful scope exit consumes it once; a trapped scope consumes it
at most once. Local events are then hidden only from the outer trace. -/
theorem bound_finished (h : (Control.bind b).demand r = some n)
    (run : Finishes b xs) : xs.count 0 = 1 := run.count_eq (bind_demand h).1

theorem bound_prefix (h : (Control.bind b).demand r = some n)
    (run : Prefix b xs) : xs.count 0 ≤ 1 := run.count_le (bind_demand h).1

/-- Erased binders cannot occur even in a trapped runtime prefix. Unlike an
unrestricted slot, they require zero local demand before scope discharge. -/
theorem erased_bound_prefix (h : (Control.scope .erased b).demand r = some n)
    (run : Prefix b xs) : xs.count 0 = 0 :=
  Nat.eq_zero_of_le_zero (run.count_le (scope_erased h))

/-- Simultaneous independent-resource guarantee. Quantities are not collapsed
into a total count that could hide duplication of one and loss of another. -/
def Linear (resources : List Nat) (c : Control) : Prop :=
  ∀ r ∈ resources, c.demand r = some 1

theorem Linear.finished (h : Linear resources c) (run : Finishes c xs) :
    ∀ r ∈ resources, xs.count r = 1 := fun r hr => run.count_eq (h r hr)

theorem Linear.prefix (h : Linear resources c) (run : Prefix c xs) :
    ∀ r ∈ resources, xs.count r ≤ 1 := fun r hr => run.count_le (h r hr)

/-- Zero checked demand excludes even a single runtime use on a partial run. -/
theorem erased_unreachable (h : c.demand r = some 0) (run : Prefix c xs) : r ∉ xs := by
  have hz := run.count_le h
  have : xs.count r = 0 := Nat.eq_zero_of_le_zero hz
  exact List.count_eq_zero.mp this

end Jihoo.Quantity
