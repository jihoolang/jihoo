import Jihoo.ScopedLendGraph

/-! Linear capability contexts for finite allocation/call sequencing.
Calls execute admitted original scalar-Lend constructor graphs. The context
tracks allocation identities, not arbitrary scalar values or raw addresses.
No-leak claims cover initial capabilities and allocations of this program;
ambient untracked heap objects are not declared owned by this context. -/
namespace Jihoo.LinearHeapPrograms
open HeapLeases ScopedLend

structure Owns (s : State) (owners : List Nat) : Prop where
  distinct : owners.Nodup
  live : ∀ x ∈ owners, s.live x = true
  leaseFree : ∀ x ∈ owners, Unborrowed s x

inductive Select : List Nat → Nat → Nat → List Nat → Prop where
  | here : Select (x :: xs) 0 x xs
  | there : Select xs k x rest → Select (y :: xs) (k + 1) x (y :: rest)

theorem Select.member (h : Select xs k x rest) : x ∈ xs := by
  induction h with
  | here => simp
  | there _ ih => exact List.mem_cons_of_mem _ ih

theorem Select.subset (h : Select xs k x rest) : ∀ y ∈ rest, y ∈ xs := by
  induction h with
  | here => intro y hy; exact List.mem_cons_of_mem _ hy
  | there _ ih =>
    intro z hz
    simp only [List.mem_cons] at *
    rcases hz with rfl | hz
    · exact Or.inl rfl
    · exact Or.inr (ih _ hz)

theorem Select.unique (h : Select xs k x rest) (distinct : xs.Nodup) :
    rest.Nodup ∧ x ∉ rest := by
  induction h with
  | here => exact ⟨(List.nodup_cons.mp distinct).2, (List.nodup_cons.mp distinct).1⟩
  | there h ih =>
    obtain ⟨hy, ht⟩ := List.nodup_cons.mp distinct
    obtain ⟨hr, hx⟩ := ih ht
    refine ⟨List.nodup_cons.mpr ⟨fun hm => hy (h.subset _ hm), hr⟩, ?_⟩
    simp only [List.mem_cons, not_or]
    exact ⟨fun eq => hy (eq ▸ h.member), hx⟩

theorem Select.length (h : Select xs k x rest) : rest.length + 1 = xs.length := by
  induction h <;> simp_all

theorem Select.count (h : Select xs k x rest) (y : Nat) :
    xs.count y = (if x = y then 1 else 0) + rest.count y := by
  induction h with
  | here => simp [List.count_cons, Nat.add_comm]
  | there _ ih => simp [List.count_cons, ih]; omega

theorem select_total (bound : k < xs.length) : ∃ x rest, Select xs k x rest := by
  induction xs generalizing k with
  | nil => simp at bound
  | cons y ys ih =>
    cases k with
    | zero => exact ⟨y, ys, .here⟩
    | succ k =>
      obtain ⟨x, rest, h⟩ := ih (by simpa using bound)
      exact ⟨x, y :: rest, .there h⟩

def allocatedState (s : State) (v : Nat) : State :=
  { s with nextObject := s.nextObject + 1, live := put s.live s.nextObject true, payload := put s.payload s.nextObject v }

theorem allocate_owns (valid : Valid s) (owned : Owns s owners) :
    Owns (allocatedState s v) (s.nextObject :: owners) := by
  have fresh : s.nextObject ∉ owners := by
    intro member
    have := valid.allocated _ (owned.live _ member)
    omega
  constructor
  · exact List.nodup_cons.mpr ⟨fresh, owned.distinct⟩
  · intro x member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · simp [allocatedState, put]
    · simp [allocatedState, put, owned.live _ member]
  · intro x member l lease
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · have := valid.allocated _ (valid.leased _ _ lease).2
      omega
    · exact owned.leaseFree _ member l lease

/-- Consumption preserves every other capability and all ambient lease tokens.
No assumed post-call heap invariant is supplied by the caller. -/
theorem consume_owns (owned : Owns s owners) (selected : Select owners slot x rest) :
    Owns (finalState s x v k) rest := by
  obtain ⟨distinct, absent⟩ := selected.unique owned.distinct
  constructor
  · exact distinct
  · intro y member
    have ne : y ≠ x := fun eq => absent (eq ▸ member)
    have live := owned.live _ (selected.subset _ member)
    cases k <;> simp [finalState, restored, put, ne, live]
  · intro y member
    cases k <;> exact owned.leaseFree _ (selected.subset _ member)

inductive Program where
  | done
  | allocate (value : Nat) (body : Program)
  | call (slot : Nat) (graph : Graph.Graph) (root type : Nat) (next : Program)

/-- The resource count is threaded linearly: allocation adds a fresh slot,
every consuming callee removes one, and only an empty context may terminate. -/
inductive Checked : Nat → Program → Prop where
  | done : Checked 0 .done
  | allocate : Checked (n + 1) body → Checked n (.allocate v body)
  | call : slot < n → Graph.Accepted graph root type → Checked (n - 1) next →
      Checked n (.call slot graph root type next)

def check (n : Nat) : Program → Bool
  | .done => n == 0
  | .allocate _ body => check (n + 1) body
  | .call slot graph root type next => slot < n && (Graph.admit graph root type).isSome && check (n - 1) next

theorem check_sound (h : check n p = true) : Checked n p := by
  induction p generalizing n with
  | done => simp [check] at h; subst n; exact .done
  | allocate v body ih => exact .allocate (ih h)
  | call slot graph root type next ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨bound, admitted⟩, rest⟩ := h
    cases ha : Graph.admit graph root type with
    | none => simp [ha] at admitted
    | some a => exact .call bound a (ih rest)

inductive Runs : Program → List Nat → State → List Event → State → Prop where
  | done : Runs .done [] s [] s
  | allocate : Runs body (s.nextObject :: owners) (allocatedState s v) events t →
      Runs (.allocate v body) owners s (.alloc s.nextObject v :: events) t
  | call : Select owners slot x rest → Graph.CoreRuns graph root type s x v first middle →
      Runs next rest middle second t →
      Runs (.call slot graph root type next) owners s (first ++ second) t

/-- Entry guards of admitted Core callees follow from the capability context. -/
theorem call_owns (valid : Valid s) (owned : Owns s owners)
    (selected : Select owners slot x rest) (a : Graph.Accepted graph root type)
    (run : Graph.CoreRuns graph root type s x v events t) :
    Steps s events t ∧ Valid t ∧ Owns t rest := by
  have source := Graph.accepted_reflect a run
  have safe := Graph.accepted_all_runs a valid (owned.live _ selected.member)
    (owned.leaseFree _ selected.member) run
  refine ⟨safe.1, safe.2.1, ?_⟩
  cases source
  exact consume_owns owned selected

/-- Finite checked programs have a complete execution in the successful-
allocation model. Resource ownership and borrow guards cannot cause a fault. -/
theorem total (checked : Checked n p) (length : owners.length = n)
    (valid : Valid s) (owned : Owns s owners) : ∃ events t, Runs p owners s events t := by
  induction checked generalizing owners s with
  | done =>
    have : owners = [] := List.length_eq_zero_iff.mp length
    subst owners
    exact ⟨[], s, .done⟩
  | @allocate n body v _ ih =>
    obtain ⟨events, t, run⟩ := ih (owners := s.nextObject :: owners) (s := allocatedState s v) (by simp [length]) (step_valid valid Step.alloc)
      (allocate_owns valid owned)
    exact ⟨_, t, .allocate run⟩
  | call bound a _ ih =>
    have kbound := bound
    rw [← length] at kbound
    obtain ⟨x, rest, selected⟩ := select_total kbound
    obtain ⟨v, events, middle, run, _, _, _, _⟩ := Graph.accepted_execution a valid
      (owned.live _ selected.member) (owned.leaseFree _ selected.member)
    obtain ⟨_, nextValid, nextOwns⟩ := call_owns valid owned selected a run
    obtain ⟨tail, t, next⟩ := ih (by have := selected.length; omega) nextValid nextOwns
    exact ⟨_, t, .call selected run next⟩

/-- Safety for every program execution, not just the totality witness. -/
theorem execution_safe (checked : Checked n p) (length : owners.length = n)
    (valid : Valid s) (owned : Owns s owners) (run : Runs p owners s events t) :
    Steps s events t ∧ Valid t := by
  induction checked generalizing owners s events t with
  | done => cases run; exact ⟨.nil, valid⟩
  | @allocate n body v _ ih =>
    cases run with
    | allocate body =>
      obtain ⟨steps, finalValid⟩ := ih (owners := s.nextObject :: owners) (s := allocatedState s v) (by simp [length]) (step_valid valid Step.alloc)
        (allocate_owns valid owned) body
      exact ⟨.cons .alloc steps, finalValid⟩
  | call bound a _ ih =>
    cases run with
    | call selected first second =>
      obtain ⟨prefixSteps, middleValid, middleOwns⟩ := call_owns valid owned selected a first
      obtain ⟨suffix, finalValid⟩ := ih (by have := selected.length; omega) middleValid middleOwns second
      exact ⟨steps_append prefixSteps suffix, finalValid⟩

def allocations (events : List Event) : List Nat :=
  events.filterMap fun e => match e with | .alloc x _ => some x | _ => none

theorem allocations_append : allocations (xs ++ ys) = allocations xs ++ allocations ys := by
  simp [allocations, List.filterMap_append]

theorem releases_append : released (xs ++ ys) = released xs ++ released ys := by
  simp [released, List.filterMap_append]

theorem reader_allocations (run : Reads s env r v events) : allocations events = [] := by
  induction run with
  | scalar | read => rfl
  | seq _ _ ia ib => rw [allocations_append, ia, ib]; rfl
  | yes _ ih | no _ ih => exact ih

theorem call_allocations (a : Graph.Accepted graph root type)
    (run : Graph.CoreRuns graph root type s owner v events t) : allocations events = [] := by
  have source := Graph.accepted_reflect a run
  cases source with
  | lend reads =>
    have hr := reader_allocations reads
    cases a.next <;> simp_all [allocations, continuationEvents]

/-- Conservation is about concrete allocation IDs, not merely context length.
It explicitly accounts for initial capabilities and every internal allocation. -/
theorem release_conservation (checked : Checked n p) (run : Runs p owners s events t) (x : Nat) :
    (released events).count x = owners.count x + (allocations events).count x := by
  induction checked generalizing owners s events t with
  | done => cases run; rfl
  | allocate _ ih =>
    cases run with
    | allocate body =>
      have h := ih body
      simp only [released, allocations, List.filterMap_cons, List.count_cons] at *
      omega
  | call _ a _ ih =>
    cases run with
    | call selected first second =>
      have hf := execution_releases (Graph.accepted_reflect a first)
      have ha := call_allocations a first
      have hs := selected.count x
      have ht := ih second
      rw [releases_append, allocations_append, hf, ha]
      simp only [List.count_append, List.nil_append, List.count_cons, List.count_nil] at *
      simp only [beq_iff_eq] at *
      omega

/-- Once dead, an old identity has no later free event; allocation cannot
resurrect it. This statement covers arbitrary valid primitive prefixes. -/
theorem dead_not_released (old : x < s.nextObject) (dead : s.live x = false)
    (run : Steps s events t) : Event.free x ∉ events := by
  induction run with
  | nil => simp
  | cons step tail ih =>
    obtain ⟨ho, hd⟩ := dead_step old dead step
    have rest := ih ho hd
    simp only [List.mem_cons, not_or]
    refine ⟨?_, rest⟩
    intro eq
    subst eq
    cases step with
    | free live _ => simp [dead] at live

theorem releases_distinct (valid : Valid s) (run : Steps s events t) : (released events).Nodup := by
  induction run with
  | nil => simp [released]
  | @cons start event middle events finish step tail ih =>
    have rest := ih (step_valid valid step)
    cases step <;> try exact rest
    case free owner live noLease =>
      apply List.nodup_cons.mpr
      refine ⟨?_, rest⟩
      intro member
      have forbidden := dead_not_released (s := { start with live := put start.live owner false })
        (valid.allocated _ live) (by simp [put]) tail
      exact forbidden (released_mem.mp member)

/-- No leaks of tracked resources on completed executions: every initially
owned or internally allocated object is freed exactly once and is dead. Ambient
objects outside this set are deliberately not claimed to belong to the program. -/
theorem no_tracked_leaks (checked : Checked n p) (length : owners.length = n)
    (valid : Valid s) (owned : Owns s owners) (run : Runs p owners s events t)
    (tracked : x ∈ owners ∨ x ∈ allocations events) :
    (released events).count x = 1 ∧ t.live x = false := by
  have steps := (execution_safe checked length valid owned run).1
  have conserved := release_conservation checked run x
  have positive : 0 < (released events).count x := by
    rcases tracked with initial | allocated
    · have := List.count_pos_iff.mpr initial; omega
    · have := List.count_pos_iff.mpr allocated; omega
  have member := List.count_pos_iff.mp positive
  have count := (releases_distinct valid steps).count (a := x)
  exact ⟨by simpa [member] using count, released_dead valid steps (released_mem.mp member)⟩

/-- Every call restores ambient leases, so composition does not silently
invalidate an unrelated lender's token. -/
theorem lease_frame (checked : Checked n p) (run : Runs p owners s events t) : t.lease = s.lease := by
  induction checked generalizing owners s events t with
  | done => cases run; rfl
  | allocate _ ih => cases run with
    | allocate body =>
      have h := ih body
      exact h
  | call _ a _ ih => cases run with
    | call _ first second =>
      exact (ih second).trans (execution_lease_frame (Graph.accepted_reflect a first)).1

theorem empty_owns : Owns empty [] := ⟨by simp, by simp, by simp⟩

/-- Closed programs manufacture all capabilities through fresh allocation,
so no live/no-lease/uniqueness assumptions are supplied by an external caller. -/
theorem closed_total (checked : Checked 0 p) : ∃ events t, Runs p [] empty events t :=
  total checked rfl empty_valid empty_owns

theorem closed_safety (checked : Checked 0 p) (run : Runs p [] empty events t) :
    Steps empty events t ∧ Valid t ∧ t.lease = empty.lease ∧
    ∀ x ∈ allocations events, (released events).count x = 1 ∧ t.live x = false := by
  obtain ⟨steps, valid⟩ := execution_safe checked rfl empty_valid empty_owns run
  refine ⟨steps, valid, lease_frame checked run, ?_⟩
  intro x member
  exact no_tracked_leaks checked rfl empty_valid empty_owns run (Or.inr member)

/-- Primitive execution cannot invent live heap identities without an
allocation event. This supplies the coverage needed for a closed no-leak claim. -/
theorem live_origin (run : Steps s events t) (live : t.live x = true) :
    s.live x = true ∨ x ∈ allocations events := by
  induction run with
  | nil => exact Or.inl live
  | @cons start event middle events finish step tail ih =>
    rcases ih live with before | allocated
    · cases step <;> try exact Or.inl before
      case alloc value =>
        by_cases eq : x = start.nextObject
        · subst x; exact Or.inr (by simp [allocations])
        · exact Or.inl (by simpa [put, eq] using before)
      case free owner _ _ =>
        simp only [put] at before
        split at before
        · contradiction
        · exact Or.inl before
    · exact Or.inr (by cases event <;> simp_all [allocations])

/-- Starting from the empty heap, every live identity would have to come from
this program's allocations, all of which are released. No coverage assumption
or claim about unrelated ambient heaps is needed for this closed endpoint. -/
theorem closed_heap_empty (checked : Checked 0 p) (run : Runs p [] empty events t) :
    ∀ x, t.live x = false := by
  intro x
  cases h : t.live x with
  | false => rfl
  | true =>
    have safe := closed_safety checked run
    rcases live_origin safe.1 h with initial | allocated
    · simp [empty] at initial
    · have dead := (safe.2.2.2 x allocated).2
      simp [h] at dead

end Jihoo.LinearHeapPrograms
