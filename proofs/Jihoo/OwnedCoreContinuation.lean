import Jihoo.LinearCoreCallers

/-! Declarative ownership rules on original Core graph nodes. The continuation
slice has literal scalar return, direct free, and allocation binding. There is
no accepted-callee or safe-trace premise. This is not whole-Core typing. -/
namespace Jihoo.OwnedCoreContinuation
open HeapLeases ScopedLend LinearHeapPrograms LinearCoreCallers

inductive Allocation (g : Graph.Graph) (root value body : Nat) : Prop where
  | intro (function argument domain length payload : Nat) :
      Graph.nodeAt g root = .app function argument →
      Graph.nodeAt g function = .lam false domain body →
      Graph.bufferOne g domain = true →
      Graph.nodeAt g argument = .alloc length payload →
      Graph.nodeAt g length = .natural 1 →
      Graph.nodeAt g payload = .integer value → Allocation g root value body

theorem Allocation.unique (a : Allocation g root v b) (a' : Allocation g root v' b') :
    v = v' ∧ b = b' := by
  obtain ⟨f, arg, d, l, p, h, hf, hd, ha, hl, hp⟩ := a
  obtain ⟨f', arg', d', l', p', h', hf', hd', ha', hl', hp'⟩ := a'
  have eq := h.symm.trans h'; cases eq
  have eq := hf.symm.trans hf'; cases eq
  have eq := ha.symm.trans ha'; cases eq
  have eq := hp.symm.trans hp'; cases eq
  exact ⟨rfl, rfl⟩

inductive Typed (g : Graph.Graph) : Context → Nat → Nat → Prop where
  | finish : Graph.nodeAt g root = .integer value → value < 2^63 → Typed g ctx 0 root
  | free : Graph.nodeAt g root = .free owner body → ownerSlot g ctx owner = some slot →
      slot < n → Typed g (consumed slot ctx) (n - 1) body → Typed g ctx n root
  | allocate : Allocation g root value body → value < 2^63 →
      Typed g (fresh ctx) (n + 1) body → Typed g ctx n root

def freedState (s : State) (x : Nat) : State := { s with live := put s.live x false }

inductive Runs (g : Graph.Graph) : Context → Nat → List Nat → State → Nat → List Event → State → Prop where
  | finish : Graph.nodeAt g root = .integer value → Runs g ctx root owners s value [] s
  | free : Graph.nodeAt g root = .free owner body → ownerSlot g ctx owner = some slot →
      Select owners slot x rest → Runs g (consumed slot ctx) body rest (freedState s x) value events t →
      Runs g ctx root owners s value (.free x :: events) t
  | allocate : Allocation g root payload body →
      Runs g (fresh ctx) body (s.nextObject :: owners) (allocatedState s payload) value events t →
      Runs g ctx root owners s value (.alloc s.nextObject payload :: events) t

theorem free_owns (owned : Owns s owners) (selected : Select owners slot x rest) :
    Owns (freedState s x) rest := by
  obtain ⟨distinct, absent⟩ := selected.unique owned.distinct
  refine ⟨distinct, ?_, ?_⟩
  · intro y hy
    have ne : y ≠ x := fun eq => absent (eq ▸ hy)
    simp [freedState, put, ne, owned.live y (selected.subset y hy)]
  · intro y hy
    exact owned.leaseFree y (selected.subset y hy)

theorem total (typed : Typed g ctx n root) (length : owners.length = n)
    (valid : Valid s) (owned : Owns s owners) :
    ∃ value events t, Runs g ctx root owners s value events t := by
  induction typed generalizing owners s with
  | finish shape bound =>
      have : owners = [] := List.length_eq_zero_iff.mp length
      subst owners
      exact ⟨_, [], s, .finish shape⟩
  | free shape resolved bound typed ih =>
      have bound' := bound
      rw [← length] at bound'
      obtain ⟨x, rest, selected⟩ := select_total bound'
      have step : Step s (.free x) (freedState s x) :=
        .free (owned.live x selected.member) (owned.leaseFree x selected.member)
      obtain ⟨v, es, t, run⟩ := ih (by have := selected.length; omega)
        (step_valid valid step) (free_owns owned selected)
      exact ⟨v, _, t, .free shape resolved selected run⟩
  | allocate shape bound typed ih =>
      obtain ⟨v, es, t, run⟩ := ih (by simp [length])
        (step_valid valid (Step.alloc (value := _))) (allocate_owns valid owned)
      exact ⟨v, _, t, .allocate shape run⟩

private theorem Allocation.application (a : Allocation g root v b) :
    ∃ f x, Graph.nodeAt g root = .app f x := by
  cases a with | intro f x _ _ _ h _ _ _ _ _ => exact ⟨f, x, h⟩

theorem execution_safe (typed : Typed g ctx n root) (length : owners.length = n)
    (valid : Valid s) (owned : Owns s owners) (run : Runs g ctx root owners s v es t) :
    Steps s es t ∧ Valid t ∧ Owns t [] := by
  induction typed generalizing owners s v es t with
  | finish shape bound =>
      cases run with
      | finish _ => exact ⟨.nil, valid, ⟨by simp, by simp, by simp⟩⟩
      | free other _ _ _ => have := shape.symm.trans other; contradiction
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; have := shape.symm.trans other; contradiction
  | free shape resolved bound typed ih =>
      cases run with
      | finish other => have := shape.symm.trans other; contradiction
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; have := shape.symm.trans other; contradiction
      | free other resolved' selected restRun =>
          have eq := shape.symm.trans other; cases eq
          have eq := resolved.symm.trans resolved'; cases eq
          have step := Step.free (owned.live _ selected.member) (owned.leaseFree _ selected.member)
          obtain ⟨steps, vt, ot⟩ := ih (by have := selected.length; omega)
            (step_valid valid step) (free_owns owned selected) restRun
          exact ⟨.cons step steps, vt, ot⟩
  | allocate a bound typed ih =>
      cases run with
      | finish other => obtain ⟨f, x, shape⟩ := a.application; have := shape.symm.trans other; contradiction
      | free other _ _ _ => obtain ⟨f, x, shape⟩ := a.application; have := shape.symm.trans other; contradiction
      | allocate a' restRun =>
          obtain ⟨rfl, rfl⟩ := a.unique a'
          obtain ⟨steps, vt, ot⟩ := ih (by simp [length])
            (step_valid valid (Step.alloc (value := _))) (allocate_owns valid owned) restRun
          exact ⟨.cons .alloc steps, vt, ot⟩

/-- Accounting follows the original graph execution, including allocations
inside the continuation, rather than a separately supplied usage trace. -/
theorem release_conservation (typed : Typed g ctx n root) (length : owners.length = n)
    (run : Runs g ctx root owners s v es t) (x : Nat) :
    (released es).count x = owners.count x + (allocations es).count x := by
  induction typed generalizing owners s v es t with
  | finish shape bound =>
      cases run with
      | finish _ =>
          have : owners = [] := List.length_eq_zero_iff.mp length
          subst owners
          simp [released, allocations]
      | free other _ _ _ => have := shape.symm.trans other; contradiction
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; have := shape.symm.trans other; contradiction
  | free shape resolved bound typed ih =>
      cases run with
      | finish other => have := shape.symm.trans other; contradiction
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; have := shape.symm.trans other; contradiction
      | free other resolved' selected restRun =>
          have eq := shape.symm.trans other; cases eq
          have eq := resolved.symm.trans resolved'; cases eq
          have h := selected.count x
          have hr := ih (by have := selected.length; omega) restRun
          simp only [released, allocations, List.filterMap_cons, List.count_cons] at *
          simp only [beq_iff_eq] at *
          omega
  | allocate a bound typed ih =>
      cases run with
      | finish other => obtain ⟨f, x, shape⟩ := a.application; have := shape.symm.trans other; contradiction
      | free other _ _ _ => obtain ⟨f, x, shape⟩ := a.application; have := shape.symm.trans other; contradiction
      | allocate a' restRun =>
          obtain ⟨rfl, rfl⟩ := a.unique a'
          have hr := ih (by simp [length]) restRun
          simp only [released, allocations, List.filterMap_cons, List.count_cons] at *
          omega

theorem no_tracked_leaks (typed : Typed g ctx n root) (length : owners.length = n)
    (valid : Valid s) (owned : Owns s owners) (run : Runs g ctx root owners s v es t)
    (tracked : x ∈ owners ∨ x ∈ allocations es) :
    (released es).count x = 1 ∧ t.live x = false := by
  have steps := (execution_safe typed length valid owned run).1
  have conserved := release_conservation typed length run x
  have positive : 0 < (released es).count x := by
    rcases tracked with initial | allocated
    · have := List.count_pos_iff.mpr initial; omega
    · have := List.count_pos_iff.mpr allocated; omega
  have member := List.count_pos_iff.mp positive
  have count := (releases_distinct valid steps).count (a := x)
  exact ⟨by simpa [member] using count, released_dead valid steps (released_mem.mp member)⟩

/-- Neither allocation nor free changes an ambient lease or its counter. -/
theorem lease_frame (run : Runs g ctx root owners s v es t) :
    t.lease = s.lease ∧ t.nextLease = s.nextLease := by
  induction run with
  | finish => exact ⟨rfl, rfl⟩
  | free _ _ _ _ ih => exact ih
  | allocate _ _ ih => exact ih

/-- If the initial capability environment covers every live object, every
final object is dead. Ambient objects outside that environment are not owned. -/
theorem heap_empty (typed : Typed g ctx n root) (length : owners.length = n)
    (valid : Valid s) (owned : Owns s owners) (run : Runs g ctx root owners s v es t)
    (coverage : ∀ x, s.live x = true → x ∈ owners) : ∀ x, t.live x = false := by
  intro x
  cases live : t.live x with
  | false => rfl
  | true =>
      have steps := (execution_safe typed length valid owned run).1
      have origin := live_origin steps live
      have tracked : x ∈ owners ∨ x ∈ allocations es := by
        rcases origin with initial | allocated
        · exact Or.inl (coverage x initial)
        · exact Or.inr allocated
      have dead := (no_tracked_leaks typed length valid owned run tracked).2
      rw [live] at dead
      contradiction

theorem Typed.free_inversion (typed : Typed g ctx n root)
    (shape : Graph.nodeAt g root = .free owner body) :
    ∃ slot, ownerSlot g ctx owner = some slot ∧ slot < n ∧
      Typed g (consumed slot ctx) (n - 1) body := by
  cases typed with
  | finish other _ => have := shape.symm.trans other; contradiction
  | free other resolved bound rest =>
      have eq := shape.symm.trans other; cases eq
      exact ⟨_, resolved, bound, rest⟩
  | allocate a _ _ =>
      obtain ⟨f, x, other⟩ := a.application
      have := shape.symm.trans other; contradiction

theorem Typed.finish_inversion (typed : Typed g ctx n root)
    (shape : Graph.nodeAt g root = .integer value) : n = 0 ∧ value < 2^63 := by
  cases typed with
  | finish other bound =>
      have eq := shape.symm.trans other; cases eq
      exact ⟨rfl, bound⟩
  | free other _ _ _ => have := shape.symm.trans other; contradiction
  | allocate a _ _ =>
      obtain ⟨f, x, other⟩ := a.application
      have := shape.symm.trans other; contradiction

/-- A consumed lexical name cannot be freed again, including a second alias
of the same original capability. -/
theorem dead_owner_rejected (shape : Graph.nodeAt g root = .free owner body)
    (dead : ownerSlot g ctx owner = none) : ¬ Typed g ctx n root := by
  intro typed
  obtain ⟨slot, resolved, _⟩ := typed.free_inversion shape
  rw [dead] at resolved
  contradiction

end Jihoo.OwnedCoreContinuation
