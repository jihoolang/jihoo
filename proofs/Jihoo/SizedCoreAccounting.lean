import Jihoo.SizedCoreSafety

namespace Jihoo.SizedCoreTyping
open ScopedLend SizedBufferContext SizedCoreExecution LinearHeapPrograms

def resultOwners : Value → List Nat
  | .owner x => [x]
  | _ => []

def Account (owners : List Nat) (value : Value) (events : List SizedBufferHeap.Event) : Prop :=
  ∀ x, (HeapLeases.released (events.map SizedBufferHeap.Event.project)).count x +
    (resultOwners value).count x = owners.count x +
      (allocations (events.map SizedBufferHeap.Event.project)).count x

theorem Account.allocate (h : Account (objectId :: owners) value events) :
    Account owners value (.alloc objectId n fill :: events) := by
  intro x
  have eq := h x
  simp only [List.map_cons, SizedBufferHeap.Event.project, HeapLeases.released,
    allocations, List.filterMap_cons, List.count_cons] at eq ⊢
  simp only [beq_iff_eq] at *
  omega

theorem Account.free (h : Account rest value events) (selected : Select owners slot object rest) :
    Account owners value (.free object :: events) := by
  intro x
  have eq := h x
  have count := selected.count x
  simp only [List.map_cons, SizedBufferHeap.Event.project, HeapLeases.released,
    allocations, List.filterMap_cons, List.count_cons] at eq ⊢
  simp only [beq_iff_eq] at *
  omega

theorem Account.lend (h : Account owners value events) :
    Account owners value ([.beginLease token object, .read token i copied, .close token] ++ events) := by
  simpa [Account, List.map_append, HeapLeases.released, allocations,
    List.filterMap_append, SizedBufferHeap.Event.project] using h

private theorem steps_append (a : SizedBufferHeap.Steps s es t)
    (b : SizedBufferHeap.Steps t fs u) : SizedBufferHeap.Steps s (es ++ fs) u := by
  induction a with
  | nil => exact b
  | cons step _ ih => exact .cons step (ih b)

theorem Typing.total_accounted (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap owners) :
    ∃ value events t, Eval g env root s value events t ∧
      SizedBufferHeap.Steps s events t ∧ SizedBufferHeap.Valid t ∧ Post kind t value ∧ Account owners value events := by
  induction typed generalizing env owners s with
  | literal shape bound =>
      have empty : owners = [] := List.eq_nil_of_length_eq_zero (by simpa using layout.length)
      subst owners
      exact ⟨_, [], s, .scalar shape, .nil, valid, trivial, by simp [Account, resultOwners, HeapLeases.released, allocations]⟩
  | scalar shape lookup =>
      obtain ⟨v, hv⟩ := agree.scalar_lookup _ lookup
      have empty : owners = [] := List.eq_nil_of_length_eq_zero (by simpa using layout.length)
      subst owners
      exact ⟨_, [], s, .var shape hv, .nil, valid, trivial, by simp [Account, resultOwners, HeapLeases.released, allocations]⟩
  | owner shape lookup =>
      obtain ⟨x, hx, he⟩ := agree.owner_lookup _ _ lookup
      obtain ⟨rfl, length⟩ := layout.owner_result hx
      exact ⟨_, [], s, .var shape he, .nil, valid, ⟨owned, length⟩, by simp [Account, resultOwners, HeapLeases.released, allocations]⟩
  | naturalLet shape lam domain argument body ih =>
      have argumentRun := argument.transport (fun _ _ h => agree.nats_transport h)
      obtain ⟨v, es, t, run, steps, vt, post, account⟩ := ih agree.bindNat layout valid owned
      exact ⟨v, es, t, by simpa using Eval.app shape lam (index_simulation argumentRun) run,
        steps, vt, post, account⟩
  | @allocate rt f arg dom bod Γ n len init ns kind shape lam annotation alloc length initial body ih =>
      obtain ⟨fill, initRun⟩ := initial.total agree
      have lengthRun := length.transport (fun _ _ h => agree.nats_transport h)
      have step : SizedBufferHeap.Step s (.alloc s.heap.nextObject n fill)
          (SizedBufferHeap.allocate s n fill) := .alloc
      have owns := SizedBufferHeap.allocate_owns (n := n) (v := fill) valid owned
      obtain ⟨v, es, t, run, steps, vt, post, account⟩ :=
        ih agree.fresh (layout.allocate valid owned) (SizedBufferHeap.step_valid valid step) owns
      exact ⟨v, _, t, .app shape lam (.allocate alloc lengthRun initRun) run,
        .cons step steps, vt, post, account.allocate⟩
  | @allocation rt len init Γ n alloc length initial =>
      obtain ⟨fill, initRun⟩ := initial.total agree
      have lengthRun := length.transport (fun _ _ h => agree.nats_transport h)
      have empty : owners = [] := List.eq_nil_of_length_eq_zero (by simpa using layout.length)
      subst owners
      have step : SizedBufferHeap.Step s (.alloc s.heap.nextObject n fill)
          (SizedBufferHeap.allocate s n fill) := .alloc
      refine ⟨_, _, _, .allocate alloc lengthRun initRun, .cons step .nil,
        SizedBufferHeap.step_valid valid step, ⟨SizedBufferHeap.allocate_owns valid owned, ?_⟩, ?_⟩
      · simp [SizedBufferHeap.allocate, HeapLeases.put]
      · simp [Account, resultOwners, HeapLeases.released, allocations, SizedBufferHeap.Event.project]
  | free shape variableShape lookup bound body ih =>
      obtain ⟨x, hx, he⟩ := agree.owner_lookup _ _ lookup
      obtain ⟨selected, rest, selection⟩ := select_total (xs := owners) (by rw [layout.length]; exact bound)
      have eq := (LinearCoreCallers.Select.lookup_selected selection).symm.trans hx
      have same : selected = x := Option.some.inj eq
      subst selected
      have step : SizedBufferHeap.Step s (.free x) (SizedBufferHeap.release s x) :=
        .free (owned.live x selection.member) (owned.leaseFree x selection.member)
      obtain ⟨v, es, t, run, steps, vt, post, account⟩ := ih (agree.consumed selection)
        (layout.consumed selection) (SizedBufferHeap.step_valid valid step)
        (SizedBufferHeap.release_owns owned selection)
      exact ⟨v, _, t, .free shape variableShape he run, .cons step steps, vt, post, account.free selection⟩
  | @branch rt l r y noRoot Γ a b ns kind shape left right yes no iy ino =>
      have leftRun := left.transport (fun _ _ h => agree.nats_transport h)
      have rightRun := right.transport (fun _ _ h => agree.nats_transport h)
      by_cases h : a < b
      · obtain ⟨v, es, t, run, steps, vt, post, account⟩ := iy h agree.bound layout valid owned
        exact ⟨v, es, t, .yes shape leftRun rightRun h run, steps, vt, post, account⟩
      · obtain ⟨v, es, t, run, steps, vt, post, account⟩ := ino h agree layout valid owned
        exact ⟨v, es, t, .no shape leftRun rightRun h run, steps, vt, post, account⟩
  | @lend rt own ref idx proof ownTy bod k Γ ns slot n i kind shape variableShape lookup size refTy ownerTy index evidence body ih =>
      obtain ⟨x, hx, he⟩ := agree.owner_lookup _ _ lookup
      have length := layout.lookup _ _ _ hx size
      have bound : i < s.length x := by rw [length]; exact evidence.sound
      have indexRun := index.transport (fun _ _ h => (agree.dead (value := .borrow x)).nats_transport h)
      have slotBound : slot < owners.length := by
        by_cases h : slot < owners.length
        · exact h
        · have missing := List.getElem?_eq_none (l := owners) (by omega : owners.length ≤ slot)
          rw [hx] at missing
          contradiction
      obtain ⟨y, rest, selected⟩ := select_total (xs := owners) slotBound
      have eq := (LinearCoreCallers.Select.lookup_selected selected).symm.trans hx
      have same : y = x := Option.some.inj eq
      subst y
      have member : x ∈ owners := selected.member
      have cycle := SizedBufferHeap.read_cycle valid (owned.live x member) bound
      obtain ⟨v, es, t, run, steps, vt, post, account⟩ := ih (s := SizedBufferHeap.restore s)
        (agree.scalarReturned selected) ⟨layout.length, layout.lookup⟩
        (SizedBufferHeap.steps_valid valid cycle) (SizedBufferHeap.restored_owns owned)
      exact ⟨v, _, t, .lend shape variableShape he indexRun run, steps_append cycle steps, vt, post, account.lend⟩


theorem Typing.every_run_accounted (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap owners)
    (run : Eval g env root s value events t) : Account owners value events := by
  obtain ⟨v, es, u, canonical, _, _, _, account⟩ := typed.total_accounted agree layout valid owned
  obtain ⟨rfl, rfl, rfl⟩ := run.deterministic canonical
  exact account

/-- Every consumed initial or newly allocated identity is actually released
exactly once; equal fill values cannot identify two distinct allocations. -/
theorem Typing.other_released (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap owners)
    (run : Eval g env root s value events t)
    (tracked : x ∈ owners ∨ x ∈ allocations (events.map SizedBufferHeap.Event.project))
    (notReturned : x ∉ resultOwners value) :
    (HeapLeases.released (events.map SizedBufferHeap.Event.project)).count x = 1 ∧ t.heap.live x = false := by
  have safe := typed.lifecycle_projection agree layout valid owned run
  have eq := typed.every_run_accounted agree layout valid owned run x
  have absent := List.count_eq_zero.mpr notReturned
  rw [absent, Nat.add_zero] at eq
  have positive : 0 < (HeapLeases.released (events.map SizedBufferHeap.Event.project)).count x := by
    rcases tracked with initial | allocated
    · have := List.count_pos_iff.mpr initial; omega
    · have := List.count_pos_iff.mpr allocated; omega
  have member := List.count_pos_iff.mp positive
  have count := (releases_distinct valid safe).count (a := x)
  exact ⟨by simpa [member] using count,
    HeapLeases.released_dead valid safe (HeapLeases.released_mem.mp member)⟩

theorem Post.result_live (post : Post kind s value) (member : x ∈ resultOwners value) :
    s.heap.live x = true := by
  cases kind <;> cases value <;> simp [Post, resultOwners] at post member
  case owner.owner n y =>
    subst x
    exact post.1.live y (by simp)

/-- With initial heap coverage, the live final heap consists exactly of the
returned capability. Ambient untracked objects are not silently included. -/
theorem Typing.heap_accounted (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap owners)
    (run : Eval g env root s value events t)
    (coverage : ∀ x, s.heap.live x = true → x ∈ owners) :
    ∀ x, t.heap.live x = true ↔ x ∈ resultOwners value := by
  intro x
  constructor
  · intro live
    by_cases returned : x ∈ resultOwners value
    · exact returned
    have safe := typed.lifecycle_projection agree layout valid owned run
    have origin := live_origin safe live
    have tracked : x ∈ owners ∨ x ∈ allocations (events.map SizedBufferHeap.Event.project) := by
      rcases origin with initial | allocated
      · exact Or.inl (coverage x initial)
      · exact Or.inr allocated
    have dead := (typed.other_released agree layout valid owned run tracked returned).2
    rw [live] at dead
    contradiction
  · exact (typed.every_run_safe agree layout valid owned run).2.2.result_live

/-- Starting empty, every completed scalar execution leaves no live buffers. -/
theorem Typing.closed_scalar_empty (typed : Typing g ctx [] root .scalar)
    (agree : Agrees ctx [] env)
    (run : Eval g env root SizedBufferHeap.empty value events t) :
    ∀ x, t.heap.live x = false := by
  have layout : Layout SizedBufferHeap.empty [] [] := ⟨rfl, by simp⟩
  have owned : Owns SizedBufferHeap.empty.heap [] := ⟨by simp, by simp, by simp⟩
  have post := (typed.every_run_safe agree layout SizedBufferHeap.empty_valid owned run).2.2
  have accounted := typed.heap_accounted agree layout SizedBufferHeap.empty_valid owned run
    (by simp [SizedBufferHeap.empty, HeapLeases.empty])
  cases value <;> simp [Post] at post
  case scalar v =>
    intro x
    have absent : ¬ t.heap.live x = true := by simpa [resultOwners] using (accounted x).mp
    cases h : t.heap.live x <;> simp_all

end Jihoo.SizedCoreTyping
