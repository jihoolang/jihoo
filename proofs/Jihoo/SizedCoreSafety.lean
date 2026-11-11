import Jihoo.SizedCoreTyping
import Jihoo.SizedCoreDeterminism
import Jihoo.OwnedApplicationFrame

namespace Jihoo.SizedCoreTyping
open ScopedLend SizedBufferContext SizedCoreExecution LinearHeapPrograms

/-- The result is scalar, or owns exactly one live unborrowed buffer of its
interpreted dependent length. No hidden postulated ownership proof is required. -/
def Post (kind : Result) (s : SizedBufferHeap.State) (value : Value) : Prop :=
  match kind, value with
  | .scalar, .scalar _ => True
  | .owner n, .owner x => Owns s.heap [x] ∧ s.length x = n
  | _, _ => False

theorem ScalarTyped.total (typed : ScalarTyped g ctx root)
    (agree : Agrees ctx owners env) : ∃ v, Scalar g env root v := by
  cases typed with
  | literal shape _ => exact ⟨_, .literal shape⟩
  | var shape lookup =>
      obtain ⟨v, hv⟩ := agree.scalar_lookup _ lookup
      exact ⟨v, .var shape hv⟩

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

theorem Account.ownedLend (h : Account (s.heap.nextObject :: owners) value events) :
    Account owners value (SizedOwnedLend.events s owner index length ++ events) := by
  intro x
  have eq := h x
  simp only [List.map_append, SizedOwnedLend.events, List.map_cons, List.map_nil,
    SizedBufferHeap.Event.project, HeapLeases.released, allocations,
    List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
    List.count_append, List.count_cons, List.count_nil] at eq ⊢
  simp only [beq_iff_eq] at *
  omega

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
  | ownedLet shape lam variableShape lookup size annotation body ih =>
      obtain ⟨x, hx, he⟩ := agree.owner_lookup _ _ lookup
      obtain ⟨v, es, t, run, steps, vt, post, account⟩ :=
        ih (agree.transferred hx) layout valid owned
      exact ⟨v, es, t, by simpa using Eval.app shape lam (.var variableShape he) run,
        steps, vt, post, account⟩
  | @framedApp rt f arg dom bod p ns Γ n kind shape lam limit annotation produce consume ihp ihc =>
      have split : Owns s.heap (owners.take p ++ owners.drop p) := by simpa using owned
      have firstOwns := OwnedApplicationFrame.owns_left split
      obtain ⟨result, before, middle, argumentRun, firstSteps, vm, firstPost, firstAccount⟩ :=
        ihp agree.producer layout.take valid firstOwns
      cases result <;> simp only [Post] at firstPost
      case owner returned =>
        obtain ⟨resultOwns, resultLength⟩ := firstPost
        have recombined : Owns middle.heap (returned :: owners.drop p) :=
          OwnedApplicationFrame.recombine valid split
            (SizedBufferHeap.steps_project firstSteps) resultOwns argumentRun.lease_frame firstAccount
        obtain ⟨value, after, t, bodyRun, lastSteps, vt, post, lastAccount⟩ :=
          ihc agree.body (layout.recombine valid owned firstSteps resultLength) vm recombined
        refine ⟨value, before ++ after, t, .app shape lam argumentRun bodyRun,
          steps_append firstSteps lastSteps, vt, post, ?_⟩
        intro x
        have first := firstAccount x
        have last := lastAccount x
        have count : owners.count x = (owners.take p).count x + (owners.drop p).count x := by
          rw [← List.count_append, List.take_append_drop]
        simp only [resultOwners, List.count_cons, List.count_nil] at first
        simp only [List.count_cons] at last
        simp only [List.map_append, HeapLeases.released, allocations,
          List.filterMap_append, List.count_append]
        simp only [HeapLeases.released, allocations] at first last
        omega
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

  | @ownedLend rt own ref len idx proof resTy ownTy bod k Γ ns slot n m i kind shape variableShape lookup size refTy length resultTy ownerTy index evidence body ih =>
      obtain ⟨x, hx, he⟩ := agree.owner_lookup _ _ lookup
      have originalLength := layout.lookup _ _ _ hx size
      have bound : i < s.length x := by rw [originalLength]; exact evidence.sound
      have indexRun := index.transport (fun _ _ h => (agree.dead (value := .borrow x)).nats_transport h)
      have lengthRun := length.transport (fun _ _ h => (agree.dead (value := .borrow x)).nats_transport h)
      have member : x ∈ owners := List.mem_of_getElem? hx
      have cycle := SizedOwnedLend.prefix_steps (length := m) valid (owned.live x member) bound
      have restoredValid : SizedBufferHeap.Valid (SizedBufferHeap.restore s) :=
        OwnedLendTransfer.restored_valid valid
      have newLayout : Layout (SizedOwnedLend.final s m (s.heap.payload x))
          (s.heap.nextObject :: owners) (m :: ns) :=
        layout.restored.allocate restoredValid (SizedBufferHeap.restored_owns owned)
      obtain ⟨v, es, t, run, steps, vt, post, account⟩ :=
        ih (s := SizedOwnedLend.final s m (s.heap.payload x)) (agree.ownedReturned hx) newLayout
          (SizedBufferHeap.steps_valid valid cycle) (SizedOwnedLend.transfer_owns valid owned)
      exact ⟨v, _, t, .ownedLend shape variableShape he indexRun lengthRun run,
        steps_append cycle steps, vt, post, account.ownedLend⟩


/-- Total safe execution is constructed from source typing and initial resource
interpretations. Neither a successful run nor a safe event trace is assumed. -/
theorem Typing.total_safe (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap owners) :
    ∃ value events t, Eval g env root s value events t ∧
      SizedBufferHeap.Steps s events t ∧ SizedBufferHeap.Valid t ∧ Post kind t value := by
  obtain ⟨value, events, t, run, steps, vt, post, _⟩ := typed.total_accounted agree layout valid owned
  exact ⟨value, events, t, run, steps, vt, post⟩

/-- The runtime ignores erased proof arguments, but every execution of a
well-typed closing instance has the derived safe trace and precise result. -/
theorem Typing.every_run_safe (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap owners)
    (run : Eval g env root s value events t) :
    SizedBufferHeap.Steps s events t ∧ SizedBufferHeap.Valid t ∧ Post kind t value := by
  obtain ⟨v, es, u, canonical, steps, vu, post⟩ := typed.total_safe agree layout valid owned
  obtain ⟨rfl, rfl, rfl⟩ := run.deterministic canonical
  exact ⟨steps, vu, post⟩

/-- The same actual events refine the established identity/lease lifecycle. -/
theorem Typing.lifecycle_projection (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap owners)
    (run : Eval g env root s value events t) :
    HeapLeases.Steps s.heap (events.map SizedBufferHeap.Event.project) t.heap :=
  SizedBufferHeap.steps_project (typed.every_run_safe agree layout valid owned run).1

end Jihoo.SizedCoreTyping
