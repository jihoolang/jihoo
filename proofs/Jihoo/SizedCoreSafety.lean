import Jihoo.SizedCoreTyping
import Jihoo.SizedCoreDeterminism

namespace Jihoo.SizedCoreTyping
open ScopedLend SizedBufferContext SizedCoreExecution
open LinearHeapPrograms

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

private theorem steps_append (a : SizedBufferHeap.Steps s es t)
    (b : SizedBufferHeap.Steps t fs u) : SizedBufferHeap.Steps s (es ++ fs) u := by
  induction a with
  | nil => exact b
  | cons step _ ih => exact .cons step (ih b)

/-- Total safe execution is constructed from source typing and initial resource
interpretations. Neither a successful run nor a safe event trace is assumed. -/
theorem Typing.total_safe (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap owners) :
    ∃ value events t, Eval g env root s value events t ∧
      SizedBufferHeap.Steps s events t ∧ SizedBufferHeap.Valid t ∧ Post kind t value := by
  induction typed generalizing env owners s with
  | literal shape bound =>
      exact ⟨_, [], s, .scalar shape, .nil, valid, trivial⟩
  | scalar shape lookup =>
      obtain ⟨v, hv⟩ := agree.scalar_lookup _ lookup
      exact ⟨_, [], s, .var shape hv, .nil, valid, trivial⟩
  | owner shape lookup =>
      obtain ⟨x, hx, he⟩ := agree.owner_lookup _ _ lookup
      obtain ⟨rfl, length⟩ := layout.owner_result hx
      exact ⟨_, [], s, .var shape he, .nil, valid, owned, length⟩
  | naturalLet shape lam domain argument body ih =>
      have argumentRun := argument.transport (fun _ _ h => agree.nats_transport h)
      obtain ⟨v, es, t, run, steps, vt, post⟩ := ih agree.bindNat layout valid owned
      exact ⟨v, es, t, by simpa using Eval.app shape lam (index_simulation argumentRun) run,
        steps, vt, post⟩
  | @allocate rt f arg dom bod Γ n len init ns kind shape lam annotation alloc length initial body ih =>
      obtain ⟨fill, initRun⟩ := initial.total agree
      have lengthRun := length.transport (fun _ _ h => agree.nats_transport h)
      have step : SizedBufferHeap.Step s (.alloc s.heap.nextObject n fill)
          (SizedBufferHeap.allocate s n fill) := .alloc
      have owns := SizedBufferHeap.allocate_owns (n := n) (v := fill) valid owned
      obtain ⟨v, es, t, run, steps, vt, post⟩ :=
        ih agree.fresh (layout.allocate valid owned) (SizedBufferHeap.step_valid valid step) owns
      exact ⟨v, _, t, .app shape lam (.allocate alloc lengthRun initRun) run,
        .cons step steps, vt, post⟩
  | @allocation rt len init Γ n alloc length initial =>
      obtain ⟨fill, initRun⟩ := initial.total agree
      have lengthRun := length.transport (fun _ _ h => agree.nats_transport h)
      have empty : owners = [] := List.eq_nil_of_length_eq_zero (by simpa using layout.length)
      subst owners
      have step : SizedBufferHeap.Step s (.alloc s.heap.nextObject n fill)
          (SizedBufferHeap.allocate s n fill) := .alloc
      refine ⟨_, _, _, .allocate alloc lengthRun initRun, .cons step .nil,
        SizedBufferHeap.step_valid valid step, SizedBufferHeap.allocate_owns valid owned, ?_⟩
      simp [SizedBufferHeap.allocate, HeapLeases.put]
  | free shape variableShape lookup bound body ih =>
      obtain ⟨x, hx, he⟩ := agree.owner_lookup _ _ lookup
      obtain ⟨selected, rest, selection⟩ := select_total (xs := owners) (by rw [layout.length]; exact bound)
      have eq := (LinearCoreCallers.Select.lookup_selected selection).symm.trans hx
      have same : selected = x := Option.some.inj eq
      subst selected
      have step : SizedBufferHeap.Step s (.free x) (SizedBufferHeap.release s x) :=
        .free (owned.live x selection.member) (owned.leaseFree x selection.member)
      obtain ⟨v, es, t, run, steps, vt, post⟩ := ih (agree.consumed selection)
        (layout.consumed selection) (SizedBufferHeap.step_valid valid step)
        (SizedBufferHeap.release_owns owned selection)
      exact ⟨v, _, t, .free shape variableShape he run, .cons step steps, vt, post⟩
  | @branch rt l r y noRoot Γ a b ns kind shape left right yes no iy ino =>
      have leftRun := left.transport (fun _ _ h => agree.nats_transport h)
      have rightRun := right.transport (fun _ _ h => agree.nats_transport h)
      by_cases h : a < b
      · obtain ⟨v, es, t, run, steps, vt, post⟩ := iy h agree.bound layout valid owned
        exact ⟨v, es, t, .yes shape leftRun rightRun h run, steps, vt, post⟩
      · obtain ⟨v, es, t, run, steps, vt, post⟩ := ino h agree layout valid owned
        exact ⟨v, es, t, .no shape leftRun rightRun h run, steps, vt, post⟩
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
      obtain ⟨v, es, t, run, steps, vt, post⟩ := ih (s := SizedBufferHeap.restore s)
        (agree.scalarReturned selected) ⟨layout.length, layout.lookup⟩
        (SizedBufferHeap.steps_valid valid cycle) (SizedBufferHeap.restored_owns owned)
      exact ⟨v, _, t, .lend shape variableShape he indexRun run, steps_append cycle steps, vt, post⟩

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
