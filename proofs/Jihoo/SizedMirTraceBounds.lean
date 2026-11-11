import Jihoo.SizedMirHeap
import Jihoo.SizedErasedRuntime

/-! Safe source trace decomposition and cumulative physical resource bounds.
The straight-line predicate excludes branching and leases, but trace bounds apply
to every sized heap event. Released objects still consume physical capacity. -/
namespace Jihoo.SizedMir.Trace
open SizedBufferHeap

inductive LinearTerm : SizedErasure.Term → Prop where
  | scalar : LinearTerm (.scalar v)
  | natural : LinearTerm (.natural n)
  | var : LinearTerm (.var k)
  | allocate : LinearTerm (.allocate length fill)
  | app : LinearTerm argument → LinearTerm body → LinearTerm (.app argument body)
  | free : LinearTerm body → LinearTerm (.free k body)

theorem steps_append (first : Steps s es t) (last : Steps t fs u) :
    Steps s (es ++ fs) u := by
  induction first with
  | nil => exact last
  | cons step _ ih => exact .cons step (ih last)

theorem steps_split (run : Steps s (es ++ fs) u) :
    ∃ t, Steps s es t ∧ Steps t fs u := by
  induction es generalizing s with
  | nil => exact ⟨s, .nil, run⟩
  | cons e es ih =>
    cases run with
    | cons step rest =>
      obtain ⟨t, first, last⟩ := ih rest
      exact ⟨t, .cons step first, last⟩

/-- Forget checks while retaining the state update of a single event. -/
def update (s : State) : Event → State
  | .alloc _ n v => allocate s n v
  | .free x => release s x
  | .beginLease _ x => lend s x
  | .close token => close s token
  | .read _ _ _ => s

theorem step_update (run : Step s e t) : t = update s e := by
  cases run <;> rfl

theorem step_deterministic (first : Step s e t) (second : Step s e u) : t = u :=
  (step_update first).trans (step_update second).symm

theorem steps_deterministic (first : Steps s es t) (second : Steps s es u) : t = u := by
  induction first generalizing u with
  | nil => cases second; rfl
  | cons step rest ih =>
    cases second with
    | cons other tail =>
      obtain rfl := step_deterministic step other
      exact ih tail

/-- Split a safe trace at the exact state selected by compact evaluation, rather
than introducing an unrelated existential midpoint. No target execution occurs. -/
theorem trace_suffix (covered : LinearTerm term)
    (run : SizedErasure.Eval env term s value events t)
    (safe : Steps s (events ++ suffix) u) :
    Steps s events t ∧ Steps t suffix u := by
  induction covered generalizing env s value events t suffix u with
  | scalar => cases run; exact ⟨.nil, safe⟩
  | natural => cases run; exact ⟨.nil, safe⟩
  | var => cases run; exact ⟨.nil, safe⟩
  | allocate =>
    cases run with
    | allocate length fill =>
      cases safe with
      | cons step rest =>
        cases step
        exact ⟨.cons .alloc .nil, rest⟩
  | app first last ihFirst ihLast =>
    cases run with
    | app firstRun lastRun =>
      have adjusted := safe
      rw [List.append_assoc] at adjusted
      obtain ⟨firstSteps, rest⟩ := ihFirst firstRun adjusted
      obtain ⟨lastSteps, tail⟩ := ihLast lastRun rest
      exact ⟨steps_append firstSteps lastSteps, tail⟩
  | free body ih =>
    cases run with
    | free lookup bodyRun =>
      cases safe with
      | cons step rest =>
        cases step with
        | free live unborrowed =>
          obtain ⟨bodySteps, tail⟩ := ih bodyRun rest
          exact ⟨.cons (.free live unborrowed) bodySteps, tail⟩

theorem eval_state_eq (covered : LinearTerm term)
    (run : SizedErasure.Eval env term s value events t)
    (safe : Steps s events u) : t = u := by
  have suffix : Steps s (events ++ []) u := by simpa using safe
  obtain ⟨_, rest⟩ := trace_suffix covered run suffix
  cases rest
  rfl

theorem step_objects_mono (run : Step s e t) : s.heap.nextObject ≤ t.heap.nextObject := by
  cases run <;> simp [allocate, release, lend, close]

theorem steps_objects_mono (run : Steps s events t) : s.heap.nextObject ≤ t.heap.nextObject := by
  induction run with
  | nil => exact Nat.le_refl _
  | cons step _ ih => exact Nat.le_trans (step_objects_mono step) ih

theorem step_cells_mono (run : Step s e t) : cellCount s ≤ cellCount t := by
  cases run with
  | alloc => rw [cellCount_allocate]; omega
  | free => exact Nat.le_refl _
  | beginLease => exact Nat.le_refl _
  | close => exact Nat.le_refl _
  | read => exact Nat.le_refl _

theorem steps_cells_mono (run : Steps s events t) : cellCount s ≤ cellCount t := by
  induction run with
  | nil => exact Nat.le_refl _
  | cons step _ ih => exact Nat.le_trans (step_cells_mono step) ih

/-- Every allocated object counts, including objects that have been released. -/
structure Bounds (s : State) : Prop where
  objects : s.heap.nextObject ≤ 512
  cells : cellCount s ≤ 4096
  payloads : ∀ object, object < s.heap.nextObject → s.heap.payload object < BoundedMir.scalarBound

/-- Final resource bounds suffice at every earlier state of a safe trace.
Payload preservation is indexed by allocated identity, not by liveness. -/
theorem Bounds.backward (bound : Bounds t) (run : Steps s events t) : Bounds s := by
  refine ⟨Nat.le_trans (steps_objects_mono run) bound.objects,
    Nat.le_trans (steps_cells_mono run) bound.cells, ?_⟩
  intro object old
  have next := (lengths_preserved old run).1
  rw [← payloads_preserved old run]
  exact bound.payloads object next

theorem Bounds.step_backward (bound : Bounds t) (run : Step s event t) : Bounds s :=
  bound.backward (.cons run .nil)

/-- Exact resource premises required by the generated allocation fragment. -/
theorem Bounds.allocation (bound : Bounds (allocate s n fill)) :
    s.heap.nextObject < 512 ∧ cellCount s + n + 1 ≤ 4096 ∧ fill < BoundedMir.scalarBound := by
  have objects := bound.objects
  have cells := bound.cells
  have payload := bound.payloads s.heap.nextObject (by simp [allocate])
  simp only [allocate] at objects
  rw [cellCount_allocate] at cells
  simp only [allocate, HeapLeases.put, ite_true] at payload
  exact ⟨by omega, cells, payload⟩

theorem Bounds.empty : Bounds SizedBufferHeap.empty := by
  constructor
  · change 0 ≤ 512; decide
  · change (List.ofFn (fun j : Fin 0 => SizedBufferHeap.empty.length j.val + 1)).sum ≤ 4096
    simp
  · intro object old
    change object < 0 at old
    omega

end Jihoo.SizedMir.Trace
