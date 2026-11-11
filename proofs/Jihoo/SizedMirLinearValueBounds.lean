import Jihoo.SizedMirLinearProgram

/-! Machine-width bounds for represented inputs and scalar results. These are
separate from heap capacity: an environment relation alone does not bound Nat. -/
namespace Jihoo.SizedMir.Linear
open BoundedMir

def ValueBounded : SizedErasure.Value → Prop
  | .nat n => n < wordBound
  | .scalar value => value < scalarBound
  | .owner _ | .borrow _ => True

def EnvBounded (env : SizedErasure.Env) : Prop := ∀ value ∈ env, ValueBounded value

theorem EnvBounded.cons (tail : EnvBounded env) (head : ValueBounded value) :
    EnvBounded (value :: env) := by
  intro v member
  rcases List.mem_cons.mp member with rfl | rest
  · exact head
  · exact tail v rest

/-- Width bounds only for allocated payloads, with no object or cell capacity
restriction. Dead objects are included because their payloads remain preserved. -/
def PayloadBounded (s : SizedBufferHeap.State) : Prop :=
  ∀ object, object < s.heap.nextObject → s.heap.payload object < scalarBound

theorem PayloadBounded.backward (bounded : PayloadBounded t)
    (safe : SizedBufferHeap.Steps s events t) : PayloadBounded s := by
  intro object old
  rw [← SizedBufferHeap.payloads_preserved old safe]
  exact bounded object (SizedBufferHeap.lengths_preserved old safe).1

/-- Lowering checks literals and safe reads obtain bounded allocated payloads.
Final payload bounds propagate backward through every intermediate safe trace. -/
theorem Compiles.value_bounded (compiled : Compiles inputs l b exit term fragment)
    (bounded : EnvBounded env) (valid : SizedBufferHeap.Valid s)
    (run : SizedErasure.Eval env term s value events t)
    (safe : SizedBufferHeap.Steps s events t) (payloads : PayloadBounded t) :
    ValueBounded value := by
  induction compiled generalizing env s value events t with
  | scalar bound => cases run; exact bound
  | natural bound => cases run; exact bound
  | var lookup =>
    cases run with
    | var source => exact bounded _ (List.mem_of_getElem? source)
  | allocate => cases run; trivial
  | app firstCompiled _ first last =>
    cases run with
    | app firstRun lastRun =>
      obtain ⟨firstSafe, lastSafe⟩ := Trace.trace_suffix firstCompiled.covered valid firstRun safe
      have computed := first bounded valid firstRun firstSafe (payloads.backward lastSafe)
      exact last (bounded.cons computed) (SizedBufferHeap.steps_valid valid firstSafe)
        lastRun lastSafe payloads
  | free _ _ ih =>
    cases run with
    | free _ body =>
      cases safe with
      | cons step rest =>
        cases step with
        | free live unborrowed =>
          exact ih bounded (SizedBufferHeap.step_valid valid (.free live unborrowed))
            body rest payloads
  | lend _ _ _ ih =>
    cases run with
    | lend lookup index body =>
      rename_i owner i bodyEvents
      obtain ⟨live, bound, rest⟩ := Trace.lend_prefix valid safe
      have cycle := SizedBufferHeap.read_cycle valid live bound
      have readBound := (payloads.backward safe) _ (valid.allocated _ live)
      exact ih ((bounded.cons (value := .scalar (s.heap.payload owner)) readBound).cons
        (value := .owner owner) trivial)
        (SizedBufferHeap.steps_valid valid cycle) body rest payloads
  | ownedLend _ _ _ _ ih =>
    cases run with
    | ownedLend lookup index length body =>
      rename_i owner i m bodyEvents
      obtain ⟨live, bound, rest⟩ := Trace.owned_lend_prefix valid safe
      have cycle := SizedOwnedLend.prefix_steps (length := m) valid live bound
      exact ih ((bounded.cons (value := .owner s.heap.nextObject) trivial).cons
        (value := .owner owner) trivial)
        (SizedBufferHeap.steps_valid valid cycle) body rest payloads

theorem scalar_result_bounded
    (success : lowerProgram inputTypes inputs term = some fragment)
    (bounded : EnvBounded env) (valid : SizedBufferHeap.Valid s)
    (run : SizedErasure.Eval env term s (.scalar value) events t)
    (safe : SizedBufferHeap.Steps s events t) (payloads : PayloadBounded t) :
    value < scalarBound :=
  (lowerProgram_shape success).1.value_bounded bounded valid run safe payloads

/-- With bounded represented inputs, the completed program returns a value in
the modeled nonnegative I64 range as well as executing with the related heap. -/
theorem bounded_program_run (success : lowerProgram inputTypes inputs term = some fragment)
    (size : inputTypes.size = f.locals.size) (related : EnvRel env inputs f)
    (heaps : HeapRel s f.heap) (initial : SizedBufferHeap.Valid s)
    (run : SizedErasure.Eval env term s (.scalar value) events t)
    (safe : SizedBufferHeap.Steps s events t) (heapBounds : Trace.Bounds t)
    (valueBounds : EnvBounded env) :
    value < scalarBound ∧
    ∃ final, Steps (program inputTypes fragment)
      (.running (start (programFrame fragment f) (entry 1 0 term)))
      (lifecycle events) (.returned value final) ∧ HeapRel t final.heap ∧
      final.locals.size = (program inputTypes fragment).locals.size ∧
      (∀ i, i < f.locals.size → i ≠ 0 → final.locals[i]? = f.locals[i]?) :=
  ⟨scalar_result_bounded success valueBounds initial run safe heapBounds.payloads,
    program_run success size related heaps initial run safe heapBounds⟩

end Jihoo.SizedMir.Linear
