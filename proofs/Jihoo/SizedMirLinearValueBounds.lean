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

/-- Lowering checks new literals; applications retain the bounds of computed
values. Heap capacity does not substitute for bounded dynamic input values. -/
theorem Compiles.value_bounded (compiled : Compiles inputs l b exit term fragment)
    (bounded : EnvBounded env) (run : SizedErasure.Eval env term s value events t) :
    ValueBounded value := by
  induction compiled generalizing env s value events t with
  | scalar bound => cases run; exact bound
  | natural bound => cases run; exact bound
  | var lookup =>
    cases run with
    | var source => exact bounded _ (List.mem_of_getElem? source)
  | allocate => cases run; trivial
  | app _ _ first last =>
    cases run with
    | app firstRun lastRun => exact last (bounded.cons (first bounded firstRun)) lastRun
  | free _ _ ih => cases run with
    | free _ body => exact ih bounded body

theorem scalar_result_bounded
    (success : lowerProgram inputTypes inputs term = some fragment)
    (bounded : EnvBounded env)
    (run : SizedErasure.Eval env term s (.scalar value) events t) : value < scalarBound :=
  (lowerProgram_shape success).1.value_bounded bounded run

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
  ⟨scalar_result_bounded success valueBounds run,
    program_run success size related heaps initial run safe heapBounds⟩

end Jihoo.SizedMir.Linear
