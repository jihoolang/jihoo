import Jihoo.CorePayloadReflection

/-! Finite execution adequacy for pure Core payload erasure. This removes proof
payloads and annotations, not ghost binder slots or applications. It concerns the
specified pure evaluation relation, not native MIR, allocation or termination. -/
namespace Jihoo.CoreBridge.Raw.Beta.PayloadErasure
open Evaluation

/-- Count runtime transitions, including erased beta contractions: payload
 erasure preserves these slots, so there is no silent/stuttering transition. -/
inductive StepsN : Nat → Raw → Raw → Prop where
  | refl : StepsN 0 t t
  | next : Evaluation.Step t u → StepsN n u v → StepsN (n + 1) t v

theorem StepsN.steps (h : StepsN n t u) : Evaluation.Steps t u := by
  induction h with
  | refl => exact .refl
  | next hs _ ih => exact .next hs ih

theorem steps_counted (h : Evaluation.Steps t u) : ∃ n, StepsN n t u := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | next hs _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, .next hs hn⟩

theorem counted_erasure (h : StepsN n t u) : StepsN n (erase t) (erase u) := by
  induction h with
  | refl => exact .refl
  | next hs _ ih => exact .next (step_erasure hs) ih

theorem counted_reflection (h : StepsN n (erase t) v) :
    ∃ u, StepsN n t u ∧ erase u = v := by
  generalize he : erase t = start at h
  induction h generalizing t with
  | refl => exact ⟨t, .refl, he⟩
  | next hs _ ih =>
      obtain ⟨u, hu, eu⟩ := step_reflection (t := t) (by simpa only [he] using hs)
      obtain ⟨w, hw, ew⟩ := ih eu
      exact ⟨w, .next hu hw, ew⟩

theorem counted_execution_iff : StepsN n (erase t) v ↔
    ∃ u, StepsN n t u ∧ erase u = v := by
  constructor
  · exact counted_reflection
  · rintro ⟨u, hu, rfl⟩
    exact counted_erasure hu

/-- Arbitrarily long finite executions are preserved in both directions.
This does not assume termination or construct a coinductive infinite run. -/
theorem unbounded_execution_iff :
    (∀ n, ∃ v, StepsN n (erase t) v) ↔ (∀ n, ∃ u, StepsN n t u) := by
  constructor
  · intro h n
    obtain ⟨v, hv⟩ := h n
    obtain ⟨u, hu, _⟩ := counted_reflection hv
    exact ⟨u, hu⟩
  · intro h n
    obtain ⟨u, hu⟩ := h n
    exact ⟨erase u, counted_erasure hu⟩

/-- Every finite erased execution lifts, including intermediate non-values. -/
theorem steps_reflection (h : Evaluation.Steps (erase t) v) :
    ∃ u, Evaluation.Steps t u ∧ erase u = v := by
  generalize he : erase t = start at h
  induction h generalizing t with
  | refl => exact ⟨t, .refl, he⟩
  | next hs _ ih =>
      obtain ⟨u, hu, eu⟩ := step_reflection (t := t) (by simpa only [he] using hs)
      obtain ⟨w, hw, ew⟩ := ih eu
      exact ⟨w, .next hu hw, ew⟩

theorem execution_iff : Evaluation.Steps (erase t) v ↔
    ∃ u, Evaluation.Steps t u ∧ erase u = v := by
  constructor
  · exact steps_reflection
  · rintro ⟨u, hu, rfl⟩
    simpa only [erase] using steps_erasure hu

theorem trap_iff : Trap (erase t) ↔ Trap t :=
  ⟨trap_reflection, trap_erasure⟩

theorem outcome_iff : Outcome (erase t) ↔ Outcome t := by
  constructor
  · intro h
    rcases h with hv | ⟨v, hs⟩ | ht
    · exact .inl (value_reflection t hv)
    · obtain ⟨u, hu, _⟩ := step_reflection hs
      exact .inr (.inl ⟨u, hu⟩)
    · exact .inr (.inr (trap_reflection ht))
  · exact outcome_erasure

/-- Erased runs preserve the exact scalar observation in both directions. -/
theorem natural_execution_iff : Evaluation.Steps (erase t) (.natural n) ↔
    Evaluation.Steps t (.natural n) := by
  constructor
  · intro h
    obtain ⟨u, hu, eu⟩ := steps_reflection h
    exact erase_natural_iff.mp eu ▸ hu
  · intro h
    simpa only [erase] using steps_erasure h

theorem integer_execution_iff : Evaluation.Steps (erase t) (.integer n) ↔
    Evaluation.Steps t (.integer n) := by
  constructor
  · intro h
    obtain ⟨u, hu, eu⟩ := steps_reflection h
    exact erase_integer_iff.mp eu ▸ hu
  · intro h
    simpa only [erase] using steps_erasure h

private theorem integer_list_reflection (xs : List Raw) (ns : List Int)
    (h : xs.map erase = ns.map Raw.integer) : xs = ns.map Raw.integer := by
  induction xs generalizing ns with
  | nil => cases ns <;> simp_all
  | cons x xs ih =>
      cases ns with
      | nil => simp at h
      | cons n ns =>
          simp only [List.map_cons, List.cons.injEq] at h
          rw [erase_integer_iff.mp h.1, ih ns h.2]
          rfl

theorem erase_integer_array_iff {ns : List Int} :
    erase t = .elements (ns.map Raw.integer) ↔ t = .elements (ns.map Raw.integer) := by
  constructor
  · intro h
    cases t <;> simp only [erase] at h <;> try contradiction
    case elements xs =>
      have hm : xs.map erase = ns.map Raw.integer := by injection h
      exact congrArg Raw.elements (integer_list_reflection xs ns hm)
  · rintro rfl
    simp [erase, List.map_map]

theorem integer_array_execution_iff {ns : List Int} :
    Evaluation.Steps (erase t) (.elements (ns.map Raw.integer)) ↔
    Evaluation.Steps t (.elements (ns.map Raw.integer)) := by
  constructor
  · intro h
    obtain ⟨u, hu, eu⟩ := steps_reflection h
    exact erase_integer_array_iff.mp eu ▸ hu
  · intro h
    simpa only [(erase_integer_array_iff (t := .elements (ns.map Raw.integer))).mpr rfl]
      using steps_erasure h

/-- A terminating run to any value is reflected; lambda annotations/proofs may
be different, so the source value is related by erasure rather than equality. -/
theorem value_execution_iff :
    (∃ v, Evaluation.Steps (erase t) v ∧ Value v) ↔
    (∃ u, Evaluation.Steps t u ∧ Value u) := by
  constructor
  · rintro ⟨v, hv, ready⟩
    obtain ⟨u, hu, rfl⟩ := steps_reflection hv
    exact ⟨u, hu, value_reflection u ready⟩
  · rintro ⟨u, hu, ready⟩
    exact ⟨erase u, steps_erasure hu, value_erasure ready⟩

theorem trap_execution_iff :
    (∃ v, Evaluation.Steps (erase t) v ∧ Trap v) ↔
    (∃ u, Evaluation.Steps t u ∧ Trap u) := by
  constructor
  · rintro ⟨v, hv, trapped⟩
    obtain ⟨u, hu, rfl⟩ := steps_reflection hv
    exact ⟨u, hu, trap_reflection trapped⟩
  · rintro ⟨u, hu, trapped⟩
    exact ⟨erase u, steps_erasure hu, trap_erasure trapped⟩

/-- Equal erased terms are observationally interchangeable for scalar/array
results and explicit traps, even when their source proof payloads differ. -/
theorem equal_erasure_natural (h : erase t = erase u) :
    Evaluation.Steps t (.natural n) ↔ Evaluation.Steps u (.natural n) := by
  calc
    _ ↔ Evaluation.Steps (erase t) (.natural n) := natural_execution_iff.symm
    _ ↔ Evaluation.Steps (erase u) (.natural n) := by rw [h]
    _ ↔ _ := natural_execution_iff

theorem equal_erasure_integer (h : erase t = erase u) :
    Evaluation.Steps t (.integer n) ↔ Evaluation.Steps u (.integer n) := by
  calc
    _ ↔ Evaluation.Steps (erase t) (.integer n) := integer_execution_iff.symm
    _ ↔ Evaluation.Steps (erase u) (.integer n) := by rw [h]
    _ ↔ _ := integer_execution_iff

theorem equal_erasure_integer_array {ns : List Int} (h : erase t = erase u) :
    Evaluation.Steps t (.elements (ns.map Raw.integer)) ↔
    Evaluation.Steps u (.elements (ns.map Raw.integer)) := by
  calc
    _ ↔ Evaluation.Steps (erase t) (.elements (ns.map Raw.integer)) := integer_array_execution_iff.symm
    _ ↔ Evaluation.Steps (erase u) (.elements (ns.map Raw.integer)) := by rw [h]
    _ ↔ _ := integer_array_execution_iff

theorem equal_erasure_trap (h : erase t = erase u) :
    (∃ v, Evaluation.Steps t v ∧ Trap v) ↔
    (∃ v, Evaluation.Steps u v ∧ Trap v) := by
  calc
    _ ↔ (∃ v, Evaluation.Steps (erase t) v ∧ Trap v) := trap_execution_iff.symm
    _ ↔ (∃ v, Evaluation.Steps (erase u) v ∧ Trap v) := by rw [h]
    _ ↔ _ := trap_execution_iff

/-- Safety for *every* finite target execution, not only a constructed forward
trace. Source typing is preserved; erased terms need not pass source typing. -/
theorem typed_target_execution (h : HasType (fun _ => none) t A)
    (run : Evaluation.Steps (erase t) v) :
    ∃ u, Evaluation.Steps t u ∧ erase u = v ∧
      HasType (fun _ => none) u A ∧ Outcome u ∧ Outcome v := by
  obtain ⟨u, hu, rfl⟩ := steps_reflection run
  obtain ⟨typed, safe⟩ := Evaluation.execution_safety h hu
  exact ⟨u, hu, rfl, typed, safe, outcome_erasure safe⟩

end Jihoo.CoreBridge.Raw.Beta.PayloadErasure
