import Jihoo.CorePayloadErasure

namespace Jihoo.CoreBridge.Raw.Beta.PayloadErasure
open Evaluation

private theorem map_split (xs pre post : List Raw) (v : Raw)
    (h : xs.map erase = pre ++ v :: post) :
    ∃ as a bs, xs = as ++ a :: bs ∧ as.map erase = pre ∧ erase a = v ∧ bs.map erase = post := by
  induction pre generalizing xs with
  | nil =>
      cases xs with
      | nil => simp at h
      | cons a bs =>
          simp only [List.map_cons, List.nil_append, List.cons.injEq] at h
          exact ⟨[], a, bs, rfl, rfl, h.1, h.2⟩
  | cons p pre ih =>
      cases xs with
      | nil => simp at h
      | cons a xs =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
          obtain ⟨as, b, bs, rfl, hp, hb, hbs⟩ := ih xs h.2
          exact ⟨a :: as, b, bs, rfl, by simp [h.1, hp], hb, hbs⟩

/-- A target evaluation frame has a source frame with the same runtime hole.
Annotations and evidence may differ, but no active constructor is deleted. -/
private theorem frame_reflection (f : Frame) (t v : Raw)
    (he : erase t = f.fill v) :
    ∃ (g : Frame) (u : Raw), t = g.fill u ∧ erase u = v ∧
      ∀ w, erase (g.fill w) = f.fill (erase w) := by
  cases f <;> cases t <;> simp [erase, Frame.fill] at he
  case appFunction.app a f x =>
    exact ⟨.appFunction x, f, rfl, he.1, fun w => by simp [Frame.fill, erase, he.2]⟩
  case appArgument.app A body f x =>
    obtain ⟨hf, hx⟩ := he
    cases f <;> simp [erase] at hf
    case lam e D b =>
      obtain ⟨rfl, rfl, rfl⟩ := hf
      exact ⟨.appArgument D b, x, rfl, hx, fun w => by simp [Frame.fill, erase]⟩
  case uaddLeft.uadd b a x =>
    exact ⟨.uaddLeft x, a, rfl, he.1, fun w => by simp [Frame.fill, erase, he.2]⟩
  case uaddRight.uadd n a b =>
    obtain ⟨ha, hb⟩ := he
    obtain rfl := erase_natural_iff.mp ha
    exact ⟨.uaddRight n, b, rfl, hb, fun w => by simp [Frame.fill, erase]⟩
  case usubLeft.usub b p a x q =>
    obtain ⟨ha, hb, rfl⟩ := he
    exact ⟨.usubLeft x q, a, rfl, ha, fun w => by simp [Frame.fill, erase, hb]⟩
  case usubRight.usub n p a b q =>
    obtain ⟨ha, hb, rfl⟩ := he
    obtain rfl := erase_natural_iff.mp ha
    exact ⟨.usubRight n q, b, rfl, hb, fun w => by simp [Frame.fill, erase]⟩
  case indexArray.index i p a x q =>
    obtain ⟨ha, hb, rfl⟩ := he
    exact ⟨.indexArray x q, a, rfl, ha, fun w => by simp [Frame.fill, erase, hb]⟩
  case indexIndex.index xs p ready a i q =>
    obtain ⟨ha, hi, rfl⟩ := he
    cases a <;> simp [erase] at ha
    case elements ys =>
      subst xs
      have hy : ∀ x ∈ ys, Value x := fun x hx =>
        value_reflection x (ready (erase x) (List.mem_map.mpr ⟨x, hx, rfl⟩))
      exact ⟨.indexIndex ys q hy, i, rfl, hi, fun w => by simp [Frame.fill, erase]⟩
  case elements.elements pre post ready xs =>
    obtain ⟨as, a, bs, rfl, hp, ha, hbs⟩ := map_split xs pre post v he
    have hr : ∀ x ∈ as, Value x := by
      intro x hx
      apply value_reflection x
      apply ready
      rw [← hp]
      exact List.mem_map.mpr ⟨x, hx, rfl⟩
    exact ⟨.elements as bs hr, a, rfl, ha, fun w => by simp [Frame.fill, erase, List.map_append, hp, hbs]⟩

private theorem step_reflection_aux (h : Evaluation.Step s v) :
    ∀ t, erase t = s → ∃ u, Evaluation.Step t u ∧ erase u = v := by
  induction h with
  | betaRuntime ready =>
      intro t he
      cases t <;> simp [erase] at he
      case app f a =>
        obtain ⟨hf, rfl⟩ := he
        cases f <;> simp [erase] at hf
        case lam e A b =>
          obtain ⟨rfl, rfl, rfl⟩ := hf
          exact ⟨_, .betaRuntime (value_reflection a ready), erase_instantiate b a⟩
  | betaErased =>
      intro t he
      cases t <;> simp [erase] at he
      case app f a =>
        obtain ⟨hf, rfl⟩ := he
        cases f <;> simp [erase] at hf
        case lam e A b =>
          obtain ⟨rfl, rfl, rfl⟩ := hf
          exact ⟨_, .betaErased, erase_instantiate b a⟩
  | add bound =>
      intro t he
      cases t <;> simp [erase] at he
      case uadd a b =>
        obtain ⟨ha, hb⟩ := he
        obtain rfl := erase_natural_iff.mp ha
        obtain rfl := erase_natural_iff.mp hb
        exact ⟨_, .add bound, by simp [erase]⟩
  | sub le bound =>
      intro t he
      cases t <;> simp [erase] at he
      case usub a b p =>
        obtain ⟨ha, hb, rfl⟩ := he
        obtain rfl := erase_natural_iff.mp ha
        obtain rfl := erase_natural_iff.mp hb
        exact ⟨_, .sub le bound, by simp [erase]⟩
  | read ready selected =>
      intro t he
      cases t <;> simp [erase] at he
      case index a i p =>
        obtain ⟨ha, hi, rfl⟩ := he
        obtain rfl := erase_natural_iff.mp hi
        cases a <;> simp [erase] at ha
        case elements xs =>
          subst ha
          rw [List.getElem?_map] at selected
          obtain ⟨u, hu, he⟩ := Option.map_eq_some_iff.mp selected
          have hr : ∀ x ∈ xs, Value x := fun x hx =>
            value_reflection x (ready (erase x) (List.mem_map.mpr ⟨x, hx, rfl⟩))
          exact ⟨u, .read hr hu, he⟩
  | context f hs ih =>
      intro t he
      obtain ⟨g, u, rfl, hu, hg⟩ := frame_reflection f t _ he
      obtain ⟨w, hw, hew⟩ := ih u hu
      exact ⟨g.fill w, .context g hw, by rw [hg, hew]⟩

/-- Every step of the payload-erased program lifts to one original strict
step. This theorem is structural and requires no source typing premise. -/
theorem step_reflection (h : Evaluation.Step (erase t) v) :
    ∃ u, Evaluation.Step t u ∧ erase u = v := step_reflection_aux h t rfl

private theorem trap_reflection_aux (h : Evaluation.Trap s) :
    ∀ t, erase t = s → Evaluation.Trap t := by
  induction h with
  | overflow bound =>
      intro t he
      cases t <;> simp [erase] at he
      case uadd a b =>
        obtain ⟨ha, hb⟩ := he
        obtain rfl := erase_natural_iff.mp ha
        obtain rfl := erase_natural_iff.mp hb
        exact .overflow bound
  | context f ht ih =>
      intro t he
      obtain ⟨g, u, rfl, hu, _⟩ := frame_reflection f t _ he
      exact .context g (ih u hu)

/-- Erasing annotations and evidence cannot introduce an arithmetic trap. -/
theorem trap_reflection (h : Evaluation.Trap (erase t)) : Evaluation.Trap t :=
  trap_reflection_aux h t rfl

end Jihoo.CoreBridge.Raw.Beta.PayloadErasure
