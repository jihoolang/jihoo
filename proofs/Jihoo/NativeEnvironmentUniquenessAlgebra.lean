import Jihoo.NativeEnvironmentBindingAlgebra

/-! Untyped full-conversion cancellation and deterministic field instantiation.
None of these lemmas assumes type preservation or constructor injectivity. -/
namespace Jihoo.NativeKernel.Environment
open Jihoo.NativeKernel.Environment.Conversion

theorem buffer_injective (h : Conv (.buffer n) (.buffer m)) : Conv n m := by
  obtain ⟨_,kids⟩ := h.full_rigid_node_injective rfl rfl
  cases kids with | cons hn _ => exact hn

theorem ref_injective (h : Conv (.ref A) (.ref B)) : Conv A B := by
  obtain ⟨_,kids⟩ := h.full_rigid_node_injective rfl rfl
  cases kids with | cons hA _ => exact hA

theorem ind_injective (h : Conv (.node (.ind f n) xs) (.node (.ind g m) ys)) :
    f = g ∧ n = m ∧ ListRel Conv xs ys := by
  obtain ⟨op,kids⟩ := h.full_rigid_node_injective rfl rfl
  cases op
  exact ⟨rfl,rfl,kids⟩

theorem applications_congr (hf : Conv f g) (hxs : ListRel Conv xs ys) :
    Conv (applications f xs) (applications g ys) := by
  induction hxs generalizing f g with
  | nil => exact hf
  | cons harg htail ih =>
    exact ih (.node .app (.cons hf (.cons harg .nil)))

/-- Substitution by a total unshift map cancels two inserted binders, without
requiring a typed substitution for the discarded variables. -/
def unshiftTwo : Nat → Term
  | 0 | 1 => .natural 0
  | n + 2 => .var n

theorem shifted_two_cancel (t : Term) :
    (t.rename (fun x => x + 2)).subst unshiftTwo = t := by
  rw [Term.subst_rename]
  change t.subst (fun x => .var x) = t
  exact Term.subst_id t

theorem lowered_conversion (left : PartialRenaming.shift (-2) 0 a = some outside)
    (right : PartialRenaming.shift (-2) 0 b = some outside') (h : Conv a b) :
    Conv outside outside' := by
  rw [←load_result_reweakens left, ←load_result_reweakens right] at h
  simpa only [shifted_two_cancel] using h.substitution unshiftTwo

/-- The result of consuming the same constructor arguments is unique even when
its field typings use different modes and its starting telescope is converted. -/
theorem Arguments.result_unique (args : Arguments env ctx mode data telescope xs result) :
    ∀ (ctx' : Context) (mode' data' : Bool) (telescope' result' : Term),
    Arguments env ctx' mode' data' telescope' xs result' → Conv telescope telescope' → Conv result result' := by
  apply Arguments.rec (t := args)
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ telescope xs result _ =>
      ∀ (ctx' : Context) (mode' data' : Bool) (telescope' result' : Term),
      Arguments env ctx' mode' data' telescope' xs result' → Conv telescope telescope' → Conv result result')
    (motive_4 := fun _ _ _ _ _ => True) (motive_5 := fun _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case nil =>
    rename_i ctx mode data telescope result converted ctx' mode' data' telescope' result' other same
    cases other with
    | nil converted' => exact .trans (.symm converted) (.trans same converted')
  case cons =>
    rename_i telescope erased domain rest ctx mode data argument arguments result converted typed tail _ ihtail ctx' mode' data' telescope' result' other same
    cases other with
    | cons converted' typed' tail' =>
      have bodies := (ACU.Conv.trans (.symm converted) (.trans same converted')).pi_injective.2.2
      exact ihtail _ _ _ _ _ tail' (bodies.substitution (single argument))

end Jihoo.NativeKernel.Environment
