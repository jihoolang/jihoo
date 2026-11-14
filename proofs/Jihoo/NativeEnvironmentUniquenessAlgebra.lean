import Jihoo.NativeEnvironmentBindingAlgebra

/-! Untyped full-conversion cancellation and deterministic field instantiation.
None of these lemmas assumes type preservation or constructor injectivity. -/
namespace Jihoo.NativeKernel.Environment
open Jihoo.NativeKernel.Environment.Conversion

theorem buffer_injective (wf : UnifiedProgram.EnvWellFormed env) (h : Conv env (.buffer n) (.buffer m)) : Conv env n m := by
  obtain ⟨_,kids⟩ := h.full_rigid_node_injective rfl rfl wf.admissible
  cases kids with | cons hn _ => exact hn

theorem ref_injective (wf : UnifiedProgram.EnvWellFormed env) (h : Conv env (.ref A) (.ref B)) : Conv env A B := by
  obtain ⟨_,kids⟩ := h.full_rigid_node_injective rfl rfl wf.admissible
  cases kids with | cons hA _ => exact hA

theorem ind_injective (wf : UnifiedProgram.EnvWellFormed env) (h : Conv env (.node (.ind f n) xs) (.node (.ind g m) ys)) :
    f = g ∧ n = m ∧ ListRel (Conv env) xs ys := by
  obtain ⟨op,kids⟩ := h.full_rigid_node_injective rfl rfl wf.admissible
  cases op
  exact ⟨rfl,rfl,kids⟩

theorem applications_congr (hf : Conv env f g) (hxs : ListRel (Conv env) xs ys) :
    Conv env (applications f xs) (applications g ys) := by
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

theorem lowered_conversion (wf : UnifiedProgram.EnvWellFormed env) (left : PartialRenaming.shift (-2) 0 a = some outside)
    (right : PartialRenaming.shift (-2) 0 b = some outside') (h : Conv env a b) :
    Conv env outside outside' := by
  rw [←load_result_reweakens left, ←load_result_reweakens right] at h
  simpa only [shifted_two_cancel] using h.substitution unshiftTwo wf.closed

/-- The result of consuming the same constructor arguments is unique even when
its field typings use different modes and its starting telescope is converted. -/
theorem Arguments.result_unique (args : Arguments env ctx mode data telescope xs result)
    (wf : UnifiedProgram.EnvWellFormed env) :
    ∀ (ctx' : Context) (mode' data' : Bool) (telescope' result' : Term),
    Arguments env ctx' mode' data' telescope' xs result' → Conv env telescope telescope' → Conv env result result' := by
  apply Arguments.rec (t := args)
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ telescope xs result _ =>
      ∀ (ctx' : Context) (mode' data' : Bool) (telescope' result' : Term),
      Arguments env ctx' mode' data' telescope' xs result' → Conv env telescope telescope' → Conv env result result')
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
      have bodies := ((EnvironmentDelta.Basis.Conv.trans (.symm converted) (.trans same converted')).pi_injective wf.admissible).2.2
      exact ihtail _ _ _ _ _ tail' (bodies.substitution (single argument) wf.closed)

theorem viewMotiveType_dependency_unique (wf : UnifiedProgram.EnvWellFormed env)
    (converted : Conv env (viewMotiveType first owner) (viewMotiveType second owner')) : first = second := by
  cases first <;> cases second
  · rfl
  · exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint (op := .universe 0) (op' := .pi false)
      rfl rfl (by intro same; cases same) converted wf.admissible)
  · exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint (op := .pi false) (op' := .universe 0)
      rfl rfl (by intro same; cases same) converted wf.admissible)
  · rfl

end Jihoo.NativeKernel.Environment
