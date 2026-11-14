import Jihoo.NativeACUBoundedNormalizer

namespace Jihoo.NativeKernel.ACU.NormalizerExamples

private def a : Term := .array (.var 3)
private def b : Term := .app (.var 5) (.var 2)
private def plus (x y : Term) : Term := .uadd x y

/-- Both atoms lie outside the previous Var/Natural/UAdd parser. -/
theorem arbitrary_native_atoms_commute : Canonical.equal (plus a b) (plus b a) = true := by cbv

theorem bounded_native_atoms_commute : Bounded.equal 8 256 (plus a b) (plus b a) = true := by cbv

theorem actual_full_conversion_of_nonaffine_atoms : Conv (plus a b) (plus b a) :=
  Bounded.equal_sound bounded_native_atoms_commute

theorem actual_forward_reduct_of_nonaffine_atoms :
    ∃ u, MixedRed (plus a b) u ∧ MixedRed (plus b a) u :=
  Bounded.equal_common_reduct bounded_native_atoms_commute

theorem balanced_ghost_constants_are_valid_leaves :
    Bounded.run 8 256 (plus (.natural (2^64-1)) (.natural 1)) =
      some (plus (.natural (2^63)) (.natural (2^63))) := by cbv

theorem oversized_raw_literal_stays_opaque :
    Bounded.equal 8 256 (.natural (2^64)) (plus (.natural (2^63)) (.natural (2^63))) = false := by cbv

theorem all_pack_proof_slots_are_retained :
    Bounded.equal 8 256 (.pack (.var 7) (.var 2) (.var 0)) (.pack (.var 7) (.var 2) (.var 1)) = false := by cbv

theorem structural_order_keeps_proof_slots :
    Canonical.compareTerm (.pack (.var 7) (.var 2) (.var 0)) (.pack (.var 7) (.var 2) (.var 1)) = .lt := by cbv

theorem strict_is_not_erased :
    Bounded.run 8 256 (.node .strict [.var 0,.var 1]) = some (.node .strict [.var 0,.var 1]) := by cbv

theorem normalization_follows_binder_children :
    Bounded.run 8 256 (.pi false (plus b a) (.lam true .u64 (plus (.var 2) (.var 0)))) =
      some (.pi false (plus a b) (.lam true .u64 (plus (.var 0) (.var 2)))) := by cbv

theorem beta_exposes_arbitrary_additive_heads :
    Bounded.run 8 256 (.app (plus (.lam false .u64 (.var 0)) (.natural 0)) (plus b a)) = some (plus a b) := by cbv

theorem zero_node_budget_fails_closed : Bounded.run 8 0 (.var 0) = none := by cbv

theorem oversized_fuel_fails_closed : Bounded.run 129 256 (.var 0) = none := by cbv

theorem child_output_allowance_is_shared :
    Bounded.run 8 2 (plus (.var 0) (.var 1)) = none := by cbv

theorem concrete_kit_soundness (h : Bounded.kit.equal fuel limit x y = true) : Conv x y :=
  Bounded.kit.equalitySound h

theorem concrete_kit_forward_output (h : Bounded.kit.normalize fuel limit x = some y) : MixedRed x y :=
  Bounded.kit.normalizationForward h

end Jihoo.NativeKernel.ACU.NormalizerExamples
