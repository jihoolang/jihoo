import Jihoo.NativeAffineTyping

namespace Jihoo.NativeKernel.AffineSum.Examples

private def lit (n : Nat) : Term := .node (.natural n) []
private def plus (a b : Term) : Term := .node .uadd [a,b]

/-- The public profile really consumes native trees, including duplicate vars. -/
theorem sorted_duplicate_variables :
    canonical (plus (.var 7) (plus (.var 2) (.var 7))) =
      some ⟨[2,7,7],0⟩ := by cbv

theorem sorted_left_association :
    (Form.mk [2,7,7] 0).emit = plus (plus (.var 2) (.var 7)) (.var 7) := by cbv

theorem omit_zero_constant : (Form.mk [3] 0).emit = .var 3 := by cbv

theorem keep_nonzero_constant_last :
    (Form.mk [1,2] 7).emit = plus (plus (.var 1) (.var 2)) (lit 7) := by cbv

theorem empty_sum_emits_zero : (Form.mk [] 0).emit = lit 0 := by cbv

theorem largest_literal_is_a_leaf :
    (Form.mk [] (wordLimit-1)).emit = lit (wordLimit-1) := by cbv

theorem oversized_even_balances :
    (Form.mk [] wordLimit).emit = plus (lit (2^63)) (lit (2^63)) := by cbv

theorem oversized_odd_balances :
    (Form.mk [] (wordLimit+1)).emit = plus (lit (2^63)) (lit (2^63+1)) := by cbv

theorem max_plus_one_no_wrap :
    equal (plus (lit (wordLimit-1)) (lit 1)) (lit 0) = false := by cbv

theorem max_plus_one_balanced_equality :
    equal (plus (lit (wordLimit-1)) (lit 1)) (plus (lit (2^63)) (lit (2^63))) = true := by cbv

theorem runtime_overflow_boundary :
    runtimeCanonical (plus (lit (wordLimit-1)) (lit 1)) = none := by cbv

theorem runtime_small_fold : runtimeCanonical (plus (lit 3) (lit 4)) = some ⟨[],7⟩ := by cbv

theorem no_invalid_literal_admission : canonical (lit wordLimit) = none := by cbv

theorem no_invalid_variable_admission : canonical (.var variableLimit) = none := by cbv

theorem largest_variable_admitted :
    canonical (.var (variableLimit-1)) = some ⟨[variableLimit-1],0⟩ := by cbv

theorem no_malformed_add_admission : canonical (.node .uadd [.var 0]) = none := by cbv

theorem no_other_atom_admission : canonical (.node .u64 []) = none := by cbv

theorem no_subtraction_cancellation_claim :
    canonical (.node .usub [lit 8,lit 3,.node .u64 []]) = none := by cbv

theorem zero_duplicate_and_permutation :
    equal (plus (plus (lit 0) (.var 5)) (plus (.var 1) (.var 5)))
      (plus (.var 1) (plus (.var 5) (.var 5))) = true := by cbv

theorem symbolic_semantic_equality :
    Equivalent (plus (.var 2) (plus (lit 5) (.var 3)))
      (plus (.var 3) (plus (.var 2) (lit 5))) :=
  equal_sound (by cbv)

theorem independent_constants_separate :
    equal (plus (.var 0) (lit 3)) (plus (.var 0) (lit 4)) = false := by cbv

theorem multiplicities_separate :
    equal (plus (.var 0) (.var 0)) (.var 0) = false := by cbv

private def sourceA : Expr := .add (.var 0) (.add (.literal 4) (.var 1))
private def sourceB : Expr := .add (.var 1) (.add (.var 0) (.literal 4))

/-- Arbitrary affine replacement may duplicate variables and reorder indices. -/
theorem symbolic_substitution (σ : Nat → Expr) :
    normalize (sourceA.subst σ) = normalize (sourceB.subst σ) :=
  normalize_subst_congr (by cbv) σ

theorem order_reversing_renaming (ρ : Nat → Nat) :
    normalize (sourceA.rename ρ) = normalize (sourceB.rename ρ) :=
  normalize_rename_congr (by cbv) ρ

theorem payload_safe_balanced_output :
    (naturalSum (3*(wordLimit-1))).Valid := (naturalSum_spec _).2

theorem no_wide_collector_overflow (e : Expr) (valid : e.Valid) (cap : e.visits ≤ workLimit) :
    e.constant < wideLimit := e.constant_wide_bound valid cap

/-- Oversized ghost constants keep their type even from a code-mode derivation.
This states typing, while runtime folding still refuses this boundary above. -/
theorem code_typing_of_balanced_overflow :
    HasType [] false (Form.mk [] wordLimit).emit .u64 := by
  apply canonical_preservation (t := plus (lit (wordLimit-1)) (lit 1)) (by cbv)
  exact .uadd (.natural (by decide)) (.natural (by decide))

theorem erased_variable_ghost_typing :
    HasType [⟨.u64,true⟩] true (Form.mk [0,0] 0).emit .u64 := by
  apply canonical_preservation (t := plus (.var 0) (.var 0)) (by cbv)
  apply HasType.uadd <;>
    exact .var (b := ⟨.u64,true⟩) (by simp [lookup, Term.rename, renameArgs]) (Or.inl rfl)

theorem code_variable_readability_preserved :
    HasType [⟨.u64,false⟩,⟨.u64,false⟩] false (Form.mk [0,1] 0).emit .u64 := by
  apply canonical_preservation (t := plus (.var 1) (.var 0)) (by cbv)
  apply HasType.uadd
  · exact .var (b := ⟨.u64,false⟩)
      (by simp [lookup, Term.rename, renameArgs]) (Or.inr rfl)
  · exact .var (b := ⟨.u64,false⟩)
      (by simp [lookup, Term.rename, renameArgs]) (Or.inr rfl)

theorem exact_unreduced_type_preserved :
    HasType [] false (Form.mk [] 7).emit (.app (.lam false .u64 .u64) (.natural 0)) := by
  apply canonical_preservation (t := plus (lit 3) (lit 4)) (by cbv)
  apply HasType.convert (.uadd (.natural (by decide)) (.natural (by decide)))
  simpa [Term.subst, substArgs] using
    (Conversion.Conv.beta false .u64 .u64 (.natural 0)).symm

end Jihoo.NativeKernel.AffineSum.Examples
