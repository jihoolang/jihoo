import Jihoo.NativeACUArithmeticConfluence

namespace Jihoo.NativeKernel.ACU.ArithmeticExamples

private def lit (n : Nat) : Term := .node (.natural n) []
private def plus (a b : Term) : Term := .node .uadd [a,b]

theorem bounded_folding : Arithmetic (plus (lit 2) (lit 3)) (lit 5) := .add 2 3 (by decide)

theorem max_plus_one_uses_valid_balanced_leaves :
    Arithmetic (plus (lit (2^64-1)) (lit 1)) (plus (lit (2^63)) (lit (2^63))) :=
  Arithmetic.affine_equal (by cbv)

theorem all_natural_payloads_injective (m n : Nat)
    (h : Arithmetic (lit m) (lit n)) : m = n := h.natural_injective

theorem distinct_scalar_values_remain_distinct : ¬ Arithmetic (lit 4) (lit 5) := by
  intro h
  have := h.natural_injective
  contradiction

/-- Oversized payloads are not the balanced representation of a ghost sum. -/
theorem invalid_literal_is_not_balanced_constant :
    ¬ Arithmetic (lit (2^64)) (plus (lit (2^63)) (lit (2^63))) := by
  intro h
  have len := h.model.length
  have big : ¬ 2^64 < AffineSum.wordLimit := by decide
  have half : 2^63 < AffineSum.wordLimit := by decide
  simp only [lit, plus, arithmeticFlatten, big, half, ↓reduceIte,
    List.length_singleton, List.length_append, List.length_replicate] at len
  omega

theorem pi_injectivity_after_arithmetic
    (h : Arithmetic (.node (.pi e) [A,B]) (.node (.pi e') [A',B'])) :
    e = e' ∧ Arithmetic A A' ∧ Arithmetic B B' := h.pi_injective

theorem pi_exposes_through_zero_wrapper (e : Bool) (A B : Term) :
    ∃ A' B', Arithmetic (plus (.node (.pi e) [A,B]) (lit 0)) (.node (.pi e) [A',B']) ∧
      Arithmetic A A' ∧ Arithmetic B B' :=
  Arithmetic.pi_view (Arithmetic.zero (.node (.pi e) [A,B])).symm

theorem arithmetic_substitution_is_not_affine_restricted (σ : Nat → Term) :
    Arithmetic ((plus (.var 0) (.var 1)).subst σ) ((plus (.var 1) (.var 0)).subst σ) :=
  (Arithmetic.comm (.var 0) (.var 1)).substitution σ

theorem fold_and_split_have_actual_common_forward_reduct :
    ArithmeticJoin (lit 5) (plus (compact [lit 1,lit 1]) (compact [lit 1,lit 1,lit 1])) :=
  ArithmeticRed.confluence (.literalAdd 2 3 (by decide))
    (.addCong (.literalSplit 2 (by decide)) (.literalSplit 3 (by decide)))

theorem quotient_characterization_does_not_assume_interpretation :
    Arithmetic (plus (lit 1) (lit 1)) (lit 2) := by
  apply ArithmeticModel.complete
  have one : 1 < AffineSum.wordLimit := by decide
  have two : 2 < AffineSum.wordLimit := by decide
  simp only [ArithmeticModel, plus, lit, arithmeticFlatten, one, two, ↓reduceIte,
    List.replicate_succ, List.replicate_zero, List.nil_append, List.cons_append]
  exact .refl _

theorem variables_remain_distinct : ¬ Arithmetic (.var 0) (.var 1) := by
  intro h
  have model := h.model
  unfold ArithmeticModel at model
  simp only [arithmeticFlatten] at model
  have atom := model.singleton ArithmeticAtom.refl ArithmeticAtom.symm ArithmeticAtom.trans
  cases atom

end Jihoo.NativeKernel.ACU.ArithmeticExamples
