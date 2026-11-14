import Jihoo.NativeACUFullConfluence
import Jihoo.NativeIrrelevanceBoundary

namespace Jihoo.NativeKernel.ACU.FullExamples

private def wrap (t : Term) : Term := .uadd t (.natural 0)

theorem beta_with_additive_head_and_argument (e : Bool) (A body a : Term) :
    Conv (.app (wrap (.lam e A body)) (wrap a)) (body.subst (single a)) := by
  apply (Conv.node .app (.cons (Conv.zero _) (.cons (Conv.zero _) .nil))).trans
  exact .legacy (.beta e A body a)

theorem mixed_beta_has_common_quotient_reduct (e : Bool) (A body a : Term) :
    QJoin (.app (wrap (.lam e A body)) (wrap a)) (body.subst (single a)) :=
  (beta_with_additive_head_and_argument e A body a).church_rosser_modulo_arithmetic

theorem full_conversion_pi_injectivity (h : Conv (.pi e A B) (.pi e' A' B')) :
    e = e' ∧ Conv A A' ∧ Conv B B' := h.full_pi_injective

theorem affine_equal_in_actual_full_conversion (h : AffineSum.equal a b = true) : Conv a b :=
  (Arithmetic.affine_equal h).toConv

theorem quotient_parallel_accepts_nonaffine_substitutions (σ τ : Nat → Term)
    (h : ∀ x, QPar (σ x) (τ x)) :
    QPar ((Term.uadd (.var 0) (.var 1)).subst σ) ((Term.uadd (.var 1) (.var 0)).subst τ) :=
  (QPar.arithmetic (Arithmetic.comm (.var 0) (.var 1))).substitution h

theorem full_borrow_overlap_has_diamond (a : Term) :
    ∃ w, QPar (.node .deref [a]) w ∧ QPar (.node .deref [a]) w := by
  apply QPar.diamond (t := .node .deref [.node .borrow [.node .deref [a]]])
  · exact QPar.ofLegacyParallel (.derefBorrow (.refl _))
  · exact QPar.ofLegacyParallel (.node .deref (.cons (.borrowDeref (.refl a)) .nil))

theorem full_natural_payloads_remain_distinct : ¬ Conv (.natural 4) (.natural 5) := by
  intro h
  have := h.full_natural_injective
  contradiction

theorem full_scalar_types_remain_distinct : ¬ Conv .u64 .i64 := Conv.full_u64_i64_separate

/-- Proof fields participate in the legacy projection rule. Arbitrary raw Pack
proof irrelevance would collapse every term and is therefore still rejected. -/
theorem arbitrary_pack_irrelevance_still_rejected : ¬ IrrelevanceBoundary.PackProofIrrelevant Conv := by
  intro irrelevant
  have total := IrrelevanceBoundary.arbitrary_pack_irrelevance_collapses Conv Conv.symm Conv.trans
    (fun p a q => Conv.legacy (.proofPack p a q))
    (fun h => Conv.node .proof (.cons h .nil)) irrelevant
  exact Conv.full_u64_i64_separate (total .u64 .i64)

theorem full_common_reduct_characterizes_actual_conversion : Conv a b ↔ QJoin a b :=
  conv_iff_quotient_join a b

end Jihoo.NativeKernel.ACU.FullExamples
