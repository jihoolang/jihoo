import Jihoo.NativeACUForwardConfluence
import Jihoo.NativeACUFullExamples

namespace Jihoo.NativeKernel.ACU.ForwardExamples

/-- The full mixed theorem ends in an actual common forward reduct. -/
theorem beta_with_hidden_additive_head_has_actual_common_reduct (e : Bool) (A body a : Term) :
    MixedJoin (.app (.uadd (.lam e A body) (.natural 0)) (.uadd a (.natural 0)))
      (body.subst (single a)) :=
  (FullExamples.beta_with_additive_head_and_argument e A body a).church_rosser

theorem actual_common_reduct_for_every_full_conversion (h : Conv a b) : MixedJoin a b :=
  h.church_rosser

theorem actual_forward_beta_arithmetic_peak :
    MixedJoin (.uadd (.natural 2) (.natural 3)) (.natural 5) := by
  let source : Term := .app (.lam false .u64 (.var 0)) (.uadd (.natural 2) (.natural 3))
  have beta : MixedRed source (.uadd (.natural 2) (.natural 3)) := by
    simpa only [source,Term.subst,single] using
      MixedRed.compute (Computes.beta false .u64 (.var 0) (.uadd (.natural 2) (.natural 3)))
  have folded : MixedRed source (.natural 5) := by
    apply (MixedRed.node .app (.cons (.refl _) (.cons (.arithmetic (.literalAdd 2 3 (by decide))) .nil))).trans
    simpa only [Term.subst,single] using
      MixedRed.compute (Computes.beta false .u64 (.var 0) (.natural 5))
  exact beta.confluence folded

theorem actual_quotient_realization_uses_no_affine_restriction (h : QPar a b) :
    ∃ c, MixedRed a c ∧ Arithmetic b c := h.realize (.refl a)

theorem actual_common_reduct_iff_full_conversion : Conv a b ↔ MixedJoin a b :=
  conv_iff_mixed_join a b

theorem actual_common_reduct_still_gives_pi_injectivity
    (h : Conv (.pi e A B) (.pi e' A' B')) : e = e' ∧ Conv A A' ∧ Conv B B' :=
  h.full_pi_injective

end Jihoo.NativeKernel.ACU.ForwardExamples
