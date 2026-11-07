import Jihoo.CoreBridgeBetaPreservation
import Jihoo.CoreBridgeMetatheoryExamples
import Jihoo.GraphCertificateBetaTyping

/-! Kernel-checked witnesses for the beta-aware extension and its boundaries. -/
namespace Jihoo.CoreBridge.Raw.Beta.Examples

open Raw.Examples

private theorem redex_step : Step argumentRedex (.natural 0) := by
  simpa [argumentRedex, subst, single] using Step.beta false .u64 (.var 0) (.natural 0)

/-- The earlier counterexample is genuinely repaired at the same raw type. -/
theorem dependent_after_original_type :
    HasType empty (.app dependentFunction (.natural 0)) (.eq argumentRedex argumentRedex) := by
  apply HasType.preservation (HasType.of_raw dependent_before_typed)
  exact .appArgument redex_step

/-- The equality of result types is non-reflexive beta conversion. -/
theorem dependent_result_conversion :
    Conv (.eq argumentRedex argumentRedex) (.eq (.natural 0) (.natural 0)) :=
  .eq redex_step.conversion redex_step.conversion

private theorem numeral_zero {Γ : Context} : HasType Γ (.natural 0) .u64 := .natural (by decide)

private theorem identity {Γ : Context} :
    HasType Γ (.lam false .u64 (.var 0)) (.pi false .u64 .u64) :=
  .lam .u64 rfl (.var (by simp [Context.extend, rename]))

private theorem argument_typed {Γ : Context} : HasType Γ argumentRedex .u64 := by
  simpa [argumentRedex, subst] using HasType.app (identity (Γ := Γ)) (numeral_zero (Γ := Γ))

/-- Reducing a lambda annotation changes the binder's context, so its body must
be transported before the original dependent Pi type can be recovered. -/
theorem annotation_before_typed :
    HasType empty (.lam true (.eq argumentRedex argumentRedex) (.var 0))
      (.pi true (.eq argumentRedex argumentRedex)
        ((Raw.eq argumentRedex argumentRedex).rename Nat.succ)) :=
  .lam (.eq argument_typed argument_typed) rfl (.var rfl)

theorem annotation_after_original_type :
    HasType empty (.lam true (.eq (.natural 0) argumentRedex) (.var 0))
      (.pi true (.eq argumentRedex argumentRedex)
        ((Raw.eq argumentRedex argumentRedex).rename Nat.succ)) :=
  annotation_before_typed.preservation
    (.lamDomain (.eqLeft redex_step))

/-- Head contraction uses Pi injectivity when the function's domain itself
has been changed by a non-reflexive conversion. -/
theorem converted_pi_head_beta :
    HasType empty (.refl (.natural 0)) (.eq argumentRedex argumentRedex) := by
  have hf : HasType empty (.lam true (.eq argumentRedex argumentRedex) (.var 0))
      (.pi true (.eq (.natural 0) (.natural 0))
        ((Raw.eq argumentRedex argumentRedex).rename Nat.succ)) :=
    .convert annotation_before_typed (.pi dependent_result_conversion (.refl _))
  have hb := (HasType.app hf (HasType.refl (numeral_zero (Γ := empty)))).head_beta
  simpa only [subst_shift, subst, single] using hb

/-- Pi formation also transports its codomain into the changed domain context. -/
theorem pi_domain_preserved :
    IsType empty (.pi true (.eq (.natural 0) argumentRedex) .u64) := by
  apply IsType.preservation
    (show IsType empty (.pi true (.eq argumentRedex argumentRedex) .u64)
      from .pi (.eq argument_typed argument_typed) rfl .u64)
  exact .piDomain (.eqLeft redex_step)

/-- A beta-redex inside an array length is allowed by formed type indices. -/
theorem array_length_preserved : IsType empty (.array (.natural 0)) :=
  (IsType.array (argument_typed (Γ := empty))).preservation
    (.array redex_step)

/-- Substitution remains capture avoiding beneath erased and value binders. -/
theorem open_substitution : HasType one nestedBody nestedType := by
  simpa [nestedBody, nestedType, subst, single, liftSub, rename] using
    (HasType.of_raw nested_body_typed).instantiate
      (show HasType one (.var 0) .u64 from .var (by simp [one, Context.extend, rename]))

/-- Literal arithmetic conversion remains bounded, not unbounded machine math. -/
theorem bounded_add_conversion :
    Conv (.eq (.uadd (.natural 2) (.natural 1)) (.natural 3))
      (.eq (.natural 3) (.natural 3)) := .eq (.add 2 1 (by decide)) (.refl _)

/-- The accepted graph output can now retain a beta-converted dependent type.
Acceptance still supplies only structural correctness; input typing is explicit. -/
theorem accepted_substitution_beta_type :
    ∃ output,
      Jihoo.GraphCertificates.decode substitutionCertificate.after
        substitutionCertificate.output = some output ∧
      Jihoo.GraphCertificates.Represents substitutionCertificate.after
        substitutionCertificate.output output ∧
      HasType empty output
        (.eq (.app (.lam false .u64 (.var 0)) (.natural 7))
          (.app (.lam false .u64 (.var 0)) (.natural 7))) := by
  have hbody : HasType (empty.extend .u64) (.refl (.var 0))
      (.eq (.app (.lam false .u64 (.var 0)) (.var 0))
        (.app (.lam false .u64 (.var 0)) (.var 0))) := by
    apply HasType.convert (.refl (.var (by simp [Context.extend, rename])))
    have hc : Conv (.app (.lam false .u64 (.var 0)) (.var 0)) (.var 0) := by
      simpa [subst, single] using Conv.beta false .u64 (.var 0) (.var 0)
    exact .eq (.symm hc) (.symm hc)
  simpa [subst, single, liftSub, rename] using
    Jihoo.GraphCertificates.Beta.validate_substitute_typed
      substitution_certificate_accepted rfl
      (show Jihoo.GraphCertificates.decode substitutionCertificate.before 1 =
        some (.refl (.var 0)) by rfl)
      (show Jihoo.GraphCertificates.decode substitutionCertificate.before 2 =
        some (.natural 7) by rfl)
      hbody (show HasType empty (.natural 7) .u64 from .natural (by decide))

theorem integer_types_separate : ¬ Conv .u64 .i64 := Conv.u64_i64_separate

/-- Erasedness is not silently discarded by beta conversion. -/
theorem pi_erasedness_separate :
    ¬ Conv (.pi false .u64 .u64) (.pi true .u64 .u64) := by
  intro h
  have bad := h.pi_injective.1
  cases bad

end Jihoo.CoreBridge.Raw.Beta.Examples
