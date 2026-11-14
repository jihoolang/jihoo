import Jihoo.KernelConversion

/-! Kernel-reduced examples exercise the executable search, including open
capture avoidance, proof fields, overflow/underflow and local array selection.
None use native_decide or supply a derivation certificate. -/
namespace Jihoo.KernelConversion.Examples

open CoreBridge CoreBridge.Raw
open GraphCertificates.Typing (rawDecidableEq)

macro "conversion_example" : tactic =>
  `(tactic| (simp [equal, normalize, children, contract, subst, single, liftSub, rename,
    GraphCertificates.Typing.substitutionSafe, GraphCertificates.Typing.rawSize,
    GraphCertificates.Typing.rawDepth, GraphCertificates.treeLimit,
    GraphCertificates.depthLimit, wordBound]))

theorem beta_equality : equal 8
    (.eq (.app (.lam false .u64 (.var 0)) (.natural 7)) (.natural 7))
    (.eq (.natural 7) (.natural 7)) = true := by conversion_example

theorem dependent_pi : equal 8
    (.pi false .u64 (.eq (.uadd (.natural 0) (.natural 1)) (.var 0)))
    (.pi false .u64 (.eq (.natural 1) (.var 0))) = true := by conversion_example

theorem nested_capture : normalize 8
    (.app (.lam false .u64 (.lam false .u64 (.var 1))) (.var 0)) =
    .lam false .u64 (.var 1) := by conversion_example

theorem capture_not_equal : equal 8
    (.app (.lam false .u64 (.lam false .u64 (.var 1))) (.var 0))
    (.lam false .u64 (.var 0)) = false := by conversion_example

theorem add_limit : normalize 4 (.uadd (.natural (2^64 - 2)) (.natural 1)) =
    .natural (2^64 - 1) := by decide +kernel

theorem overflow_stays_neutral : normalize 4
    (.uadd (.natural (2^64 - 1)) (.natural 1)) =
    .uadd (.natural (2^64 - 1)) (.natural 1) := by decide +kernel

theorem subtraction : normalize 4
    (.usub (.natural 9) (.natural 4) (.decide (.natural 4) (.natural 10))) =
    .natural 5 := by decide +kernel

theorem underflow_stays_neutral : normalize 4
    (.usub (.natural 4) (.natural 9) (.decide (.natural 9) (.natural 5))) =
    .usub (.natural 4) (.natural 9) (.decide (.natural 9) (.natural 5)) := by decide +kernel

theorem local_read : normalize 8
    (.index (.elements [.integer (-7), .integer 13]) (.uadd (.natural 0) (.natural 1))
      (.decide (.natural 1) (.natural 2))) = .integer 13 := by decide +kernel

theorem out_of_range_stays_neutral : normalize 4
    (.index (.elements [.integer (-7)]) (.natural 1) (.decide (.natural 1) (.natural 1))) =
    .index (.elements [.integer (-7)]) (.natural 1) (.decide (.natural 1) (.natural 1)) := by decide +kernel

theorem proof_fields : equal 8
    (.index (.var 0) (.natural 0)
      (.app (.lam true (.lt (.natural 0) (.natural 1)) (.var 0))
        (.decide (.natural 0) (.natural 1))))
    (.index (.var 0) (.natural 0) (.decide (.natural 0) (.natural 1))) = true := by conversion_example

theorem residual_zero : normalize 0
    (.app (.lam false .u64 (.var 0)) (.natural 7)) =
    .app (.lam false .u64 (.var 0)) (.natural 7) := rfl

theorem no_false_equality : equal 8 (.eq (.natural 0) (.natural 0))
    (.eq (.natural 0) (.natural 1)) = false := by decide +kernel

theorem no_scalar_confusion : equal 8 .u64 .i64 = false := by decide +kernel

end Jihoo.KernelConversion.Examples
