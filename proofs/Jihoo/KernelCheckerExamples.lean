import Jihoo.KernelChecker

/-! Regression examples for raw-input checking. No derivation certificate is
supplied. Reduction proofs below check the actual executable definitions. -/
namespace Jihoo.KernelChecker.Examples

open CoreBridge CoreBridge.Raw
open GraphCertificates.Typing (rawDecidableEq)

private def dependent : Raw :=
  .app (.lam false .u64 (.refl (.var 0))) (.natural 7)

-- The argument is free in the application, but must remain free beneath the
-- returned lambda. Replacing Var 1 by Var 0 here would capture it.
private def nested : Raw :=
  .lam false .u64
    (.app (.lam false .u64 (.lam false .u64 (.refl (.var 1)))) (.var 0))

-- Concrete outcomes are reduced and checked by the Lean kernel.
macro "kernel_checker_example" : tactic => `(tactic| cbv)

theorem dependent_application : infer 12 [] dependent = some (.eq (.natural 7) (.natural 7)) := by
  kernel_checker_example
theorem nested_capture : infer 12 [] nested =
    some (.pi false .u64 (.pi false .u64 (.eq (.var 1) (.var 1)))) := by
  kernel_checker_example
example : isType 12 [] (.pi false .u64 (.eq (.var 0) (.var 0))) = true := by
  kernel_checker_example
-- Context annotations are stored before their binder, newest first.
example : infer 4 [.eq (.var 0) (.var 0), .u64] (.var 0) =
    some (.eq (.var 1) (.var 1)) := by
  kernel_checker_example
example : infer 4 [.eq (.var 0) (.var 0), .u64] (.var 1) = some .u64 := by
  kernel_checker_example
example : infer 4 [] (.var 0) = none := by
  kernel_checker_example
example : infer 12 [] (.app (.lam false .u64 (.var 0)) (.integer (-7))) = none := by
  kernel_checker_example
example : infer 12 []
    (.app (.lam true (.eq (.natural 0) (.natural 1)) (.natural 7))
      (.refl (.natural 0))) = none := by
  kernel_checker_example
example : infer 4 [] (.refl (.natural 0)) ≠ some (.eq (.natural 0) (.natural 1)) := by
  decide +kernel
-- An unequal proposition can be formed; formation does not produce evidence.
example : isType 4 [] (.eq (.natural 0) (.natural 1)) = true := by
  kernel_checker_example
example : isType 4 [] (.eq (.integer 0) (.integer 0)) = false := by
  kernel_checker_example
example : infer 4 [] (.refl (.integer 0)) = none := by
  kernel_checker_example
example : infer 4 [] (.uadd (.natural 1) (.natural 2)) = some .u64 := by
  kernel_checker_example
example : infer 4 [] (.natural (2^64)) = none := by
  kernel_checker_example
example : infer 4 [] (.integer (2^63)) = none := by
  kernel_checker_example
example : infer 4 [] (.integer (-(2^63))) = some .i64 := by
  kernel_checker_example
example : infer 4 [] (.integer (-(2^63) - 1)) = none := by
  kernel_checker_example
example : infer 4 [] (.natural (2^64 - 1)) = some .u64 := by
  kernel_checker_example
example : infer 4 [] (.integer (2^63 - 1)) = some .i64 := by
  kernel_checker_example
-- No universe term is silently synthesized by infer.
example : infer 4 [] .u64 = none := by
  kernel_checker_example
example : isType 4 [] .u64 = true := by
  kernel_checker_example
example : isType 4 [] (.array (.natural 1)) = true := by
  kernel_checker_example
example : infer 4 [] (.elements [.integer 7]) = some (.array (.natural 1)) := by
  kernel_checker_example
example : infer 4 [] (.decide (.natural 0) (.natural 1)) = some (.lt (.natural 0) (.natural 1)) := by
  kernel_checker_example
example : infer 4 [] (.lam true .u64 (.var 0)) = none := by
  kernel_checker_example
example : infer 4 [] (.lam false (.eq (.natural 0) (.natural 0)) (.var 0)) = none := by
  kernel_checker_example
-- Verified conversion now accepts the native arithmetic-conversion case.
example : infer 12 []
    (.app (.lam true (.eq (.uadd (.natural 0) (.natural 1)) (.natural 1)) (.natural 7))
      (.refl (.natural 1))) = some .u64 := by
  kernel_checker_example
example : infer 0 [] (.natural 7) = none := rfl
example : isType 0 [] .u64 = false := rfl
example : infer 1 [] dependent = none := by
  kernel_checker_example
example : infer 1 [] (.natural 7) = some .u64 := by
  kernel_checker_example

end Jihoo.KernelChecker.Examples
