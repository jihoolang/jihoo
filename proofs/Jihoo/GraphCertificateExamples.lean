import Jihoo.GraphCertificates

/-! Small kernel-checked nonvacuity checks. Broad graph and parser coverage
comes from freshly exported artifacts in the integration test. -/
namespace Jihoo.GraphCertificates
open CoreBridge

private def shiftExample : Certificate :=
  ⟨#[.var 0], #[.var 0, .var 1], 0, 1, .shift 1⟩

theorem shiftExample_accepted : validate shiftExample = true := by
  have hi : decode shiftExample.before shiftExample.input = some (.var 0) := rfl
  have ho : decode shiftExample.after shiftExample.output = some (.var 1) := rfl
  have hp : appendOnly shiftExample = true := by decide
  simp only [validate, hp, hi, ho, ↓reduceIte]
  simp [expected, shiftExample, Raw.rename, rawEqual, signedBound]

private def mixedBefore : Graph :=
  #[.var 0, .var 1, .var 2, .lam false 1 2, .pi true 0 3]

private def mixedAfter : Graph :=
  mixedBefore ++ #[.var 3, .lam false 2 5, .pi true 1 6]

private def mixedExample : Certificate :=
  ⟨mixedBefore, mixedAfter, 4, 7, .substitute 1⟩

/-- An open replacement is shifted under both binder sorts and in annotations. -/
theorem mixedExample_accepted : validate mixedExample = true := by
  have hi : decode mixedExample.before mixedExample.input =
      some (.pi true (.var 0) (.lam false (.var 1) (.var 2))) := rfl
  have ho : decode mixedExample.after mixedExample.output =
      some (.pi true (.var 1) (.lam false (.var 2) (.var 3))) := rfl
  have hp : appendOnly mixedExample = true := by decide
  have hs : substitutionSafe mixedExample 1 = true := by decide
  have hv : decode mixedExample.before 1 = some (.var 1) := rfl
  have hop : mixedExample.operation = .substitute 1 := rfl
  simp only [validate, hp, hi, ho, ↓reduceIte, expected, hop, hs, hv]
  simp [Raw.subst, Raw.liftSub, Raw.single, Raw.rename, rawEqual]

theorem malformedRoot_rejected :
    validate { shiftExample with output := 9 } = false := by
  have ho : decode shiftExample.after 9 = none := rfl
  have hp : appendOnly { shiftExample with output := 9 } = true := by decide
  simp [validate, hp, ho]

theorem changedPrefix_rejected :
    validate { shiftExample with after := #[.var 1, .var 1] } = false := by
  have hp : appendOnly { shiftExample with after := #[.var 1, .var 1] } = false := by decide
  simp [validate, hp]

end Jihoo.GraphCertificates
