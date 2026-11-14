import Jihoo.KernelCheckerSoundness

/-! Executable acceptance and rejection examples for conversion, arithmetic
proofs, dependent arrays and bounds-checked reads. Every computation is checked
by Lean's kernel with `cbv`; no external evaluator or certificate is used. -/
namespace Jihoo.KernelChecker.ExtendedExamples
open CoreBridge CoreBridge.Raw
open GraphCertificates.Typing (rawDecidableEq)

private def values : Raw := .elements [.integer (-7), .integer 9]

private def reader : Raw :=
  .lam false .u64
    (.lam false (.array (.var 0))
      (.lam true (.lt (.natural 0) (.var 1))
        (.index (.var 1) (.natural 0) (.var 0))))

private def dependentRead : Raw :=
  .app (.app (.app reader (.natural 2)) values) (.decide (.natural 0) (.natural 2))

private def dependentArray : Raw :=
  .app
    (.app (.lam false .u64 (.lam false (.array (.var 0)) (.var 0)))
      (.uadd (.natural 1) (.natural 1))) values

/-- Pi codomains retain the array length's dependency before application. -/
theorem dependent_reader_type : infer 16 [] reader =
    some (.pi false .u64 (.pi false (.array (.var 0))
      (.pi true (.lt (.natural 0) (.var 1)) .i64))) := by cbv

/-- Three dependent applications instantiate a length and its bounds proof. -/
theorem dependent_read_accepted : check 16 [] dependentRead .i64 = true := by cbv

/-- Argument checking accepts a computed array length through conversion. -/
theorem dependent_array_accepted :
    check 16 [] dependentArray (.array (.natural 2)) = true := by cbv

/-- The previously rejected arithmetic conversion gap is accepted. -/
theorem arithmetic_conversion_accepted :
    check 8 [] (.refl (.natural 1))
      (.eq (.uadd (.natural 0) (.natural 1)) (.natural 1)) = true := by cbv

/-- Conversion is checked inside application domains as well as at the root. -/
theorem converted_argument_accepted : infer 12 []
    (.app (.lam true (.eq (.uadd (.natural 0) (.natural 1)) (.natural 1)) (.natural 7))
      (.refl (.natural 1))) = some .u64 := by cbv

/-- Beta conversion also works inside an expected proposition's indices. -/
theorem beta_index_accepted : check 12 [] (.refl (.natural 7))
    (.eq (.app (.lam false .u64 (.var 0)) (.natural 7)) (.natural 7)) = true := by cbv

/-- Literal evidence establishes the subtraction's converted non-underflow bound. -/
theorem subtraction_accepted : check 8 []
    (.usub (.natural 5) (.natural 2) (.decide (.natural 2) (.natural 6))) .u64 = true := by cbv

/-- Both the array and the supplied index proof are inferred independently. -/
theorem array_read_accepted : check 8 []
    (.index values (.natural 1) (.decide (.natural 1) (.natural 2))) .i64 = true := by cbv

/-- A proof about another index does not authorize an out-of-bounds read. -/
theorem wrong_index_rejected : infer 8 []
    (.index values (.natural 2) (.decide (.natural 1) (.natural 2))) = none := by cbv

/-- A proof with a different endpoint cannot authorize a read. -/
theorem wrong_length_rejected : infer 8 []
    (.index values (.natural 1) (.decide (.natural 1) (.natural 3))) = none := by cbv

/-- False closed comparisons never become evidence. -/
theorem false_decide_rejected :
    infer 8 [] (.decide (.natural 2) (.natural 2)) = none := by cbv

/-- A mismatched witness cannot hide subtraction underflow. -/
theorem subtraction_underflow_rejected : infer 8 []
    (.usub (.natural 1) (.natural 2) (.decide (.natural 0) (.natural 1))) = none := by cbv

/-- Element inference enforces the signed array payload type. -/
theorem unsigned_element_rejected :
    infer 8 [] (.elements [.natural 0]) = none := by cbv

/-- Array formation checks the length's type rather than only its shape. -/
theorem bad_array_length_rejected : isType 8 [] (.array (.integer 2)) = false := by cbv

/-- Conversion cannot identify distinct scalar type constructors. -/
theorem scalar_mismatch_rejected : check 8 [] (.natural 7) .i64 = false := by cbv

/-- Formation of a false proposition does not produce a proof of it. -/
theorem false_equality_rejected :
    check 8 [] (.refl (.natural 0)) (.eq (.natural 0) (.natural 1)) = false := by cbv

/-- Empty arrays retain their exact zero length. -/
theorem empty_array_accepted : check 4 [] (.elements []) (.array (.natural 0)) = true := by cbv

/-- A length-dependent function rejects an argument of another length. -/
theorem dependent_length_mismatch_rejected : infer 16 []
    (.app (.app (.lam false .u64 (.lam false (.array (.var 0)) (.var 0)))
      (.natural 1)) values) = none := by cbv

/-- The accepted dependent program has the requested declarative type. -/
theorem dependent_read_typed : Beta.HasType (GraphCertificates.Typing.context []) dependentRead .i64 :=
  check_sound dependent_read_accepted

end Jihoo.KernelChecker.ExtendedExamples
