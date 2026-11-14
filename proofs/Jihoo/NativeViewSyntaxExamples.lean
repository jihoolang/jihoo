import Jihoo.NativeViewMotiveCongruence

/-! Exact telescope and capture regressions for native borrowed views. The
rule/checker layer is separate; these tests do not assume a live native loan. -/
namespace Jihoo.NativeKernel.Environment.ViewSyntaxExamples

private def nat : Term := .node (.ind 0 0) []
private def natEntry : CheckedFamily :=
  ⟨⟨true,0,0,[nat,.pi false nat nat],0⟩,[⟨[],[]⟩,⟨[⟨false,nat,some []⟩],[]⟩],true⟩
private def env : Environment := ⟨#[],#[natEntry]⟩
private def succSignature : Signature := ⟨[⟨false,nat,some []⟩],[]⟩
private def motive : Term := .lam false (.ref nat) .u64

theorem one_level_field_is_borrowed :
    viewCaseType env 0 1 0 0 succSignature [] .u64 false false =
      some (.pi false (.ref nat) .u64) := by cbv

theorem recursive_result_is_runtime :
    viewCaseType env 0 1 0 0 succSignature [] .u64 true false =
      some (.pi false (.ref nat) (.pi false .u64 .u64)) := by cbv

theorem dependent_reconstructed_field_is_read :
    viewCaseType env 0 1 0 0 succSignature [] motive false true =
      some (.pi false (.ref nat) (.app (.lam false (.ref nat) .u64)
        (.borrow (.node (.con 0 1 1) [.deref (.var 0)])))) := by cbv

theorem recursive_dependent_hypothesis_uses_the_borrow :
    viewCaseType env 0 1 0 0 succSignature [] motive true true =
      some (.pi false (.ref nat) (.pi false (.app motive (.var 0))
        (.app motive (.borrow (.node (.con 0 1 1) [.deref (.var 1)]))))) := by cbv

private def paramNat (n : Term) : Term := .node (.ind 0 1) [n]
private def paramSignature : Signature :=
  ⟨[⟨true,.u64,none⟩,⟨false,paramNat (.var 0),some [.var 0]⟩],[.var 1]⟩

theorem leading_parameters_are_substituted_before_borrowing :
    viewCaseType env 0 1 1 0 paramSignature [.natural 3] .u64 false false =
      some (.pi false (.ref (paramNat (.natural 3))) .u64) := by cbv

private def predicate (owner : Term) : Term :=
  .lam false .u64 (.eq (.free owner (.natural 0)) (.free owner (.natural 0)))
private def dependentSignature : Signature :=
  ⟨[⟨false,.buffer (.natural 2),none⟩,⟨false,.refine (predicate (.var 1)),none⟩],[]⟩

theorem later_refinement_reads_the_preserved_binder :
    viewCaseType env 0 0 0 0 dependentSignature [] .u64 false false =
      some (.pi false (.ref (.buffer (.natural 2)))
        (.pi false (.refine (predicate (.deref (.var 1)))) .u64)) := by cbv

theorem latest_unborrowed_field_is_not_dereferenced : viewRead [true,false] (.var 0) = .var 0 := by cbv
theorem previous_borrowed_field_is_dereferenced : viewRead [true,false] (.var 1) = .deref (.var 1) := by cbv
theorem outer_variables_keep_their_index : viewRead [true,false] (.var 2) = .var 2 := by cbv

theorem reading_does_not_capture_a_lambda_binder :
    viewRead [true] (.lam false .u64 (.uadd (.var 0) (.var 1))) =
      .lam false .u64 (.uadd (.var 0) (.deref (.var 1))) := by cbv

theorem unknown_family_field_rejected :
    viewCaseType env 0 0 0 0 ⟨[⟨false,.node (.ind 99 0) [],none⟩],[]⟩ [] .u64 false false = none := by cbv

theorem unknown_global_field_rejected :
    viewCaseType env 0 0 0 0 ⟨[⟨false,.node (.global 0) [],none⟩],[]⟩ [] .u64 false false = none := by cbv

theorem fixed_array_length_accepted : viewRepresentation 128 1 (.array (.natural 2)) = true := by cbv
theorem motive_dependent_array_length_rejected : viewRepresentation 128 1 (.array (.var 0)) = false := by cbv

theorem returned_function_parameter_cannot_change_array_layout :
    viewRepresentation 128 1 (.pi false .u64 (.array (.var 0))) = false := by cbv

theorem outside_array_length_survives_all_result_binders :
    viewRepresentation 128 1 (.pi false .u64 (.array (.var 2))) = true := by cbv

theorem returned_borrow_rejected : viewRepresentation 128 1 (.ref (.buffer (.natural 2))) = false := by cbv

end Jihoo.NativeKernel.Environment.ViewSyntaxExamples
