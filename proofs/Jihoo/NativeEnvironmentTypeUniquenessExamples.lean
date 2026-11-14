import Jihoo.NativeEnvironmentRootPreservation
import Jihoo.NativeEnvironmentGhostPolicy

/-! Regression derivations combine actual checking with universal uniqueness
and original-type preservation, rather than comparing inferred values only. -/
namespace Jihoo.NativeKernel.Environment.UniquenessExamples

private abbrev allocated : Term := .alloc (.natural 2) (.integer 0)
private abbrev evidence : Term := .decide (.natural 0) (.natural 2)
private abbrev continuation : Term :=
  .lam false .i64 (.lam false (.buffer (.natural 2)) (.free (.var 0) (.var 1)))
private abbrev loaded : Term := .load allocated (.natural 0) evidence continuation

/-- Load's lowered result remains unique against any converted ghost type. -/
theorem load_result_unique (other : HasType empty [] mode loaded T) :
    Conversion.Conv .i64 T :=
  Checker.infer_unique (fuel := 32) (mode := false) (by cbv) other

theorem borrowed_index_no_u64 :
    ¬ HasType empty [] mode (.index (.borrow allocated) (.natural 0) evidence) .u64 := by
  intro other
  have checked : HasType empty [] true (.index (.borrow allocated) (.natural 0) evidence) .i64 :=
    Checker.infer_sound (fuel := 32) (by cbv)
  exact other.no_scalar_confusion checked

/-- The formerly failing ghost function Load cannot also acquire scalar type. -/
theorem ghost_function_load_no_scalar :
    ¬ HasType empty GhostContinuationExamples.afterContext mode
      GhostContinuationExamples.loadTerm .u64 := by
  intro other
  have converted := Checker.infer_unique GhostContinuationExamples.function_substitution_accepted other
  exact ACU.Conv.full_rigid_disjoint (op := .pi false) (op' := .u64)
    rfl rfl (by intro same; cases same) converted

theorem borrow_round_trip_original_type (other : HasType empty [] mode
    (.deref (.borrow allocated)) T) : HasType empty [] true allocated T :=
  other.ghostDerefBorrow

theorem literal_reassociation_original_type
    (other : HasType empty [] mode (.uadd (.uadd (.natural 1) (.natural 2)) (.natural 3)) T) :
    HasType empty [] true (.uadd (.natural 1) (.uadd (.natural 2) (.natural 3))) T :=
  other.ghostAddAssocRight

/-- Code and ghost results share actual full conversion, including ACU indices. -/
theorem buffer_length_acu_unique (other : HasType empty [] mode allocated (.buffer n)) :
    Conversion.Conv (.uadd (.natural 1) (.natural 1)) n := by
  have typed : HasType empty [] false allocated (.buffer (.natural 2)) :=
    Checker.infer_sound (fuel := 24) (by cbv)
  exact .trans (.legacy (.add 1 1 (by decide))) (typed.buffer_index_unique other)

end Jihoo.NativeKernel.Environment.UniquenessExamples
