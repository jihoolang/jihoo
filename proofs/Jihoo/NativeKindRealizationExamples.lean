import Jihoo.NativeCodeInterpretation
import Jihoo.NativeContextReplayExamples

namespace Jihoo.NativeKernel.Environment.KindRealizationExamples
open CodeKinds

def familyKind : Kind := .index false (.type 0)
def scalarMotive : Term := .lam false .u64 .u64
def oneStep : Term := .lam false .u64
  (.lam true (.lt (.var 0) (.natural 1)) (.lam false .u64 (.var 0)))
def neutralIndex : Term := .loop (.natural 1) scalarMotive (.natural 0) oneStep

def neutralFamily : Term := .ifEq neutralIndex (.natural 0)
  (.lam false .u64 .u64) (.lam false .u64 .i64)

def computedFamily : Term := .app (.lam false .u64 (.lam false .u64 (.array (.var 0)))) (.natural 0)

theorem neutral_index_checked : Checker.check 64 .empty [] false neutralIndex .u64 = true := by cbv

theorem neutral_family_checked : Checker.check 64 .empty [] false neutralFamily familyKind.term = true := by cbv

theorem neutral_family_application_gate :
    Checker.applicationOK 64 .empty false familyKind.term neutralFamily = true := by cbv

/-- The accepted argument remains a conditional, rather than a leading Lam. -/
theorem neutral_family_not_canonical_lambda :
    (Conversion.normalize? .empty 64 neutralFamily).any (fun term => match term with
      | .node .ifEq _ => true | _ => false) = true := by cbv

theorem computed_family_admitted : Admitted .empty familyKind computedFamily :=
  ⟨64, by cbv, by cbv⟩

theorem neutral_family_admitted : Admitted .empty familyKind neutralFamily :=
  ⟨64, neutral_family_checked, neutral_family_application_gate⟩

/-- This covers every typed index, not only the concrete regression inputs. -/
theorem all_typed_indices_nonowning (typed : HasType .empty [] true index .u64) :
    ¬ Owned .empty (.app neutralFamily index) ∧ PiSeparated .empty (.app neutralFamily index) := by
  have realized := (neutral_family_admitted.realizes UnifiedProgram.UnifiedProgramChecked.empty).index typed
  exact ⟨realized.not_owned UnifiedProgram.UnifiedProgramChecked.empty,
    realized.nonFunction UnifiedProgram.UnifiedProgramChecked.empty⟩

theorem typed_unplain_index_nonowning :
    ¬ Owned .empty (.app neutralFamily (.strict (.buffer (.natural 0)) (.natural 0))) :=
  (all_typed_indices_nonowning (Checker.check_sound (by cbv :
    Checker.check 32 .empty [] true (.strict (.buffer (.natural 0)) (.natural 0)) .u64 = true))).1

theorem additive_index_above_word_nonowning :
    ¬ Owned .empty (.app neutralFamily (.uadd (.natural (2^64-1)) (.natural (2^64-1)))) :=
  (all_typed_indices_nonowning (.uadd (.natural (by decide)) (.natural (by decide)))).1

theorem owner_family_gate_rejected :
    Checker.applicationOK 64 .empty false familyKind.term (.lam false .u64 (.buffer (.var 0))) = false := by cbv

theorem function_type_argument_rejected :
    Checker.applicationOK 64 .empty false (Kind.type 0).term (.pi false .u64 .u64) = false := by cbv

end Jihoo.NativeKernel.Environment.KindRealizationExamples
