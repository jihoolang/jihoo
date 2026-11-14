import Jihoo.NativeEnvironmentConversionBasis
import Jihoo.NativeEnvironmentDeltaBounded

/-! Actual executable delta/ACU search and unconditional equation soundness.
Forward derivations provide every proof: no environment-validity oracle or
externally selected comparison relation is passed to the implementation. -/
namespace Jihoo.NativeKernel.EnvironmentDelta.Basis

abbrev treeSize := NativeKernel.Conversion.treeSize
abbrev treeDepth := NativeKernel.Conversion.treeDepth
abbrev substitutionSafe := NativeKernel.Conversion.substitutionSafe

def normalize? (env : Environment) (fuel : Nat) (term : Term) : Option Term :=
  EnvironmentDelta.Bounded.normalize env (min fuel 128) 200000 term

def normalize (env : Environment) (fuel : Nat) (term : Term) : Term := (normalize? env fuel term).getD term

def equal (env : Environment) (fuel : Nat) (first second : Term) : Bool :=
  EnvironmentDelta.Bounded.equal env (min fuel 128) 200000 first second

theorem normalize?_forward (accepted : normalize? env fuel term = some result) :
    EnvironmentDelta.Forward env term result := EnvironmentDelta.Bounded.normalize_forward accepted

theorem normalize?_sound (accepted : normalize? env fuel term = some result) : Conv env term result :=
  forward_toConv (normalize?_forward accepted)

theorem normalize_sound (env : Environment) (fuel : Nat) (term : Term) : Conv env term (normalize env fuel term) := by
  unfold normalize
  cases accepted : normalize? env fuel term with
  | none => exact .refl _
  | some result => exact normalize?_sound accepted

theorem equal_common_reduct (accepted : equal env fuel first second = true) :
    ∃ common, EnvironmentDelta.Forward env first common ∧ EnvironmentDelta.Forward env second common :=
  EnvironmentDelta.Bounded.equal_common_reduct accepted

theorem equal_sound (accepted : equal env fuel first second = true) : Conv env first second := by
  obtain ⟨common, firstPath, secondPath⟩ := equal_common_reduct accepted
  exact (forward_toConv firstPath).trans (forward_toConv secondPath).symm

end Jihoo.NativeKernel.EnvironmentDelta.Basis
