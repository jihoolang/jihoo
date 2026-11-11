import Jihoo.SizedMirLinearProgram
import Jihoo.BoundedMirRun

/-! Executable compact-to-MIR branch regressions. These check the modeled
compiler and interpreter, not correspondence with the native compiler. -/
namespace Jihoo.SizedMirBranchExamples
open BoundedMir SizedMir SizedMir.Linear
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- The observation retains the entire heap and event sequence, not just success. -/
structure Observation where
  result : Nat
  heap : Array Object
  events : List Event
  deriving DecidableEq, Repr

def types : Array Ty := #[.i64, .u64, .u64, .ptr]
def inputs : List Operand := [.copy ⟨1,false⟩, .copy ⟨2,false⟩, .copy ⟨3,false⟩]
def prior : SizedBufferHeap.State :=
  SizedBufferHeap.release
    (SizedBufferHeap.allocate (SizedBufferHeap.allocate SizedBufferHeap.empty 1 73) 0 5) 1

def fragment (term : SizedErasure.Term) : Fragment :=
  (compile inputs [.natural,.natural,.pointer] 4 1 0 term).getD
    (pureFragment (.constant (.i64 0)))

def observe (term : SizedErasure.Term) (left right : Nat)
    (s : SizedBufferHeap.State := SizedBufferHeap.empty) : Option Observation := do
  let part ← lowerProgram types inputs term
  let f : Frame := ⟨0,0,#[some (.i64 777),some (.u64 left),some (.u64 right),
    some (.pointer 0 0)],materialize s⟩
  let out ← runFor 100 (program types part)
    (.running (start (programFrame part f) (entry 1 0 term)))
  let .returned value final := out.machine | none
  return ⟨value,final.heap,out.events⟩

def freed (s : SizedBufferHeap.State) (n fill : Nat) : SizedBufferHeap.State :=
  SizedBufferHeap.release (SizedBufferHeap.allocate s n fill) s.heap.nextObject

def scalarFill : SizedErasure.Term :=
  .app (.ifLt (.var 0) (.var 1) (.scalar 11) (.scalar 22))
    (.app (.allocate (.literal 2) (.var 0)) (.free 0 (.var 1)))
def naturalLength : SizedErasure.Term :=
  .app (.ifLt (.var 0) (.var 1) (.natural 0) (.natural 3))
    (.app (.allocate (.var 0) (.literal 9)) (.free 0 (.scalar 42)))
def ownerJoin : SizedErasure.Term :=
  .app (.ifLt (.var 0) (.var 1)
    (.allocate (.literal 1) (.literal 13)) (.allocate (.literal 2) (.literal 27)))
    (.free 0 (.scalar 99))
def nested : SizedErasure.Term :=
  .ifLt (.var 0) (.var 1)
    (.ifLt (.var 0) (.literal 1) (.scalar 10)
      (.app (.allocate (.literal 0) (.literal 0)) (.free 0 (.scalar 20))))
    (.scalar 30)
def unsafeUnselected : SizedErasure.Term :=
  .ifLt (.var 0) (.var 1) (.scalar 71) (.free 2 (.free 2 (.scalar 72)))
def expensiveUnselected : SizedErasure.Term :=
  .ifLt (.var 0) (.var 1) (.scalar 81)
    (.app (.allocate (.literal 4096) (.literal 1)) (.free 0 (.scalar 82)))
def aliasJoin : SizedErasure.Term :=
  .app (.ifLt (.var 0) (.var 1) (.var 2)
    (.allocate (.literal 1) (.literal 31))) (.free 0 (.scalar 91))

theorem scalar_fill_valid : lowerProgram types inputs scalarFill = some (fragment scalarFill) := by decide +kernel
theorem natural_length_valid : lowerProgram types inputs naturalLength = some (fragment naturalLength) := by decide +kernel
theorem owner_join_valid : lowerProgram types inputs ownerJoin = some (fragment ownerJoin) := by decide +kernel
theorem nested_valid : lowerProgram types inputs nested = some (fragment nested) := by decide +kernel
theorem unsafe_unselected_valid : lowerProgram types inputs unsafeUnselected = some (fragment unsafeUnselected) := by decide +kernel
theorem expensive_unselected_valid : lowerProgram types inputs expensiveUnselected = some (fragment expensiveUnselected) := by decide +kernel
theorem alias_join_valid : lowerProgram types inputs aliasJoin = some (fragment aliasJoin) := by decide +kernel

theorem scalar_fill_yes : observe scalarFill 0 1 = some ⟨11,
    materialize (freed SizedBufferHeap.empty 2 11), [.alloc 0 24,.free 0]⟩ := by decide +kernel
theorem scalar_fill_equal : observe scalarFill 1 1 = some ⟨22,
    materialize (freed SizedBufferHeap.empty 2 22), [.alloc 0 24,.free 0]⟩ := by decide +kernel
theorem natural_length_yes : observe naturalLength 0 1 = some ⟨42,
    materialize (freed SizedBufferHeap.empty 0 9), [.alloc 0 8,.free 0]⟩ := by decide +kernel
theorem natural_length_greater : observe naturalLength 2 1 = some ⟨42,
    materialize (freed SizedBufferHeap.empty 3 9), [.alloc 0 32,.free 0]⟩ := by decide +kernel
theorem owner_join_yes : observe ownerJoin 0 1 = some ⟨99,
    materialize (freed SizedBufferHeap.empty 1 13), [.alloc 0 16,.free 0]⟩ := by decide +kernel
theorem owner_join_equal : observe ownerJoin 1 1 = some ⟨99,
    materialize (freed SizedBufferHeap.empty 2 27), [.alloc 0 24,.free 0]⟩ := by decide +kernel
theorem nested_pure : observe nested 0 2 = some ⟨10,#[],[]⟩ := by decide +kernel
theorem nested_effectful : observe nested 1 2 = some ⟨20,
    materialize (freed SizedBufferHeap.empty 0 0), [.alloc 0 8,.free 0]⟩ := by decide +kernel
theorem nested_outer_no : observe nested 2 2 = some ⟨30,#[],[]⟩ := by decide +kernel
theorem unsafe_not_executed : observe unsafeUnselected 0 1 prior =
    some ⟨71,materialize prior,[]⟩ := by decide +kernel
theorem expensive_not_executed : observe expensiveUnselected 0 1 = some ⟨81,#[],[]⟩ := by decide +kernel
theorem alias_prior_live_dead : observe aliasJoin 0 1 prior =
    some ⟨91,materialize (SizedBufferHeap.release prior 0),[.free 0]⟩ := by decide +kernel
theorem allocation_prior_live_dead : observe aliasJoin 1 1 prior =
    some ⟨91,materialize (freed prior 1 31),[.alloc 2 16,.free 2]⟩ := by decide +kernel

theorem mismatched_branch_kind_rejected : lowerProgram types inputs
    (.ifLt (.literal 0) (.literal 1) (.scalar 1) (.natural 2)) = none := by decide +kernel
theorem wrong_comparison_type_rejected : lowerProgram #[.i64,.i64] [.copy ⟨1,false⟩]
    (.ifLt (.var 0) (.literal 1) (.scalar 1) (.scalar 2)) = none := by decide +kernel
theorem missing_kind_rejected : compile inputs [] 4 1 0
    (.ifLt (.literal 0) (.literal 1) (.var 0) (.var 0)) = none := by decide +kernel
theorem invalid_input_rejected : lowerProgram types [.copy ⟨7,false⟩]
    (.ifLt (.literal 0) (.literal 1) (.scalar 1) (.scalar 2)) = none := by decide +kernel
theorem unsupported_input_kind_rejected : lowerProgram #[.i64,.bool] [.copy ⟨1,false⟩]
    (.ifLt (.literal 0) (.literal 1) (.scalar 1) (.scalar 2)) = none := by decide +kernel
theorem unselected_arm_still_checked : lowerProgram types inputs
    (.ifLt (.literal 0) (.literal 1) (.scalar 1) (.scalar scalarBound)) = none := by decide +kernel

/-- Declared scalar input versus represented natural input fails the new premise. -/
theorem inconsistent_environment_not_agree :
    ¬ InputKindsAgree #[.i64,.i64] [.copy ⟨1,false⟩] [.nat 7] := by
  unfold InputKindsAgree
  decide +kernel


def pureBranch : SizedErasure.Term :=
  .ifLt (.var 0) (.var 1) (.scalar 11) (.scalar 22)
def generalFrame (left right : Nat) : Frame :=
  ⟨0,0,#[some (.i64 777),some (.u64 left),some (.u64 right),
    some (.pointer 0 0)],#[]⟩

theorem pure_branch_valid : lowerProgram types inputs pureBranch =
    some (fragment pureBranch) := by decide +kernel

/-- Arbitrary comparison operands, with the new declaration/environment-kind
premise discharged explicitly. The runtime frame itself is supplied by the
fixture rather than assumed globally well typed. -/
theorem general_pure_branch_run (left right : Nat) :
    ∃ final, Steps (program types (fragment pureBranch))
      (.running (start (programFrame (fragment pureBranch) (generalFrame left right)) 1))
      [] (.returned (if left < right then 11 else 22) final) ∧
      HeapRel SizedBufferHeap.empty final.heap := by
  have related : EnvRel [.nat left,.nat right,.owner 0] inputs (generalFrame left right) :=
    .keep rfl (.keep rfl (.keep rfl .nil))
  have kinds : InputKindsAgree types inputs [.nat left,.nat right,.owner 0] := rfl
  have source : SizedErasure.Eval [.nat left,.nat right,.owner 0] pureBranch
      SizedBufferHeap.empty (.scalar (if left < right then 11 else 22)) []
      SizedBufferHeap.empty := by
    by_cases h : left < right
    · simp only [ite_eq_left h]
      exact .yes (.var rfl) (.var rfl) h (.scalar)
    · simp only [ite_eq_right h]
      exact .no (.var rfl) (.var rfl) h (.scalar)
  obtain ⟨final,run,heap,_⟩ := program_run pure_branch_valid rfl related kinds
    HeapRel.empty SizedBufferHeap.empty_valid source (.nil) Trace.Bounds.empty
  exact ⟨final,run,heap⟩

end Jihoo.SizedMirBranchExamples
