import Jihoo.ReferenceCfgEmbedding
import Jihoo.BoundedMirExamples

namespace Jihoo.ReferenceCfg.Checks

/-- The loaded reference points back to the allocation itself. This exercises
reference locals, pointer words and the heap, rather than a scalar-only wrapper. -/
def cycle : Code := ⟨#[.i64, .ptr, .i64, .ptr, .unit], #[
  ⟨#[], .malloc (.constant (.u64 8)) ⟨1, false⟩ 1⟩,
  ⟨#[⟨⟨2, false⟩, .pointerToWord (.copy ⟨1, false⟩)⟩,
      ⟨⟨1, true⟩, .use (.copy ⟨2, false⟩)⟩,
      ⟨⟨2, false⟩, .use (.copy ⟨1, true⟩)⟩,
      ⟨⟨3, false⟩, .wordToPointer (.copy ⟨2, false⟩)⟩],
    .free (.copy ⟨3, false⟩) ⟨4, false⟩ 2⟩,
  ⟨#[⟨⟨0, false⟩, .use (.constant (.i64 7))⟩], .ret⟩]⟩

def cycleFinal : Frame := ⟨2, 1,
  #[some (.i64 7), some (.pointer 0 0), some (.referenceWord (.object 0 0)),
    some (.pointer 0 0), some .unit],
  #[⟨false, #[some (.reference (.object 0 0))]⟩]⟩

theorem reference_cycle_exact : execute 8 cycle (initial cycle) =
    some ⟨7, cycleFinal, [.alloc 0 8, .free 0]⟩ := by decide +kernel

theorem reference_cycle_steps : Steps cycle (.running (initial cycle))
    [.alloc 0 8, .free 0] (.returned 7 cycleFinal) := execute_sound reference_cycle_exact

theorem reference_cycle_needs_return_fuel : execute 7 cycle (initial cycle) = none := by decide +kernel

def nullFrame : Frame := ⟨0, 0, #[some .null, some (.referenceWord .null)], #[]⟩
def ptrCode : Code := ⟨#[.ptr, .i64], #[]⟩

theorem null_created : rvalue nullFrame .null = some .null := rfl

theorem null_roundtrip :
    rvalue nullFrame (.pointerToWord (.copy ⟨0, false⟩)) = some (.referenceWord .null) ∧
    rvalue nullFrame (.wordToPointer (.copy ⟨1, false⟩)) = some .null ∧
    rvalue nullFrame (.nullTest (.copy ⟨0, false⟩)) = some (.boolean true) := by decide +kernel

theorem null_deref_rejected : operand nullFrame (.copy ⟨0, true⟩) = none := by decide +kernel

theorem null_store_rejected : write ptrCode nullFrame ⟨0, true⟩ (.i64 1) = none := by decide +kernel

theorem null_free_rejected : tick ⟨#[.ptr, .unit], #[⟨#[], .free (.copy ⟨0, false⟩) ⟨1, false⟩ 0⟩]⟩
    nullFrame = none := by decide +kernel

def oneCell : Frame := ⟨0, 0, #[some (.pointer 0 0), some (.pointer 0 1)],
  #[⟨true, #[some (.scalar 11)]⟩]⟩

theorem one_past_created : rvalue oneCell (.offset (.copy ⟨0, false⟩) (.constant (.u64 1))) =
    some (.pointer 0 1) := by decide +kernel

theorem one_past_load_rejected : operand oneCell (.copy ⟨1, true⟩) = none := by decide +kernel

theorem one_past_store_rejected : write ⟨#[.ptr, .ptr], #[]⟩ oneCell ⟨1, true⟩ (.i64 4) = none := by decide +kernel

theorem beyond_one_past_rejected : rvalue oneCell (.offset (.copy ⟨0, false⟩) (.constant (.u64 2))) =
    none := by decide +kernel

theorem old_cast_stays_tag : rvalue oneCell (.ptrCast (.copy ⟨0, false⟩)) = some (.address 0) := by decide +kernel

theorem tag_is_not_reference : toRef (.address 0) = none ∧
    rvalue {oneCell with locals := #[some (.address 0)]} (.wordToPointer (.copy ⟨0, false⟩)) = none := by decide +kernel

theorem scalar_zero_cannot_forge :
    rvalue oneCell (.wordToPointer (.constant (.i64 0))) = none := by decide +kernel

theorem dangling_transport :
    rvalue cycleFinal (.pointerToWord (.copy ⟨1, false⟩)) = some (.referenceWord (.object 0 0)) ∧
    rvalue cycleFinal (.wordToPointer (.copy ⟨2, false⟩)) = some (.pointer 0 0) ∧
    operand cycleFinal (.copy ⟨1, true⟩) = none := by decide +kernel

theorem words_are_not_arithmetic : binary .add (.referenceWord (.object 0 0)) (.u64 1) = none := rfl

theorem words_are_not_scalar_returns :
    tick ⟨#[.i64], #[⟨#[], .ret⟩]⟩ {oneCell with locals := #[some (.referenceWord .null)]} = none := by decide +kernel

/-- The retained scalar fixture is transferred by a universal theorem, not
proved again by running the larger interpreter. -/
theorem scalar_fixture_preserved :
    execute BoundedMir.Examples.accepted.fuel (Scalar.code BoundedMir.Examples.single)
      (initial (Scalar.code BoundedMir.Examples.single)) =
      some (Scalar.outcome BoundedMir.Examples.accepted.outcome) :=
  Scalar.accepted_execution BoundedMir.Examples.accepted

theorem scalar_insufficient_fuel :
    execute 21 (Scalar.code BoundedMir.Examples.single)
      (initial (Scalar.code BoundedMir.Examples.single)) = none := by
  rw [Scalar.initial_eq, Scalar.execute_eq, BoundedMir.Examples.one_less_fuel_rejected]
  rfl

end Jihoo.ReferenceCfg.Checks
