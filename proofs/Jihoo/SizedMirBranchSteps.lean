import Jihoo.BoundedMirRun

/-! Actual comparison/switch and result-copy/goto transitions in arbitrary
completed code. Inputs are evaluated before scratch or result locals are written. -/
namespace Jihoo.SizedMir.Branch
open BoundedMir
set_option linter.unusedSimpArgs false

def decisionBlock (scratch : Nat) (left right : Operand) (yes no : Nat) : Block :=
  ⟨#[⟨⟨scratch, false⟩, .bin .lt left right⟩],
    .switch (.copy ⟨scratch, false⟩) [(1, yes)] no⟩

def decisionFrame (f : Frame) (scratch yes no a b : Nat) : Frame :=
  ⟨if a < b then yes else no, 0,
    f.locals.set! scratch (some (.boolean (a < b))), f.heap⟩

@[simp] theorem decisionFrame_block :
    (decisionFrame f scratch yes no a b).block = (if a < b then yes else no) := rfl
@[simp] theorem decisionFrame_index : (decisionFrame f scratch yes no a b).index = 0 := rfl
@[simp] theorem decisionFrame_heap : (decisionFrame f scratch yes no a b).heap = f.heap := rfl
@[simp] theorem decisionFrame_size :
    (decisionFrame f scratch yes no a b).locals.size = f.locals.size := by simp [decisionFrame]

theorem decisionFrame_other (other : k ≠ scratch) :
    (decisionFrame f scratch yes no a b).locals[k]? = f.locals[k]? := by
  by_cases bound : scratch < f.locals.size <;>
    simp [decisionFrame, Array.set!, Array.setIfInBounds, bound, Ne.symm other]

theorem decisionFrame_result (bound : scratch < f.locals.size) :
    operand (decisionFrame f scratch yes no a b) (.copy ⟨scratch, false⟩) =
      some (.boolean (a < b)) := by
  simp [operand, decisionFrame, Array.set!, Array.setIfInBounds, bound]

/-- No disjointness premise: either input may read the old scratch local. -/
theorem decision_run
    (block : c.blocks[f.block]? = some (decisionBlock scratch left right yes no))
    (start : f.index = 0) (ty : c.locals[scratch]? = some .bool)
    (bound : scratch < f.locals.size)
    (yesBound : yes < c.blocks.size) (noBound : no < c.blocks.size)
    (leftValue : operand f left = some (.u64 a))
    (rightValue : operand f right = some (.u64 b)) :
    Steps c (.running f) [] (.running (decisionFrame f scratch yes no a b)) := by
  let first : Frame := { f with index := 1, locals := f.locals.set! scratch (some (.boolean (a < b))) }
  have step1 : Step c (.running f) [] (.running first) := by
    have h := Step.assign (c := c) (f := f) (place := ⟨scratch, false⟩)
      (rhs := .bin .lt left right) (v := .boolean (a < b))
      (next := { f with locals := f.locals.set! scratch (some (.boolean (a < b))) })
      (by simp [fetch, block, start, decisionBlock])
      (by simp [rvalue, leftValue, rightValue, binary])
      (by simp [write, ty, valueType, bound])
    simpa [first, advance, start] using h
  have fetched : fetch c first = some
      (.term (.switch (.copy ⟨scratch, false⟩) [(1, yes)] no)) := by
    simp [fetch, first, block, decisionBlock]
  have value : operand first (.copy ⟨scratch, false⟩) = some (.boolean (a < b)) := by
    simp [operand, first, Array.set!, Array.setIfInBounds, bound]
  have step2 : Step c (.running first) []
      (.running (decisionFrame f scratch yes no a b)) := by
    by_cases lt : a < b
    · have h := Step.switch fetched value
        (show switchValue (.boolean (a < b)) = some 1 by simp [switchValue, lt])
        (show select 1 [(1, yes)] no < c.blocks.size by simpa [select] using yesBound)
      simpa [jump, first, decisionFrame, select, lt] using h
    · have h := Step.switch fetched value
        (show switchValue (.boolean (a < b)) = some 0 by simp [switchValue, lt])
        (show select 0 [(1, yes)] no < c.blocks.size by simpa [select] using noBound)
      simpa [jump, first, decisionFrame, select, lt] using h
  exact .cons step1 (.cons step2 .nil)

def joinBlock (slot : Nat) (result : Operand) (exit : Nat) : Block :=
  ⟨#[⟨⟨slot, false⟩, .use result⟩], .goto exit⟩

def joinFrame (f : Frame) (slot exit : Nat) (v : Value) : Frame :=
  ⟨exit, 0, f.locals.set! slot (some v), f.heap⟩

@[simp] theorem joinFrame_block : (joinFrame f slot exit v).block = exit := rfl
@[simp] theorem joinFrame_index : (joinFrame f slot exit v).index = 0 := rfl
@[simp] theorem joinFrame_heap : (joinFrame f slot exit v).heap = f.heap := rfl
@[simp] theorem joinFrame_size :
    (joinFrame f slot exit v).locals.size = f.locals.size := by simp [joinFrame]

theorem joinFrame_other (other : k ≠ slot) :
    (joinFrame f slot exit v).locals[k]? = f.locals[k]? := by
  by_cases bound : slot < f.locals.size <;>
    simp [joinFrame, Array.set!, Array.setIfInBounds, bound, Ne.symm other]

theorem joinFrame_result (bound : slot < f.locals.size) :
    operand (joinFrame f slot exit v) (.copy ⟨slot, false⟩) = some v := by
  simp [operand, joinFrame, Array.set!, Array.setIfInBounds, bound]

/-- Works for every value kind, including pointers, and allows result-slot aliasing. -/
theorem join_run
    (block : c.blocks[f.block]? = some (joinBlock slot result exit))
    (start : f.index = 0) (ty : c.locals[slot]? = some (valueType v))
    (bound : slot < f.locals.size) (out : exit < c.blocks.size)
    (value : operand f result = some v) :
    Steps c (.running f) [] (.running (joinFrame f slot exit v)) := by
  let first : Frame := { f with index := 1, locals := f.locals.set! slot (some v) }
  have step1 : Step c (.running f) [] (.running first) := by
    have h := Step.assign (c := c) (f := f) (place := ⟨slot, false⟩)
      (rhs := .use result) (v := v)
      (next := { f with locals := f.locals.set! slot (some v) })
      (by simp [fetch, block, start, joinBlock]) value
      (by simp [write, ty, bound])
    simpa [first, advance, start] using h
  have step2 : Step c (.running first) [] (.running (joinFrame f slot exit v)) := by
    have h := Step.goto (f := first) (by simp [fetch, first, block, joinBlock]) out
    simpa [jump, first, joinFrame] using h
  exact .cons step1 (.cons step2 .nil)

/- Executable checks deliberately overwrite an input slot and retain an unrelated
local and a nonempty heap. Both strict-comparison outcomes are covered. -/
private def branchCode : Code :=
  ⟨#[.bool, .u64, .i64],
    #[decisionBlock 0 (.copy ⟨0, false⟩) (.copy ⟨1, false⟩) 1 2,
      ⟨#[], .ret⟩, ⟨#[], .ret⟩]⟩

private def branchStart (a b : Nat) : Frame :=
  ⟨0, 0, #[some (.u64 a), some (.u64 b), some (.i64 71)],
    #[⟨true, #[some 29]⟩]⟩

example : runFor 2 branchCode (.running (branchStart 3 9)) =
    some ⟨.running (decisionFrame (branchStart 3 9) 0 1 2 3 9), []⟩ := by decide
example : runFor 2 branchCode (.running (branchStart 9 3)) =
    some ⟨.running (decisionFrame (branchStart 9 3) 0 1 2 9 3), []⟩ := by decide
example : runFor 2 branchCode (.running (branchStart 3 3)) =
    some ⟨.running (decisionFrame (branchStart 3 3) 0 1 2 3 3), []⟩ := by decide

private def copyCode (v : Value) : Code :=
  ⟨#[valueType v, .i64], #[joinBlock 0 (.copy ⟨0, false⟩) 1, ⟨#[], .ret⟩]⟩
private def copyStart (v : Value) : Frame :=
  ⟨0, 0, #[some v, some (.i64 71)], #[⟨true, #[some 29]⟩]⟩

example : runFor 2 (copyCode (.pointer 0 0)) (.running (copyStart (.pointer 0 0))) =
    some ⟨.running (joinFrame (copyStart (.pointer 0 0)) 0 1 (.pointer 0 0)), []⟩ := by decide
example : runFor 2 (copyCode (.u64 42)) (.running (copyStart (.u64 42))) =
    some ⟨.running (joinFrame (copyStart (.u64 42)) 0 1 (.u64 42)), []⟩ := by decide
example : runFor 2 (copyCode (.i64 42)) (.running (copyStart (.i64 42))) =
    some ⟨.running (joinFrame (copyStart (.i64 42)) 0 1 (.i64 42)), []⟩ := by decide

end Jihoo.SizedMir.Branch
