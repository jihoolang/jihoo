import Jihoo.CommonDataBranchFinish

namespace Jihoo.CommonDataBranchFinishChecks
open CommonDataBranchFinish CommonCompositionContract CommonDataTargetContext
open CommonDataReference

variable {a : Boundary} {shell next : Pending} {tail : List Pending} {image : Image}

-- Actual one-tick installed free with stale child references. The destination
-- is already unit: this restricted write set preserves every local exactly.
def stale : ReferenceHeap.Object := ReferenceHeap.node (.object 99 0) (.object 98 0)
def heap : ReferenceHeap.Heap := #[stale, ReferenceHeap.nilObject]
def locals : Array (Option ReferenceCfg.Value) :=
  #[some (.pointer 0 0), some .unit, some (.pointer 1 0), some (.i64 42)]
def program : ReferenceCalls.Program :=
  #[⟨⟨⟨#[.ptr, .unit, .ptr, .i64],
    #[⟨#[], .free (.copy ⟨0,false⟩) ⟨1,false⟩ 1⟩, ⟨#[], .goto 1⟩]⟩, #[]⟩, #[]⟩]
def caller : ReferenceCalls.Continuation := ⟨7, 8, #[some (.i64 91)], ⟨0,false⟩⟩
def start : ReferenceCalls.State := ⟨0, ⟨0,0,locals,heap⟩, [caller]⟩
def stop : ReferenceCalls.State :=
  ⟨0, ⟨1,0,locals,retired heap 0 stale⟩, [caller]⟩

theorem concrete_walk : CommonDataCaseRelocation.walk program 1 1 start =
    some (stop, [.free 0]) := by decide

theorem concrete_execution (a : Boundary) (hs : a.target = start)
    (shell : Pending) (ht : shell.target = 0) (ho : shell.object = stale) :
    FinishExecution program 1 1 a shell stop := by
  constructor
  · simpa [hs, ht] using concrete_walk
  · simp [hs, ht, ho, start, stop]
  · simp [hs, start, stop]
  · simp [hs, start, stop]

-- Live result and suspended caller really survive the concrete execution.
example : stop.frame.locals[2]? = some (some (.pointer 1 0)) := by decide
example : stop.frame.heap[1]? = some ReferenceHeap.nilObject := by decide
example : stop.stack = [caller] := rfl
example : ReferenceHeap.loadRef heap (.object 0 1) = some (.object 99 0) := by decide
example : ReferenceHeap.loadScalar heap (.object 99 0) = none := by decide

-- Arbitrary nested pending parents, buffers/sizes and ambient frames are covered
-- by finish_context: this specialization does not assume child validity.
theorem nested_buffers (h : a.Valid) (head : a.pending = shell :: next :: tail)
    (exec : FinishExecution p limit ticks a shell machine) :
    (finished a shell (next :: tail) machine).Valid ∧
    (finished a shell (next :: tail) machine).buffers = a.buffers ∧
    (finished a shell (next :: tail) machine).sizes = a.sizes ∧
    machine.stack = a.target.stack :=
  ⟨finish_context h head exec.heap exec.locals, rfl, rfl, exec.callers⟩

-- Negative ownership check: aliasing a pending source with an actual result
-- image is inconsistent with the valid boundary, even with lexical aliases.
theorem reject_alias (h : a.Valid) (head : a.pending = shell :: tail)
    (member : image ∈ a.images) (alias : shell.source ∈ image.source.owners) : False :=
  pending_not_result h head member alias

#print axioms finish_context
#print axioms finish_authority
#print axioms finish_result
#print axioms body_finish
#print axioms result_preserved
#print axioms pending_not_result
#print axioms concrete_walk
#print axioms concrete_execution
#print axioms nested_buffers
#print axioms reject_alias
end Jihoo.CommonDataBranchFinishChecks
