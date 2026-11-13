import Jihoo.CommonCaseChildConsumption

namespace Jihoo.CommonCaseChildConsumption.Checks
open CommonDataTargetContext CommonDataReference RecursiveLexicalFields

theorem typed_ghost_aliases : CommonDataSourceRules.Typing (graph 7)
    (bindContext 2 [.data 0, .data 0, .scalar]) 2 [] 4 .scalar := typed (by decide)

theorem aliases_retired :
    CommonData.removeHead (CommonData.removeHead
      (bindContext 2 [.data 0, .data 0, .scalar])) =
      [.dead, .dead, .ghost, .ghost, .dead, .dead, .scalar] := rfl

theorem literal_rejected : ¬ CommonDataSourceRules.Typing (graph 7)
    (bindContext 0 []) 2 [] 2 .scalar := by
  intro h
  have impossible := (literal_inventory_zero rfl h).1
  contradiction

/-- Two boxed Nil children really require two target frees, despite having no
source allocations. The pending parent object at index two stays unchanged. -/
def caller : ReferenceCalls.Function :=
  ⟨⟨⟨#[.ptr, .ptr, .unit],
    #[⟨#[], .ret⟩, ⟨#[], .ret⟩, ⟨#[], .goto 2⟩]⟩,
    #[some (.call (TreeDropCall.call 1 (TreeDropCall.arg 1) 2 1)),
      some (.call (TreeDropCall.call 1 (TreeDropCall.arg 0) 2 2))]⟩, #[]⟩
def program : ReferenceCalls.Program := #[caller, TreeDropCall.body 1]
def parent : ReferenceHeap.Object :=
  ⟨true, #[some (.scalar 1), some (.reference (.object 0 0)), some (.reference (.object 1 0))]⟩
def heap : ReferenceHeap.Heap := #[ReferenceHeap.nilObject, ReferenceHeap.nilObject, parent]
def entry : ReferenceCalls.State :=
  ⟨0, ⟨0, 0, #[some (.pointer 1 0), some (.pointer 0 0), none], heap⟩, []⟩
def finalHeap : ReferenceHeap.Heap :=
  #[deadObject ReferenceHeap.nilObject, deadObject ReferenceHeap.nilObject, parent]
def finalState := TreeDropCall.resume (TreeDropCall.resume entry 2 1 finalHeap) 2 2 finalHeap

theorem calls_execute : CommonDataCaseRelocation.walk program 10 2 entry =
    some (finalState, [.free 0, .free 1]) := by decide

theorem shell_unchanged : finalState.frame.heap[2]? = entry.frame.heap[2]? := rfl

#print axioms typed
#print axioms literal_inventory_zero
#print axioms no_node_literal_body
#print axioms total
#print axioms child_released
#print axioms frame_survives
#print axioms installed_children
#print axioms calls_execute
end Jihoo.CommonCaseChildConsumption.Checks
