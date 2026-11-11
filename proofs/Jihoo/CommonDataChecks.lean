import Jihoo.CommonDataExamples

namespace Jihoo.CommonDataChecks
open RecursiveFieldRuntime RecursiveLexicalFields RecursiveBodyProjection CommonData
open CommonDataExamples

/-- The same syntactic child cannot supply two distinct linear slots. -/
theorem duplicate_child_rejected (shape : nodeAt g term = .construct child child) :
    ¬ Typing g ctx 2 [] term .data := by
  intro typed
  cases typed <;> simp_all

theorem empty_cannot_discard_data : ¬ Typing graph ctx 1 [] 31 .data := by
  intro typed
  cases typed <;> simp_all [nodeAt, graph]

theorem empty_cannot_discard_buffer : ¬ Typing graph ctx 0 [1] 31 .data := by
  intro typed
  cases typed <;> simp_all [nodeAt, graph]

theorem variable_cannot_discard_child : ¬ Typing graph ctx 2 [] 26 .data := by
  intro typed
  cases typed <;> simp_all [nodeAt, graph]

theorem constructor_cannot_return_scalar : ¬ Typing graph ctx 2 [] 28 .scalar := by
  intro typed
  cases typed <;> simp_all [nodeAt, graph]

theorem parent_aliases_retired :
    (bindContext 2 [.data 0, .data 0, .data 1, .buffer 2])[4]? = some .dead ∧
    (bindContext 2 [.data 0, .data 0, .data 1, .buffer 2])[5]? = some .dead := by decide

theorem suffix_slots_shift :
    removeHead [.data 0, .data 1, .buffer 2] = [.dead, .data 0, .buffer 1] ∧
    bindContext 2 [.data 0, .data 1, .buffer 2] =
      [.data 1, .data 0, .ghost, .ghost, .dead, .data 2, .buffer 3] := by decide

theorem missing_cell_rejected :
    enter { start.recursive with cells := fun _ => none } env 0 2 = none := by rfl

/-- The old Core embedding has a separate source boundary and retains node IDs. -/
def scalarGraph : CommonData.Graph := #[.core (.integer 99), .embedded 0]

theorem embedded_typed : Typing scalarGraph [] 0 [] 1 .scalar :=
  .core rfl (.literal (v := 99) (by rw [core_at]; rfl) (by decide))

theorem embedded_run : Eval scalarGraph [] 1 start (.scalar 99) [] start :=
  .core rfl (.scalar (v := 99) (by rw [core_at]; rfl))

theorem extension_projects_opaque :
    ScopedLend.Graph.nodeAt (coreGraph graph) 39 = .opaque := by rw [core_at]; rfl

end Jihoo.CommonDataChecks
