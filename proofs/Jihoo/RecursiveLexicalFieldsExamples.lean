import Jihoo.RecursiveLexicalBufferBridge
import Jihoo.RecursiveFieldRuntimeExamples
import Jihoo.SizedCoreExamples

namespace Jihoo.RecursiveLexicalFieldsExamples
open HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime
open RecursiveLexicalFields RecursiveFieldRuntimeExamples
open RecursiveFieldOwnershipExamples (leaf)

def parent : Tree := .node 0 (leaf 1) rightTree

def context : List Entry := [.data 0, .ghost, .data 0]
def environment : List Value := [.data (some 0), .ghost, .data (some 0)]

theorem agrees_fixture : Agrees [.data parent] context environment :=
  .cons ⟨parent, rfl, rfl⟩ (.cons rfl (.cons ⟨parent, rfl, rfl⟩ .nil))

theorem inventory_fixture : Inventory fixture [.data parent] := by
  constructor
  · exact owns_fixture
  · intro c member
    have eq : c = .data parent := by simpa using member
    subst c
    exact fields_fixture

/-- Selecting the second parent alias still reads exactly roots 2 and 1,
with one erased slot before the unchanged outer environment. -/
theorem actual_root_order : enter fixture environment 2 1 =
    some ([.data (some 2), .data (some 1), .ghost,
      .data (some 0), .ghost, .data (some 0)], 0) := by decide

theorem all_parent_aliases_retired : bindContext 1 context =
    [.data 1, .data 0, .ghost, .dead, .ghost, .dead] := rfl

theorem lexical_entry_safe :
    ∃ env', enter fixture environment 2 1 = some (env', 0) ∧
      Agrees [.data (leaf 1), .data rightTree] (bindContext 1 context) env' ∧
      Owns fixture.heap [0, 1, 2, 3] ∧
      Fields fixture.cells [.data (leaf 1), .data rightTree] :=
  enter_total agrees_fixture rfl inventory_fixture

theorem delayed_release_preserves_children :
    Step fixture.heap (.free 0) (release fixture 0).heap ∧
      Valid (release fixture 0).heap ∧
      Inventory (release fixture 0) [.data (leaf 1), .data rightTree] :=
  finish_safe valid_fixture owns_fixture inventory_fixture.2.bind

/-- The parent remains allocated during entry, then is absent after finish. -/
theorem parent_release_timing : fixture.heap.live 0 = true ∧
    (release fixture 0).heap.live 0 = false := by decide

theorem buffer_not_a_case_root : enter fixture [.buffer 0] 0 1 = none := rfl
theorem empty_not_a_node : enter fixture [.data none] 0 1 = none := rfl
theorem missing_cell_rejected :
    enter { fixture with cells := fun _ => none } environment 2 1 = none := rfl
theorem freed_parent_rejected : enter (release fixture 0) environment 2 1 = none := rfl

/-- A tail capability, including all its lexical aliases, shifts past both
child capabilities; it is not silently dropped with the parent. -/
theorem tail_buffer_aliases_preserved :
    Agrees [.data (leaf 1), .data rightTree, .buffer 8]
      (bindContext 2 [.buffer 1, .data 0, .buffer 1])
      (bindValues 2 ⟨some 1, some 2⟩ [.buffer 8, .data (some 0), .buffer 8]) := by
  exact Agrees.bind (x := 0) (left := leaf 1) (right := rightTree)
    (.cons ⟨8, rfl, rfl⟩ (.cons ⟨parent, rfl, rfl⟩ (.cons ⟨8, rfl, rfl⟩ .nil)))

/-- A data tail keeps its own root and shifts independently of lexical depth. -/
theorem mixed_tail_preserved :
    Agrees [.data (leaf 1), .data rightTree, .buffer 8, .data (leaf 9)]
      (bindContext 2 [.data 2, .buffer 1, .data 0])
      (bindValues 2 ⟨some 1, some 2⟩ [.data (some 9), .buffer 8, .data (some 0)]) := by
  exact Agrees.bind (x := 0) (left := leaf 1) (right := rightTree)
    (.cons ⟨leaf 9, rfl, rfl⟩ (.cons ⟨8, rfl, rfl⟩ (.cons ⟨parent, rfl, rfl⟩ .nil)))

theorem stale_alias_cannot_select :
    (bindContext 1 context)[3]? ≠ some (.data 0) ∧
      (bindContext 1 context)[5]? ≠ some (.data 0) := by decide

theorem recursive_root_not_buffer : ¬ Rel [.data rightTree] (.buffer 0) (.data (some 2)) :=
  data_not_buffer

/-- Nonempty Buffer ownership is preserved across the compatibility map. -/
theorem buffer_environment_bridge :
    SizedBufferContext.Agrees [.owner 0, .scalar, .nat 3] [8] [.owner 8, .scalar 7, .nat 3] := by
  apply Agrees.toSized
  exact .cons ⟨8, rfl, rfl⟩ (.cons ⟨7, rfl⟩ (.cons rfl .nil))

/-- The existing allocation/lend/read/free source graph runs from the new
lexical relation for every closing length/index, using its original typing. -/
theorem existing_buffer_program (n i value : Nat) :
    ∃ result events t,
      SizedCoreExecution.Eval SizedCoreExamples.graph (SizedCoreExamples.inputEnv n i value)
        40 SizedBufferHeap.empty result events t ∧
      SizedBufferHeap.Steps SizedBufferHeap.empty events t ∧ SizedBufferHeap.Valid t ∧
      SizedCoreTyping.Post .scalar t result ∧ SizedCoreTyping.Account [] result events := by
  apply buffer_total (cells := fun _ => none) (SizedCoreExamples.body_typed n i)
  · exact .cons ⟨value, rfl⟩ (.cons rfl (.cons rfl .nil))
  · exact ⟨empty_owns, by intro c member; cases member⟩
  · exact SizedCoreExamples.empty_layout
  · exact empty_valid

end Jihoo.RecursiveLexicalFieldsExamples
