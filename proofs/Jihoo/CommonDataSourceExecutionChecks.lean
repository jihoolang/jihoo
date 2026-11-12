import Jihoo.CommonDataSourceExecution
import Jihoo.CommonDataSourceRulesChecks

namespace Jihoo.CommonDataSourceExecutionChecks
open CommonDataSourceExecution CommonDataSourceRulesChecks
open CommonDataSourceRules CommonData RecursiveFieldRuntime RecursiveFieldOwnership
open RecursiveLexicalFields HeapLeases LinearHeapPrograms
open CommonDataExamples (start parent)

/-- Direct source derivation, not obtained by reflecting a target execution. -/
theorem scalar_source : CommonDataSourceExecution.Eval nodes [.data (some 0)] 16 start (.scalar 9)
    [.free 1,.free 2,.free 3,.free 0] scalarFinal :=
  .nodeCase rfl rfl rfl rfl rfl
    (.drop (before := [.free 1]) rfl rfl rfl
      (.node (left := []) (right := []) rfl .empty .empty)
      (.drop (before := [.free 2,.free 3]) rfl rfl rfl
        (.node (left := [.free 3]) (right := []) rfl
          (.node (left := []) (right := []) rfl .empty .empty) .empty)
        (.literal rfl)))

def nestedFinal := finish (finish (finish (finish start 2) 3) 1) 0

/-- Inner child shell 1 is freed after its branch and before outer shell 0. -/
theorem nested_source : CommonDataSourceExecution.Eval nodes [.data (some 0)] 33 start (.scalar 9)
    [.free 2,.free 3,.free 1,.free 0] nestedFinal :=
  .nodeCase rfl rfl rfl rfl rfl
    (.nodeCase rfl rfl rfl rfl rfl
      (.drop (before := []) rfl rfl rfl .empty
        (.drop (before := []) rfl rfl rfl .empty
          (.drop (before := [.free 2,.free 3]) rfl rfl rfl
            (.node (left := [.free 3]) (right := []) rfl
              (.node (left := []) (right := []) rfl .empty .empty) .empty)
            (.literal rfl)))))

/-- The argument returns tree 1 while tree 2 is retained and then reconstructed. -/
theorem split_source : CommonDataSourceExecution.Eval nodes [.data (some 1),.data (some 2)] 45 start
    (.data (some start.buffers.heap.nextObject)) [.alloc start.buffers.heap.nextObject 0]
    (allocate start (some 1) (some 2)) :=
  .dataLet rfl rfl rfl (.dataVar rfl rfl) (.construct rfl rfl rfl rfl rfl)

theorem computed_nil_source : CommonDataSourceExecution.Eval nodes [.data none] 24 start (.data none) [] start :=
  .emptyCase rfl rfl rfl rfl rfl
    (.dataLet rfl rfl rfl (.empty rfl) (.drop rfl rfl rfl .empty (.empty rfl)))

theorem recursive_drop_source : CommonDataSourceExecution.Eval nodes [.data (some 0)] 12 start (.scalar 9)
    [.free 0,.free 1,.free 2,.free 3] CommonDataDropExamples.destroyed :=
  .drop rfl rfl rfl CommonDataDropExamples.destroy_run (.literal rfl)

theorem nested_accounted : AccountedPost .scalar nestedFinal (.scalar 9)
    [4,5,6] parent.owners [.free 2,.free 3,.free 1,.free 0] :=
  every_run_accounted nested_case (trees := [parent]) (owners := []) rfl
    (.cons ⟨parent,rfl,rfl⟩ .nil) CommonData.empty_layout CommonDataExamples.valid_start
    CommonDataDropExamples.input_owned CommonDataDropExamples.input_fields nested_source

/-- No supplied source or target execution: existence follows from typing. -/
theorem source_exists : ∃ v es t, CommonDataSourceExecution.Eval nodes [.data (some 0)] 33 start v es t ∧
    Steps start.buffers.heap es t.buffers.heap ∧ Valid t.buffers.heap ∧
    AccountedPost .scalar t v [4,5,6] parent.owners es :=
  total_accounted nested_case (trees := [parent]) (owners := []) rfl
    (.cons ⟨parent,rfl,rfl⟩ .nil) CommonData.empty_layout CommonDataExamples.valid_start
    CommonDataDropExamples.input_owned CommonDataDropExamples.input_fields

open RecursiveFieldOwnershipExamples (leaf)
open RecursiveFieldRuntimeExamples (rightTree)

/-- Coupling the concrete retained-tree run to the split typing rule. -/
theorem split_accounted : AccountedPost .data (allocate start (some 1) (some 2))
    (.data (some 7)) [0,4,5,6] [1,2,3] [.alloc 7 0] := by
  apply every_run_accounted split_application (trees := [leaf 1,rightTree]) (owners := []) rfl
    (.cons ⟨leaf 1,rfl,rfl⟩ (.cons ⟨rightTree,rfl,rfl⟩ .nil)) empty_layout
    CommonDataExamples.valid_start _ _ split_source
  · apply owns_permute CommonDataExamples.owns_start
    decide
  · intro c member
    simp [caps] at member
    rcases member with rfl | rfl
    · exact RecursiveFieldRuntimeExamples.fields_fixture.2.1
    · exact RecursiveFieldRuntimeExamples.fields_fixture.2.2

#print axioms split_accounted
#print axioms Jihoo.CommonDataSourceExecution.sourceCore_eq
#print axioms Jihoo.CommonDataSourceExecution.Eval.to_common
#print axioms Jihoo.CommonDataSourceExecution.reflect
#print axioms Jihoo.CommonDataSourceExecution.total_accounted
#print axioms Jihoo.CommonDataSourceExecution.Eval.deterministic
#print axioms Jihoo.CommonDataSourceExecution.correspondence
#print axioms Jihoo.CommonDataSourceExecution.every_run_accounted
#print axioms scalar_source
#print axioms nested_source
#print axioms split_source
#print axioms computed_nil_source
#print axioms recursive_drop_source
#print axioms nested_accounted
#print axioms source_exists
end Jihoo.CommonDataSourceExecutionChecks
