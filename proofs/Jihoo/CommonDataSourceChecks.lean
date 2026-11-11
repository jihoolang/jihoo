import Jihoo.CommonDataSourceExamples

namespace Jihoo.CommonDataSourceChecks
open CommonDataSource CommonDataSourceExamples CommonData
open RecursiveFieldOwnership RecursiveFieldRuntime RecursiveLexicalFields HeapLeases LinearHeapPrograms

def replace (id : Nat) (node : CommonDataSource.Node) : Source :=
  { source with nodes := source.nodes.set! id node }

theorem family_rejections :
    adapt { source with family := { source.family with data := false } } = none ∧
    adapt { source with family := { source.family with params := 1 } } = none ∧
    adapt { source with family := { source.family with arity := 1 } } = none ∧
    adapt { source with family := { source.family with globals := 1 } } = none ∧
    adapt { source with family := { source.family with constructors := [5,0] } } = none ∧
    adapt { source with family := { source.family with constructors := [0,5,5] } } = none := by decide

theorem telescope_rejections :
    adapt (replace 4 (.core (.pi true 2 3))) = none ∧
    adapt (replace 1 (.core .i64)) = none ∧
    adapt (replace 3 (.core .i64)) = none := by decide

theorem entry_rejections :
    entry { source with root := 95 } = none ∧
    entry { source with typeRoot := 95 } = none ∧
    entry (replace 29 (.core (.lam true 9 28))) = none ∧
    entry (replace 8 (.core (.pi false 6 6))) = none ∧
    entry (replace 12 (.core (.integer (2^63)))) = none ∧
    entry (replace 11 (.core (.var (2^32)))) = none ∧
    entry (replace 28 (.core (.app 14 95))) = none := by decide

theorem foreign_nodes_opaque :
    adaptNode source.nodes (.ind 1 []) = .core .opaque ∧
    adaptNode source.nodes (.ind 0 [0]) = .core .opaque ∧
    adaptNode source.nodes (.drop 1 11 12) = .core .opaque ∧
    adaptNode source.nodes (.con 0 0 [11]) = .core .opaque ∧
    adaptNode source.nodes (.con 0 1 [11]) = .core .opaque ∧
    adaptNode source.nodes (.con 1 1 [11,11]) = .core .opaque := by decide

theorem case_rejections :
    adaptNode (replace 17 (.core (.lam false 15 7))).nodes (CommonDataSource.nodeAt source.nodes 27) = .core .opaque ∧
    adaptNode (replace 18 (.core (.integer 99))).nodes (CommonDataSource.nodeAt source.nodes 27) = .core .opaque ∧
    adaptNode (replace 25 (.core (.lam true 19 24))).nodes (CommonDataSource.nodeAt source.nodes 27) = .core .opaque ∧
    adaptNode (replace 24 (.core (.lam false 7 23))).nodes (CommonDataSource.nodeAt source.nodes 27) = .core .opaque ∧
    adaptNode source.nodes (.caseOf 0 17 [18] 26) = .core .opaque ∧
    adaptNode source.nodes (.caseOf 1 17 [18,25] 26) = .core .opaque := by decide

theorem case_result (typed : Typing graph ctx count sizes 27 kind) : kind = .data :=
  case_empty_result (by rw [adapted_at]; rfl) (by rw [adapted_at]; rfl) typed

local macro "source_shape" : term => `(by first | rfl | (rw [adapted_at]; rfl))

theorem fixture_run : Eval graph [.data (some 0)] 28 CommonDataExamples.start (.scalar 99)
    [.alloc 7 0,.free 0,.free 7,.free 1,.free 2,.free 3] CommonDataApplicationExamples.dropped :=
  .dataLet source_shape source_shape source_shape
    (.nodeCase source_shape source_shape rfl (.construct source_shape source_shape rfl source_shape rfl))
    (.drop source_shape source_shape rfl CommonDataApplicationExamples.computed_destroy (.literal source_shape))

theorem fixture_safe :
    Steps CommonDataExamples.start.buffers.heap [.alloc 7 0,.free 0,.free 7,.free 1,.free 2,.free 3]
      CommonDataApplicationExamples.dropped.buffers.heap ∧
    Valid CommonDataApplicationExamples.dropped.buffers.heap ∧
    Owns CommonDataApplicationExamples.dropped.buffers.heap [4,5,6] := by
  have result := entry_typed.every_run (trees := [CommonDataExamples.parent]) (owners := []) rfl
    (.cons ⟨CommonDataExamples.parent,rfl,rfl⟩ .nil) empty_layout CommonDataExamples.valid_start
    CommonDataDropExamples.input_owned CommonDataDropExamples.input_fields fixture_run
  exact ⟨result.1,result.2.1,result.2.2.2⟩

theorem empty_input_run : Eval graph [.data none] 28 CommonDataExamples.start (.scalar 99) []
    CommonDataExamples.start :=
  .dataLet source_shape source_shape source_shape
    (.emptyCase source_shape source_shape rfl (.empty source_shape))
    (.drop source_shape source_shape rfl .empty (.literal source_shape))

end Jihoo.CommonDataSourceChecks
